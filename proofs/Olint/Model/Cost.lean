import Olint.Axioms
import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# Work semantics

A big-step, fuel-indexed definitional interpreter over the syntax of `Olint.Model.Syntax` that
counts work. Every evaluation of an expression or statement charges one unit, every call one
unit, every built-in the work `Olint.Model.step` assigns it (§2.3), and every spec-internal
operation the step cost `Olint.Axioms` drafts for it.

Fuel bounds the interpreter's recursion depth and loop iterations, so the interpreter is total.
A run ends normally, runs out of fuel, or aborts: on a TypeError, on a construct outside the
model, on an implementation-defined built-in (§2.4), or on a spec-internal operation with no
work definition. A thrown exception aborts the run too: exceptions are outside the model, and
`Olint.Bound` requires every run it bounds to complete.

`Work : Program → Instance → Entry → ℕ` is the model of work the spec's §1 defines for an
entry: the operations the entry performs in one instance, including those of its calls and
callbacks. A node inside an entry is costed over the configurations its entry's runs reach:
`Frame` names every recursive call of the interpreter, `Sub` relates a call to the calls it
makes, and `Reach` closes `Sub` from the entry's root call (`Olint.Bound`).
-/

namespace Olint.Model

/-- Why a run stops before completing. -/
inductive Abort where
  | fuel
  | typeError
  | unmodelled
  | implementationDefined (b : Builtin)
  /-- A spec-internal operation with no work definition (§2.4, `Olint.Axioms`). -/
  | undefinedWork (op : String)

/-- Interpreter state: the heap and the work performed so far. -/
structure St where
  heap : Heap
  work : ℕ

/-- The state after one unit of work. -/
def St.tick (st : St) : St := { st with work := st.work + 1 }

/-- The interpreter monad. -/
abbrev M := StateT St (Except Abort)

/-- Statement completions (ECMA-262 §6.2.4, without `throw`). -/
inductive Completion where
  | normal
  | ret (v : Value)
  | brk
  | cont

/-- A loop continues after a body completing normally or with `continue`. -/
def Completion.continues : Completion → Bool
  | .normal | .cont => true
  | _ => false

/-- Charge `n` units of work. -/
def tick (n : ℕ := 1) : M Unit := modify fun s => { s with work := s.work + n }

/-- Read a heap object. -/
def load (l : Loc) : M Obj := do
  match (← get).heap.get l with
  | some o => pure o
  | none => throw .typeError

/-- Allocate a heap object. -/
def allocate (o : Obj) : M Loc := do
  let s ← get
  let (l, h) := s.heap.alloc o
  set { s with heap := h }
  pure l

/-- Overwrite a heap object. -/
def store (l : Loc) (o : Obj) : M Unit :=
  modify fun s => { s with heap := s.heap.put l o }

/-- Read a variable cell: its value and declared type. -/
def readCell (l : Loc) : M (Value × Ty) := do
  match ← load l with
  | .cell v τ => pure (v, τ)
  | _ => throw .typeError

/-- ECMAScript `ToBoolean` (ECMA-262 §7.1.2) on the modelled values. -/
def truthy : Value → Bool
  | .undef | .null => false
  | .bool b => b
  | .num n => n.truthy
  | .str s => !s.isEmpty
  | .ref _ | .builtin _ => true

/-- A literal's value; a numeric literal is its Number value. -/
def Lit.value : Lit → Value
  | .undefined => .undef
  | .null => .null
  | .bool b => .bool b
  | .num n => .num n.normalize
  | .str s => .str s

/-- ECMAScript `ToNumeric` (§7.1.3) on the primitives whose conversion needs no further
algorithm: `undefined` is `NaN`, `null` is `+0`, a Boolean is `1` or `+0`. `StringToNumber`
and `ToPrimitive` of an object are outside the model. -/
def toNumeric : Value → M Double
  | .num n => pure n
  | .undef => pure .nan
  | .null => pure 0
  | .bool b => pure (if b then 1 else 0)
  | _ => throw .unmodelled

/-- The value of a non-short-circuit binary operator (ECMA-262 §13.15.3
`ApplyStringOrNumericBinaryOperator`, §7.2.13 `IsLessThan`, §7.2.15 `IsStrictlyEqual`). `+` on
two Strings concatenates them; a String beside a non-String needs `ToString` of a Number and
two Strings compared with `<` need the code-unit order, both outside the model. -/
def binop : BinOp → Value → Value → M Value
  | .add, .str a, .str b => do tick (stringConcatWork a b); pure (.str (a ++ b))
  | .add, .str _, _ | .add, _, .str _ => throw .unmodelled
  | .lt, .str _, .str _ | .le, .str _, .str _ | .gt, .str _, .str _ | .ge, .str _, .str _ =>
    throw .unmodelled
  | .strictEq, a, b => do tick (valueEqWork a b); pure (.bool (strictEquals a b))
  | .strictNe, a, b => do tick (valueEqWork a b); pure (.bool !(strictEquals a b))
  | .and, _, _ | .or, _, _ | .nullish, _, _ => throw .unmodelled
  | op, a, b => do
    let x ← toNumeric a
    let y ← toNumeric b
    pure <| match op with
      | .add => .num (x.add y)
      | .sub => .num (x.sub y)
      | .mul => .num (x.mul y)
      | .div => .num (x.div y)
      | .mod => .num (x.rem y)
      | .lt => .bool (x.cmp y == some .lt)
      | .le => .bool (x.cmp y == some .lt || x.cmp y == some .eq)
      | .gt => .bool (x.cmp y == some .gt)
      | .ge => .bool (x.cmp y == some .gt || x.cmp y == some .eq)
      | .band => .num (Double.ofInt32Bits (Nat.land x.toUint32 y.toUint32))
      | .bor => .num (Double.ofInt32Bits (Nat.lor x.toUint32 y.toUint32))
      | .bxor => .num (Double.ofInt32Bits (Nat.xor x.toUint32 y.toUint32))
      | .shl => .num (Double.ofInt32Bits (x.toUint32 <<< (y.toUint32 % 32)))
      | .shr => .num (Double.ofInt (Int.ediv x.toInt32 (2 ^ (y.toUint32 % 32))))
      | .ushr => .num (Double.ofNat (x.toUint32 >>> (y.toUint32 % 32)))
      | _ => .undef

/-- Unary operators on the modelled values (ECMA-262 §13.5). -/
def unop : UnOp → Value → M Value
  | .not, v => pure (.bool !(truthy v))
  | .neg, v => do pure (.num (← toNumeric v).neg)
  | .bitNot, v => do pure (.num (Double.ofInt (-(← toNumeric v).toInt32 - 1)))
  | .typeof, v => pure (.str (match v with
      | .undef => "undefined"
      | .null => "object"
      | .bool _ => "boolean"
      | .num _ => "number"
      | .str _ => "string"
      | .ref _ => "object"
      | .builtin _ => "function"))

/-- Bind a fresh cell for `x` with declared type `τ`. -/
def bindCell (env : Env) (x : Name) (v : Value) (τ : Ty := .any) : M Env := do
  let l ← allocate (.cell v τ)
  pure ((x, l) :: env)

/-- Bind parameters to arguments with their declared types, missing arguments to
`undefined`. -/
def bindParams : Env → List (Name × Ty) → List Value → M Env
  | env, [], _ => pure env
  | env, (x, τ) :: ps, args => do
    let env ← bindCell env x (arg0 args) τ
    bindParams env ps args.tail

/-- Enter a function: bind `this` for a non-arrow function, then the parameters. -/
def enterFunc : Func → Env → Value → List Value → M Env
  | .mk params _ arrow, env, self, args => do
    let env ← if arrow then pure env else bindCell env "this" self
    bindParams env params args

/-- A class method by name. -/
def findMethod (x : Name) : List (Name × Func) → Option Func
  | [] => none
  | (y, f) :: rest => if y = x then some f else findMethod x rest

/-- Set an own property, keeping creation order: overwrite in place, else append. -/
def setProp (props : List (Name × Value)) (x : Name) (v : Value) : List (Name × Value) :=
  if props.any (·.1 == x) then props.map fun p => if p.1 == x then (x, v) else p
  else props ++ [(x, v)]

/-- Resolve a property read on an object: own properties and class methods first, then
built-ins (§2.2). An ordinary object's lookup costs `propertyLookupWork`; a class method read
allocates its closure. -/
def readProp (o : Obj) (x : Name) : M Value := do
  match o with
  | .ordinary props cls =>
    tick propertyLookupWork
    match props.lookup x with
    | some v => pure v
    | none =>
      match cls with
      | some c =>
        match ← load c with
        | .klass (.mk _ methods) env =>
          match findMethod x methods with
          | some f => pure (.ref (← allocate (.closure f env)))
          | none => pure .undef
        | _ => pure .undef
      | none => pure .undef
  | _ =>
    match builtinGetter o x with
    | some (v, w) => do tick w; pure v
    | none =>
      match builtinMethod o x with
      | some b => pure (.builtin b)
      | none => throw .unmodelled

/-- `v.x`: a property of an object, or a String's `length` in UTF-16 code units. Reading a
property of `undefined` or `null` throws a TypeError. -/
def getProp (v : Value) (x : Name) : M Value :=
  match v with
  | .ref l => do readProp (← load l) x
  | .str s => if x = "length" then pure (.num (Double.ofNat (utf16Length s))) else throw .unmodelled
  | .undef | .null => throw .typeError
  | _ => throw .unmodelled

/-- `v[k]`. A Number key is its `ToString` (§7.1.19 `ToPropertyKey`): an Array reads the element
at an array index and `undefined` at any other Number key, which names no own property. -/
def getIndex (v k : Value) : M Value :=
  match v, k with
  | .ref l, .num d => do
    match ← load l with
    | .array elems => pure (match d.toArrayIndex with
      | some i => (elems[i]?).getD .undef
      | none => .undef)
    | o => match d.toPropertyString with
      | some x => readProp o x
      | none => throw .unmodelled
  | .ref l, .str x => do
    match ← load l, arrayIndexKey x with
    | .array elems, some i => pure ((elems[i]?).getD .undef)
    | o, _ => readProp o x
  | .str s, .str x => getProp (.str s) x
  | .undef, _ | .null, _ => throw .typeError
  | _, _ => throw .unmodelled

/-- Write an Array element: overwrite within the length, append at the length; a write past the
length, which leaves holes, is outside the model. -/
def putElem (l : Loc) (elems : List Value) (i : ℕ) (v : Value) : M Unit :=
  if i < elems.length then store l (.array (elems.set i v))
  else if i = elems.length then store l (.array (elems ++ [v]))
  else throw .unmodelled

/-- `v[k] = w`. -/
def putIndex (v k w : Value) : M Unit :=
  match v with
  | .ref l => do
    match ← load l, k with
    | .array elems, .num d => match d.toArrayIndex with
      | some i => putElem l elems i w
      | none => throw .unmodelled
    | .array elems, .str x => match arrayIndexKey x with
      | some i => putElem l elems i w
      | none => throw .unmodelled
    | .ordinary props cls, .str x => do
      tick propertyLookupWork
      store l (.ordinary (setProp props x w) cls)
    | .ordinary props cls, .num d => match d.toPropertyString with
      | some x => do
        tick propertyLookupWork
        store l (.ordinary (setProp props x w) cls)
      | none => throw .unmodelled
    | _, _ => throw .unmodelled
  | .undef | .null => throw .typeError
  | _ => throw .unmodelled

/-- Whether a binary operator evaluates its right operand once its left operand is `v`: the
logical operators short-circuit, every other operator evaluates both. -/
def evaluatesRight : BinOp → Value → Bool
  | .and, v => truthy v
  | .or, v => !truthy v
  | .nullish, .undef | .nullish, .null => true
  | .nullish, _ => false
  | _, _ => true

/-- One element an iteration step yields over an object's live List, by position: `none` when
the List is exhausted, `some none` for a deleted entry the step skips. Map entries yield fresh
`[key, value]` Arrays (ECMA-262 §24.1.5.2.1). -/
def iterStep (o : Obj) (i : ℕ) : M (Option (Option Value)) := do
  match o with
  | .array elems => pure (elems[i]?.map some)
  | .set data => pure (data[i]?)
  | .map data =>
    match data[i]? with
    | none => pure none
    | some none => pure (some none)
    | some (some (k, v)) => pure (some (some (.ref (← allocate (.array [k, v])))))
  | _ => throw .unmodelled

/-- An ordinary object's keys in `OrdinaryOwnPropertyKeys` order (§10.1.11.1): array indices
ascending, then the other String keys in creation order. -/
def ownKeysOrder (props : List (Name × Value)) : List Value :=
  let indices := props.filterMap fun p => (arrayIndexKey p.1).map fun i => (i, p.1)
  let sorted := indices.mergeSort fun a b => decide (a.1 ≤ b.1)
  sorted.map (fun p => Value.str p.2) ++
    (props.filter fun p => (arrayIndexKey p.1).isNone).map fun p => Value.str p.1

/-- The keys `for (x in o)` visits: its own enumerable String keys in property order (§14.7.5.9
`EnumerateObjectProperties`); an Array's indices ascending. -/
def forInKeys (l : Loc) : M (List Value) := do
  match ← load l with
  | .ordinary props _ => pure (ownKeysOrder props)
  | .array elems => pure ((List.range elems.length).map fun i => Value.str (toString i))
  | _ => throw .unmodelled

/-- Run a built-in through `Olint.Model.step`, charging its work. -/
def runStep : Builtin → Bool → Value → List Value → M Value
  | b, isNew, self, args => do
    match step b isNew (← get).heap self args with
    | .ok v h w => do modify fun s => { s with heap := h }; tick w; pure v
    | .typeError => throw .typeError
    | .unmodelled => throw .unmodelled
    | .implementationDefined => throw (.implementationDefined b)

mutual

/-- Evaluate an expression. -/
def evalExpr : ℕ → Env → Expr → M Value
  | 0, _, _ => throw .fuel
  | fuel + 1, env, e => do
    tick
    match e with
    | .lit l => pure l.value
    | .ident x =>
      match env.lookup x with
      | some l => do pure (← readCell l).1
      | none => match builtinGlobal x with
        | some b => pure (.builtin b)
        | none => throw .typeError
    | .«this» =>
      match env.lookup "this" with
      | some l => do pure (← readCell l).1
      | none => pure .undef
    | .unary op a => do unop op (← evalExpr fuel env a)
    | .binary op a b => do
      let va ← evalExpr fuel env a
      match op with
      | .and | .or | .nullish =>
        if evaluatesRight op va then evalExpr fuel env b else pure va
      | _ => do
        let vb ← evalExpr fuel env b
        binop op va vb
    | .cond c t f => do
      if truthy (← evalExpr fuel env c) then evalExpr fuel env t else evalExpr fuel env f
    | .assign x a => do
      let v ← evalExpr fuel env a
      match env.lookup x with
      | some l => do
        let (_, τ) ← readCell l
        store l (.cell v τ)
        pure v
      | none => throw .typeError
    | .assignIndex o k a => do
      let vo ← evalExpr fuel env o
      let vk ← evalExpr fuel env k
      let v ← evalExpr fuel env a
      putIndex vo vk v
      pure v
    | .assignOp op x a =>
      match env.lookup x with
      | some l => do
        let (lv, τ) ← readCell l
        if evaluatesRight op lv then do
          let rv ← evalExpr fuel env a
          let r ← match op with
            | .and | .or | .nullish => pure rv
            | _ => binop op lv rv
          store l (.cell r τ)
          pure r
        else pure lv
      | none => throw .typeError
    | .assignOpIndex op o k a => do
      let vo ← evalExpr fuel env o
      let vk ← evalExpr fuel env k
      let lv ← getIndex vo vk
      if evaluatesRight op lv then do
        let rv ← evalExpr fuel env a
        let r ← match op with
          | .and | .or | .nullish => pure rv
          | _ => binop op lv rv
        putIndex vo vk r
        pure r
      else pure lv
    | .update inc pre x =>
      match env.lookup x with
      | some l => do
        let (v, τ) ← readCell l
        let old ← toNumeric v
        let new := if inc then old.add 1 else old.sub 1
        store l (.cell (.num new) τ)
        pure (.num (if pre then new else old))
      | none => throw .typeError
    | .updateIndex inc pre o k => do
      let vo ← evalExpr fuel env o
      let vk ← evalExpr fuel env k
      let old ← toNumeric (← getIndex vo vk)
      let new := if inc then old.add 1 else old.sub 1
      putIndex vo vk (.num new)
      pure (.num (if pre then new else old))
    | .member o x => do getProp (← evalExpr fuel env o) x
    | .index o k => do
      let vo ← evalExpr fuel env o
      let vk ← evalExpr fuel env k
      getIndex vo vk
    | .call (.member o x) args => do
      let self ← evalExpr fuel env o
      let callee ← getProp self x
      let vs ← evalArgs fuel env args
      callValue fuel callee self vs
    | .call (.index o k) args => do
      let self ← evalExpr fuel env o
      let vk ← evalExpr fuel env k
      let callee ← getIndex self vk
      let vs ← evalArgs fuel env args
      callValue fuel callee self vs
    | .call f args => do
      let callee ← evalExpr fuel env f
      let vs ← evalArgs fuel env args
      callValue fuel callee .undef vs
    | .new f args => do
      let callee ← evalExpr fuel env f
      let vs ← evalArgs fuel env args
      construct fuel callee vs
    | .func f => pure (.ref (← allocate (.closure f env)))
    | .klass c => pure (.ref (← allocate (.klass c env)))
    | .array elems => do
      let vs ← evalArgs fuel env elems
      pure (.ref (← allocate (.array vs)))
    | .object props => do
      let ps ← evalProps fuel env props
      pure (.ref (← allocate (.ordinary (ps.foldl (fun acc p => setProp acc p.1 p.2) []) none)))
    | .regex pattern flags => do
      tick (regexCreateWork pattern flags)
      pure (.ref (← allocate (.regexp pattern flags)))

/-- Evaluate arguments left to right. -/
def evalArgs : ℕ → Env → List Expr → M (List Value)
  | 0, _, _ => throw .fuel
  | _ + 1, _, [] => pure []
  | fuel + 1, env, e :: es => do
    let v ← evalExpr fuel env e
    let vs ← evalArgs fuel env es
    pure (v :: vs)

/-- Evaluate object literal properties left to right. -/
def evalProps : ℕ → Env → List (Name × Expr) → M (List (Name × Value))
  | 0, _, _ => throw .fuel
  | _ + 1, _, [] => pure []
  | fuel + 1, env, (x, e) :: ps => do
    let v ← evalExpr fuel env e
    let vs ← evalProps fuel env ps
    pure ((x, v) :: vs)

/-- Call a function value with a receiver. -/
def callValue : ℕ → Value → Value → List Value → M Value
  | 0, _, _, _ => throw .fuel
  | fuel + 1, callee, self, args => do
    tick
    match callee with
    | .builtin b => runStep b false self args
    | .ref l =>
      match ← load l with
      | .closure f env => callFunc fuel f env self args
      | _ => throw .typeError
    | _ => throw .typeError

/-- `new` on a value. -/
def construct : ℕ → Value → List Value → M Value
  | 0, _, _ => throw .fuel
  | fuel + 1, callee, args => do
    tick
    match callee with
    | .builtin b => runStep b true .undef args
    | .ref l =>
      match ← load l with
      | .klass (.mk ctor _) env => do
        let self : Value := .ref (← allocate (.ordinary [] (some l)))
        match ctor with
        | some f => discard <| callFunc fuel f env self args
        | none => pure ()
        pure self
      | _ => throw .typeError
    | _ => throw .typeError

/-- Run a function body. -/
def callFunc : ℕ → Func → Env → Value → List Value → M Value
  | 0, _, _, _, _ => throw .fuel
  | fuel + 1, f, env, self, args => do
    let env ← enterFunc f env self args
    match f with
    | .mk _ body _ =>
      match (← execStmts fuel env body).2 with
      | .ret v => pure v
      | _ => pure .undef

/-- Execute a statement, returning the environment it extends. -/
def execStmt : ℕ → Env → Stmt → M (Env × Completion)
  | 0, _, _ => throw .fuel
  | fuel + 1, env, s => do
    tick
    match s with
    | .expr e => do let _ ← evalExpr fuel env e; pure (env, .normal)
    | .decl _ x τ init => do
      let v ← match init with
        | some e => evalExpr fuel env e
        | none => pure .undef
      pure (← bindCell env x v τ, .normal)
    | .block body => do pure (env, (← execStmts fuel env body).2)
    | .ite c t f => do
      if truthy (← evalExpr fuel env c) then pure (env, (← execStmt fuel env t).2)
      else match f with
        | some f => pure (env, (← execStmt fuel env f).2)
        | none => pure (env, .normal)
    | .forLoop init test update body => do
      let env' ← match init with
        | some i => do pure (← execStmt fuel env i).1
        | none => pure env
      pure (env, (← forLoop fuel env' test update body))
    | .forOf x e body => do
      match ← evalExpr fuel env e with
      | .ref l => pure (env, (← forOfLoop fuel env x l 0 body))
      | _ => throw .typeError
    | .forIn x e body => do
      match ← evalExpr fuel env e with
      | .ref l =>
        match ownPropertyKeysWork with
        | none => throw (.undefinedWork "OrdinaryOwnPropertyKeys")
        | some w => do
          tick w
          let keys ← forInKeys l
          pure (env, (← forEachValue fuel env x keys body))
      | .undef | .null => pure (env, .normal)
      | _ => throw .unmodelled
    | .«while» c body => do pure (env, (← whileLoop fuel env c body))
    | .doWhile body c => do
      let c' := (← execStmt fuel env body).2
      if c'.continues then pure (env, (← whileLoop fuel env c body))
      else match c' with
        | .ret v => pure (env, .ret v)
        | _ => pure (env, .normal)
    | .ret e => do
      match e with
      | some e => pure (env, .ret (← evalExpr fuel env e))
      | none => pure (env, .ret .undef)
    | .brk => pure (env, .brk)
    | .cont => pure (env, .cont)
    | .funDecl x f => do
      let l ← allocate (.cell .undef .any)
      let env' := (x, l) :: env
      store l (.cell (.ref (← allocate (.closure f env'))) .any)
      pure (env', .normal)
    | .classDecl x c => do
      let l ← allocate (.cell .undef .any)
      let env' := (x, l) :: env
      store l (.cell (.ref (← allocate (.klass c env'))) .any)
      pure (env', .normal)

/-- Execute a statement list in order, stopping at an abrupt completion. -/
def execStmts : ℕ → Env → List Stmt → M (Env × Completion)
  | 0, _, _ => throw .fuel
  | _ + 1, env, [] => pure (env, .normal)
  | fuel + 1, env, s :: ss => do
    let (env', c) ← execStmt fuel env s
    match c with
    | .normal => execStmts fuel env' ss
    | c => pure (env', c)

/-- `while (c) body`, one fuel unit per iteration. -/
def whileLoop : ℕ → Env → Expr → Stmt → M Completion
  | 0, _, _, _ => throw .fuel
  | fuel + 1, env, c, body => do
    if truthy (← evalExpr fuel env c) then
      let c' := (← execStmt fuel env body).2
      if c'.continues then whileLoop fuel env c body
      else match c' with
        | .ret v => pure (.ret v)
        | _ => pure .normal
    else pure .normal

/-- `for (…; test; update) body`, one fuel unit per iteration. -/
def forLoop : ℕ → Env → Option Expr → Option Expr → Stmt → M Completion
  | 0, _, _, _, _ => throw .fuel
  | fuel + 1, env, test, update, body => do
    let go ← match test with
      | some t => do pure (truthy (← evalExpr fuel env t))
      | none => pure true
    if go then
      let c' := (← execStmt fuel env body).2
      if c'.continues then do
        match update with
        | some u => discard <| evalExpr fuel env u
        | none => pure ()
        forLoop fuel env test update body
      else match c' with
        | .ret v => pure (.ret v)
        | _ => pure .normal
    else pure .normal

/-- `for (const x of o) body` over the live List of an Array, Map or Set, reading it afresh at
each step as ECMAScript iterators do; a deleted entry costs its skip. -/
def forOfLoop : ℕ → Env → Name → Loc → ℕ → Stmt → M Completion
  | 0, _, _, _, _, _ => throw .fuel
  | fuel + 1, env, x, l, i, body => do
    tick
    match ← iterStep (← load l) i with
    | none => pure .normal
    | some none => forOfLoop fuel env x l (i + 1) body
    | some (some v) => do
      let env' ← bindCell env x v
      let c' := (← execStmt fuel env' body).2
      if c'.continues then forOfLoop fuel env x l (i + 1) body
      else match c' with
        | .ret v => pure (.ret v)
        | _ => pure .normal

/-- Run `body` once per value, binding `x` afresh each time. -/
def forEachValue : ℕ → Env → Name → List Value → Stmt → M Completion
  | 0, _, _, _, _ => throw .fuel
  | _ + 1, _, _, [], _ => pure .normal
  | fuel + 1, env, x, v :: vs, body => do
    let env' ← bindCell env x v
    let c' := (← execStmt fuel env' body).2
    if c'.continues then forEachValue fuel env x vs body
    else match c' with
      | .ret v => pure (.ret v)
      | _ => pure .normal

end

/-! ## Frames and configurations

A frame is one call of the interpreter's mutual functions, a configuration a frame with the
state it starts from. `Sub c c'` holds when running `c` makes the call `c'`: for a call made
after earlier calls of the same frame, from a state those calls reach with some fuel. -/

/-- A call of the interpreter. -/
inductive Frame where
  | expr (env : Env) (e : Expr)
  | stmt (env : Env) (s : Stmt)
  | stmts (env : Env) (ss : List Stmt)
  | args (env : Env) (es : List Expr)
  | props (env : Env) (ps : List (Name × Expr))
  | callValue (callee self : Value) (args : List Value)
  | construct (callee : Value) (args : List Value)
  | callFunc (f : Func) (env : Env) (self : Value) (args : List Value)
  | whileLoop (env : Env) (c : Expr) (body : Stmt)
  | forLoop (env : Env) (test update : Option Expr) (body : Stmt)
  | forOfLoop (env : Env) (x : Name) (l : Loc) (i : ℕ) (body : Stmt)
  | forEachValue (env : Env) (x : Name) (vs : List Value) (body : Stmt)

/-- What a call returns. -/
inductive Outcome where
  | val (v : Value)
  | vals (vs : List Value)
  | props (ps : List (Name × Value))
  | stmt (env : Env) (c : Completion)
  | compl (c : Completion)

/-- Run a frame with the given fuel. -/
def Frame.run (fuel : ℕ) : Frame → M Outcome
  | .expr env e => Outcome.val <$> evalExpr fuel env e
  | .stmt env s => (fun r => Outcome.stmt r.1 r.2) <$> execStmt fuel env s
  | .stmts env ss => (fun r => Outcome.stmt r.1 r.2) <$> execStmts fuel env ss
  | .args env es => Outcome.vals <$> evalArgs fuel env es
  | .props env ps => Outcome.props <$> evalProps fuel env ps
  | .callValue callee self vs => Outcome.val <$> Olint.Model.callValue fuel callee self vs
  | .construct callee vs => Outcome.val <$> Olint.Model.construct fuel callee vs
  | .callFunc f env self vs => Outcome.val <$> Olint.Model.callFunc fuel f env self vs
  | .whileLoop env c body => Outcome.compl <$> Olint.Model.whileLoop fuel env c body
  | .forLoop env test update body => Outcome.compl <$> Olint.Model.forLoop fuel env test update body
  | .forOfLoop env x l i body => Outcome.compl <$> Olint.Model.forOfLoop fuel env x l i body
  | .forEachValue env x vs body => Outcome.compl <$> Olint.Model.forEachValue fuel env x vs body

/-- A configuration: a frame and the state it runs from. -/
structure Cfg where
  frame : Frame
  st : St

/-- The configuration completes with fuel `fuel`, returning `o` in state `st'`. -/
def Cfg.Runs (c : Cfg) (fuel : ℕ) (o : Outcome) (st' : St) : Prop :=
  (c.frame.run fuel).run c.st = .ok (o, st')

/-- A computation of `M` returns `a` in state `st'` from state `st`. -/
def Out {α : Type} (x : M α) (st : St) (a : α) (st' : St) : Prop := x.run st = .ok (a, st')

/-- Frame `fr` completes from `st` with some fuel, returning `o` in state `st'`. -/
def Ev (fr : Frame) (st : St) (o : Outcome) (st' : St) : Prop := ∃ fuel, Cfg.Runs ⟨fr, st⟩ fuel o st'

/-- `Sub c c'`: running configuration `c` calls configuration `c'`. One constructor per
recursive call of the interpreter; a call made after other calls of the same frame starts from
a state those calls reach. -/
inductive Sub : Cfg → Cfg → Prop where
  | unary {env op a st} : Sub ⟨.expr env (.unary op a), st⟩ ⟨.expr env a, st.tick⟩
  | binaryL {env op a b st} : Sub ⟨.expr env (.binary op a b), st⟩ ⟨.expr env a, st.tick⟩
  | binaryR {env op a b st v st1} : Ev (.expr env a) st.tick (.val v) st1 →
      evaluatesRight op v = true → Sub ⟨.expr env (.binary op a b), st⟩ ⟨.expr env b, st1⟩
  | condTest {env c t f st} : Sub ⟨.expr env (.cond c t f), st⟩ ⟨.expr env c, st.tick⟩
  | condThen {env c t f st v st1} : Ev (.expr env c) st.tick (.val v) st1 → truthy v = true →
      Sub ⟨.expr env (.cond c t f), st⟩ ⟨.expr env t, st1⟩
  | condElse {env c t f st v st1} : Ev (.expr env c) st.tick (.val v) st1 → truthy v = false →
      Sub ⟨.expr env (.cond c t f), st⟩ ⟨.expr env f, st1⟩
  | assign {env x a st} : Sub ⟨.expr env (.assign x a), st⟩ ⟨.expr env a, st.tick⟩
  | assignIndexO {env o k a st} : Sub ⟨.expr env (.assignIndex o k a), st⟩ ⟨.expr env o, st.tick⟩
  | assignIndexK {env o k a st vo st1} : Ev (.expr env o) st.tick (.val vo) st1 →
      Sub ⟨.expr env (.assignIndex o k a), st⟩ ⟨.expr env k, st1⟩
  | assignIndexA {env o k a st vo st1 vk st2} : Ev (.expr env o) st.tick (.val vo) st1 →
      Ev (.expr env k) st1 (.val vk) st2 → Sub ⟨.expr env (.assignIndex o k a), st⟩ ⟨.expr env a, st2⟩
  | assignOp {env op x a st l lv τ} : env.lookup x = some l → Out (readCell l) st.tick (lv, τ) st.tick →
      evaluatesRight op lv = true → Sub ⟨.expr env (.assignOp op x a), st⟩ ⟨.expr env a, st.tick⟩
  | assignOpIndexO {env op o k a st} :
      Sub ⟨.expr env (.assignOpIndex op o k a), st⟩ ⟨.expr env o, st.tick⟩
  | assignOpIndexK {env op o k a st vo st1} : Ev (.expr env o) st.tick (.val vo) st1 →
      Sub ⟨.expr env (.assignOpIndex op o k a), st⟩ ⟨.expr env k, st1⟩
  | assignOpIndexA {env op o k a st vo st1 vk st2 lv st3} : Ev (.expr env o) st.tick (.val vo) st1 →
      Ev (.expr env k) st1 (.val vk) st2 → Out (getIndex vo vk) st2 lv st3 →
      evaluatesRight op lv = true → Sub ⟨.expr env (.assignOpIndex op o k a), st⟩ ⟨.expr env a, st3⟩
  | updateIndexO {env inc pre o k st} :
      Sub ⟨.expr env (.updateIndex inc pre o k), st⟩ ⟨.expr env o, st.tick⟩
  | updateIndexK {env inc pre o k st vo st1} : Ev (.expr env o) st.tick (.val vo) st1 →
      Sub ⟨.expr env (.updateIndex inc pre o k), st⟩ ⟨.expr env k, st1⟩
  | memberO {env o x st} : Sub ⟨.expr env (.member o x), st⟩ ⟨.expr env o, st.tick⟩
  | indexO {env o k st} : Sub ⟨.expr env (.index o k), st⟩ ⟨.expr env o, st.tick⟩
  | indexK {env o k st vo st1} : Ev (.expr env o) st.tick (.val vo) st1 →
      Sub ⟨.expr env (.index o k), st⟩ ⟨.expr env k, st1⟩
  | callMemberO {env o x args st} :
      Sub ⟨.expr env (.call (.member o x) args), st⟩ ⟨.expr env o, st.tick⟩
  | callMemberArgs {env o x args st self st1 callee st2} : Ev (.expr env o) st.tick (.val self) st1 →
      Out (getProp self x) st1 callee st2 →
      Sub ⟨.expr env (.call (.member o x) args), st⟩ ⟨.args env args, st2⟩
  | callMemberCall {env o x args st self st1 callee st2 vs st3} :
      Ev (.expr env o) st.tick (.val self) st1 → Out (getProp self x) st1 callee st2 →
      Ev (.args env args) st2 (.vals vs) st3 →
      Sub ⟨.expr env (.call (.member o x) args), st⟩ ⟨.callValue callee self vs, st3⟩
  | callIndexO {env o k args st} :
      Sub ⟨.expr env (.call (.index o k) args), st⟩ ⟨.expr env o, st.tick⟩
  | callIndexK {env o k args st self st1} : Ev (.expr env o) st.tick (.val self) st1 →
      Sub ⟨.expr env (.call (.index o k) args), st⟩ ⟨.expr env k, st1⟩
  | callIndexArgs {env o k args st self st1 vk st2 callee st3} :
      Ev (.expr env o) st.tick (.val self) st1 → Ev (.expr env k) st1 (.val vk) st2 →
      Out (getIndex self vk) st2 callee st3 →
      Sub ⟨.expr env (.call (.index o k) args), st⟩ ⟨.args env args, st3⟩
  | callIndexCall {env o k args st self st1 vk st2 callee st3 vs st4} :
      Ev (.expr env o) st.tick (.val self) st1 → Ev (.expr env k) st1 (.val vk) st2 →
      Out (getIndex self vk) st2 callee st3 → Ev (.args env args) st3 (.vals vs) st4 →
      Sub ⟨.expr env (.call (.index o k) args), st⟩ ⟨.callValue callee self vs, st4⟩
  | callF {env f args st} : (∀ o x, f ≠ .member o x) → (∀ o k, f ≠ .index o k) →
      Sub ⟨.expr env (.call f args), st⟩ ⟨.expr env f, st.tick⟩
  | callArgs {env f args st callee st1} : (∀ o x, f ≠ .member o x) → (∀ o k, f ≠ .index o k) →
      Ev (.expr env f) st.tick (.val callee) st1 →
      Sub ⟨.expr env (.call f args), st⟩ ⟨.args env args, st1⟩
  | callCall {env f args st callee st1 vs st2} : (∀ o x, f ≠ .member o x) →
      (∀ o k, f ≠ .index o k) → Ev (.expr env f) st.tick (.val callee) st1 →
      Ev (.args env args) st1 (.vals vs) st2 →
      Sub ⟨.expr env (.call f args), st⟩ ⟨.callValue callee .undef vs, st2⟩
  | newF {env f args st} : Sub ⟨.expr env (.new f args), st⟩ ⟨.expr env f, st.tick⟩
  | newArgs {env f args st callee st1} : Ev (.expr env f) st.tick (.val callee) st1 →
      Sub ⟨.expr env (.new f args), st⟩ ⟨.args env args, st1⟩
  | newConstruct {env f args st callee st1 vs st2} : Ev (.expr env f) st.tick (.val callee) st1 →
      Ev (.args env args) st1 (.vals vs) st2 →
      Sub ⟨.expr env (.new f args), st⟩ ⟨.construct callee vs, st2⟩
  | arrayElems {env elems st} : Sub ⟨.expr env (.array elems), st⟩ ⟨.args env elems, st.tick⟩
  | objectProps {env ps st} : Sub ⟨.expr env (.object ps), st⟩ ⟨.props env ps, st.tick⟩
  | argsHead {env e es st} : Sub ⟨.args env (e :: es), st⟩ ⟨.expr env e, st⟩
  | argsTail {env e es st v st1} : Ev (.expr env e) st (.val v) st1 →
      Sub ⟨.args env (e :: es), st⟩ ⟨.args env es, st1⟩
  | propsHead {env x e ps st} : Sub ⟨.props env ((x, e) :: ps), st⟩ ⟨.expr env e, st⟩
  | propsTail {env x e ps st v st1} : Ev (.expr env e) st (.val v) st1 →
      Sub ⟨.props env ((x, e) :: ps), st⟩ ⟨.props env ps, st1⟩
  | callValue {l self args st f env} : st.heap.get l = some (.closure f env) →
      Sub ⟨.callValue (.ref l) self args, st⟩ ⟨.callFunc f env self args, st.tick⟩
  | construct {l args st f ms env l' st1} : st.heap.get l = some (.klass (.mk (some f) ms) env) →
      Out (allocate (.ordinary [] (some l))) st.tick l' st1 →
      Sub ⟨.construct (.ref l) args, st⟩ ⟨.callFunc f env (.ref l') args, st1⟩
  | callFunc {params body arrow env self args st env' st1} :
      Out (enterFunc (.mk params body arrow) env self args) st env' st1 →
      Sub ⟨.callFunc (.mk params body arrow) env self args, st⟩ ⟨.stmts env' body, st1⟩
  | exprStmt {env e st} : Sub ⟨.stmt env (.expr e), st⟩ ⟨.expr env e, st.tick⟩
  | declInit {env k x τ e st} : Sub ⟨.stmt env (.decl k x τ (some e)), st⟩ ⟨.expr env e, st.tick⟩
  | block {env ss st} : Sub ⟨.stmt env (.block ss), st⟩ ⟨.stmts env ss, st.tick⟩
  | iteTest {env c t f st} : Sub ⟨.stmt env (.ite c t f), st⟩ ⟨.expr env c, st.tick⟩
  | iteThen {env c t f st v st1} : Ev (.expr env c) st.tick (.val v) st1 → truthy v = true →
      Sub ⟨.stmt env (.ite c t f), st⟩ ⟨.stmt env t, st1⟩
  | iteElse {env c t f st v st1} : Ev (.expr env c) st.tick (.val v) st1 → truthy v = false →
      Sub ⟨.stmt env (.ite c t (some f)), st⟩ ⟨.stmt env f, st1⟩
  | forInit {env i test update body st} :
      Sub ⟨.stmt env (.forLoop (some i) test update body), st⟩ ⟨.stmt env i, st.tick⟩
  | forStart {env i test update body st env' c st1} : Ev (.stmt env i) st.tick (.stmt env' c) st1 →
      Sub ⟨.stmt env (.forLoop (some i) test update body), st⟩ ⟨.forLoop env' test update body, st1⟩
  | forStartBare {env test update body st} :
      Sub ⟨.stmt env (.forLoop none test update body), st⟩ ⟨.forLoop env test update body, st.tick⟩
  | forOfExpr {env x e body st} : Sub ⟨.stmt env (.forOf x e body), st⟩ ⟨.expr env e, st.tick⟩
  | forOfStart {env x e body st l st1} : Ev (.expr env e) st.tick (.val (.ref l)) st1 →
      Sub ⟨.stmt env (.forOf x e body), st⟩ ⟨.forOfLoop env x l 0 body, st1⟩
  | forInExpr {env x e body st} : Sub ⟨.stmt env (.forIn x e body), st⟩ ⟨.expr env e, st.tick⟩
  | forInStart {env x e body st l st1 w keys st2} : Ev (.expr env e) st.tick (.val (.ref l)) st1 →
      ownPropertyKeysWork = some w → Out (forInKeys l) { st1 with work := st1.work + w } keys st2 →
      Sub ⟨.stmt env (.forIn x e body), st⟩ ⟨.forEachValue env x keys body, st2⟩
  | whileStart {env c body st} : Sub ⟨.stmt env (.«while» c body), st⟩ ⟨.whileLoop env c body, st.tick⟩
  | doBody {env body c st} : Sub ⟨.stmt env (.doWhile body c), st⟩ ⟨.stmt env body, st.tick⟩
  | doLoop {env body c st env' c' st1} : Ev (.stmt env body) st.tick (.stmt env' c') st1 →
      c'.continues = true → Sub ⟨.stmt env (.doWhile body c), st⟩ ⟨.whileLoop env c body, st1⟩
  | retExpr {env e st} : Sub ⟨.stmt env (.ret (some e)), st⟩ ⟨.expr env e, st.tick⟩
  | stmtsHead {env s ss st} : Sub ⟨.stmts env (s :: ss), st⟩ ⟨.stmt env s, st⟩
  | stmtsTail {env s ss st env' st1} : Ev (.stmt env s) st (.stmt env' .normal) st1 →
      Sub ⟨.stmts env (s :: ss), st⟩ ⟨.stmts env' ss, st1⟩
  | whileTest {env c body st} : Sub ⟨.whileLoop env c body, st⟩ ⟨.expr env c, st⟩
  | whileBody {env c body st v st1} : Ev (.expr env c) st (.val v) st1 → truthy v = true →
      Sub ⟨.whileLoop env c body, st⟩ ⟨.stmt env body, st1⟩
  | whileNext {env c body st v st1 env' c' st2} : Ev (.expr env c) st (.val v) st1 →
      truthy v = true → Ev (.stmt env body) st1 (.stmt env' c') st2 → c'.continues = true →
      Sub ⟨.whileLoop env c body, st⟩ ⟨.whileLoop env c body, st2⟩
  | forTest {env t update body st} : Sub ⟨.forLoop env (some t) update body, st⟩ ⟨.expr env t, st⟩
  | forBody {env test update body st st1} :
      (test = none ∧ st1 = st ∨ ∃ t v, test = some t ∧ Ev (.expr env t) st (.val v) st1 ∧
        truthy v = true) →
      Sub ⟨.forLoop env test update body, st⟩ ⟨.stmt env body, st1⟩
  | forUpdate {env test u body st st1 env' c' st2} :
      (test = none ∧ st1 = st ∨ ∃ t v, test = some t ∧ Ev (.expr env t) st (.val v) st1 ∧
        truthy v = true) →
      Ev (.stmt env body) st1 (.stmt env' c') st2 → c'.continues = true →
      Sub ⟨.forLoop env test (some u) body, st⟩ ⟨.expr env u, st2⟩
  | forNext {env test update body st st1 env' c' st2 st3} :
      (test = none ∧ st1 = st ∨ ∃ t v, test = some t ∧ Ev (.expr env t) st (.val v) st1 ∧
        truthy v = true) →
      Ev (.stmt env body) st1 (.stmt env' c') st2 → c'.continues = true →
      (update = none ∧ st3 = st2 ∨ ∃ u v, update = some u ∧ Ev (.expr env u) st2 (.val v) st3) →
      Sub ⟨.forLoop env test update body, st⟩ ⟨.forLoop env test update body, st3⟩
  | forOfSkip {env x l i body st st1} : Out (do iterStep (← load l) i) st.tick (some none) st1 →
      Sub ⟨.forOfLoop env x l i body, st⟩ ⟨.forOfLoop env x l (i + 1) body, st1⟩
  | forOfBody {env x l i body st v st1 env' st2} :
      Out (do iterStep (← load l) i) st.tick (some (some v)) st1 →
      Out (bindCell env x v) st1 env' st2 → Sub ⟨.forOfLoop env x l i body, st⟩ ⟨.stmt env' body, st2⟩
  | forOfNext {env x l i body st v st1 env' st2 env'' c' st3} :
      Out (do iterStep (← load l) i) st.tick (some (some v)) st1 →
      Out (bindCell env x v) st1 env' st2 → Ev (.stmt env' body) st2 (.stmt env'' c') st3 →
      c'.continues = true →
      Sub ⟨.forOfLoop env x l i body, st⟩ ⟨.forOfLoop env x l (i + 1) body, st3⟩
  | eachBody {env x v vs body st env' st1} : Out (bindCell env x v) st env' st1 →
      Sub ⟨.forEachValue env x (v :: vs) body, st⟩ ⟨.stmt env' body, st1⟩
  | eachNext {env x v vs body st env' st1 env'' c' st2} : Out (bindCell env x v) st env' st1 →
      Ev (.stmt env' body) st1 (.stmt env'' c') st2 → c'.continues = true →
      Sub ⟨.forEachValue env x (v :: vs) body, st⟩ ⟨.forEachValue env x vs body, st2⟩

/-! ## Channels -/

/-- A completion channel: the kind of completion a run ends in. -/
inductive Channel where
  | normal | ret | brk | cont
  deriving DecidableEq, Repr

/-- Every channel. -/
def allChannels : List Channel := [.normal, .ret, .brk, .cont]

theorem mem_allChannels (k : Channel) : k ∈ allChannels := by cases k <;> simp [allChannels]

/-- The channel of a completion. -/
def Completion.channel : Completion → Channel
  | .normal => .normal
  | .ret _ => .ret
  | .brk => .brk
  | .cont => .cont

/-- The channel a call's outcome ends in; an expression or a call returns normally. -/
def Outcome.channel : Outcome → Channel
  | .stmt _ c | .compl c => c.channel
  | _ => .normal

/-! ## Entries, nodes, instances and work -/

/-- A size quantity an input dimension measures: the length of an Array or String, or of a Map's
or Set's `[[MapData]]`/`[[SetData]]` List. -/
inductive Measure where
  /-- The `k`-th argument of an entry. -/
  | arg (k : ℕ)
  /-- A free variable of the entry. -/
  | var (x : Name)

/-- The syntax a node denotes: its entry's run, or every evaluation of an expression or
statement within it. -/
inductive Site where
  | entry
  | expr (e : Expr)
  | stmt (s : Stmt)

/-- An entry: the function run, its free variables with their declared types (§2.5), and the
input dimensions its nodes are costed over, each with the quantity it measures. -/
structure Entry where
  fn : Func
  scope : List (Name × Ty)
  dims : List (ℕ × Measure)

/-- A node: its entry and its syntax. -/
structure Node where
  entry : Entry
  site : Site

/-- An instance: the input values entering the entry and their input dimensions. `envelope` is
the value of olint's legacy size envelope, which §2 does not constrain. -/
structure Instance where
  heap : Heap
  env : Env
  args : List Value
  dims : ℕ → ℝ
  envelope : ℝ

/-- Instances are ordered by their dimensions, pointwise, so `atTop` is the filter of instances
whose every dimension is large, jointly. -/
instance : Preorder Instance := Preorder.lift Instance.dims

/-- The length a value measures, if it has one: a String's in UTF-16 code units. -/
def Heap.lengthOf (h : Heap) : Value → Option ℕ
  | .str s => some (utf16Length s)
  | .ref l => match h.get l with
    | some (.array elems) => some elems.length
    | some (.map data) => some data.length
    | some (.set data) => some data.length
    | _ => none
  | _ => none

/-- The value of a variable's cell. -/
def Heap.var (h : Heap) (env : Env) (x : Name) : Option Value :=
  match env.lookup x with
  | some l => match h.get l with
    | some (.cell v _) => some v
    | _ => none
  | none => none

/-- The quantity a measure takes in an instance. -/
def Instance.measure (i : Instance) : Measure → Option ℕ
  | .arg k => (i.args[k]?).bind i.heap.lengthOf
  | .var x => (i.heap.var i.env x).bind i.heap.lengthOf

/-- Every location at or past `next` is free. -/
def Heap.WF (h : Heap) : Prop := ∀ l, h.next ≤ l → h.get l = none

/-- Every variable cell holds a value conforming to its declared type (§2.5). -/
def Heap.RespectsTypes (h : Heap) : Prop := ∀ l v τ, h.get l = some (.cell v τ) → Conforms h v τ

/-- Bind the program's top-level definitions, which shadow built-ins of the same name (§2.2),
recursively over one another. -/
def bindProgram (p : Program) (env : Env) : M Env := do
  let mut env := env
  for (x, _) in p.defs do
    env ← bindCell env x .undef
  for (x, f) in p.defs do
    match env.lookup x with
    | some l => store l (.cell (.ref (← allocate (.closure f env))) .any)
    | none => pure ()
  pure env

/-- The root configuration of an entry's run in an instance: the call of the entry function
with the instance's arguments, after the program's definitions are bound. -/
def root (p : Program) (e : Entry) (i : Instance) : Cfg :=
  match (bindProgram p i.env).run ⟨i.heap, 0⟩ with
  | .ok (env, st) => ⟨.callFunc e.fn env .undef i.args, st⟩
  | .error _ => ⟨.callFunc e.fn i.env .undef i.args, ⟨i.heap, 0⟩⟩

/-- The configurations the entry's runs reach in an instance. -/
def Reach (p : Program) (e : Entry) (i : Instance) : Cfg → Prop :=
  Relation.ReflTransGen Sub (root p e i)

/-- A configuration evaluates a node's syntax: the root for the entry itself, else any
evaluation of the node's expression or statement. -/
def Cfg.At (p : Program) (e : Entry) (i : Instance) : Site → Cfg → Prop
  | .entry, c => c = root p e i
  | .expr x, c => ∃ env, c.frame = .expr env x
  | .stmt s, c => ∃ env, c.frame = .stmt env s

/-- The instances §2 admits for an entry: a well-formed heap; arguments conforming to the
parameters' declared types and free variables bound to cells of their declared types (§2.5);
every dimension equal to the quantity it measures; and, since §2.5 holds of every value, every
variable cell conforming to its declared type in every state the run reaches. -/
def Admitted (p : Program) (e : Entry) (i : Instance) : Prop :=
  i.heap.WF ∧
  (match e.fn with
    | .mk params _ _ =>
      ∀ k (x : Name) (τ : Ty), params[k]? = some (x, τ) → Conforms i.heap (arg0 (i.args.drop k)) τ) ∧
  (∀ x τ, (x, τ) ∈ e.scope → ∃ l v, i.env.lookup x = some l ∧ i.heap.get l = some (.cell v τ)) ∧
  (∀ x l, (x, l) ∈ i.env → ∃ τ, (x, τ) ∈ e.scope) ∧
  (∀ j m, (j, m) ∈ e.dims → i.measure m = some ⌈i.dims j⌉₊ ∧ i.dims j = ⌈i.dims j⌉₊) ∧
  ∀ c, Reach p e i c → c.st.heap.RespectsTypes

/-- Run an entry in an instance with the given fuel, returning the work performed. -/
def run (fuel : ℕ) (p : Program) (i : Instance) (e : Entry) : Except Abort ℕ :=
  let c := root p e i
  ((c.frame.run fuel).run c.st).map (·.2.work)

/-- The run halts normally with fuel `fuel`. -/
def HaltsWith (fuel : ℕ) (p : Program) (i : Instance) (e : Entry) : Prop :=
  (run fuel p i e).toBool = true

instance (fuel : ℕ) (p : Program) (i : Instance) (e : Entry) : Decidable (HaltsWith fuel p i e) :=
  inferInstanceAs (Decidable ((run fuel p i e).toBool = true))

/-- Some fuel lets the entry's run in instance `i` halt normally. -/
def Halts (p : Program) (i : Instance) (e : Entry) : Prop := ∃ fuel, HaltsWith fuel p i e

open Classical in
/-- The work entry `e` performs in instance `i`: the work of its run at the least fuel that
halts, and `0` when none does (`Bound` requires halting separately). -/
noncomputable def Work (p : Program) (i : Instance) (e : Entry) : ℕ :=
  if h : Halts p i e then (run (Nat.find h) p i e).toOption.getD 0 else 0

/-! ## Interpreter lemmas -/

theorem run_bind {α β} (x : M α) (f : α → M β) (st : St) :
    (x >>= f).run st = match x.run st with
      | .ok (a, st') => (f a).run st'
      | .error e => .error e := by
  simp only [StateT.run_bind]
  cases x.run st <;> rfl

theorem run_map {α β} (g : α → β) (x : M α) (st : St) :
    (g <$> x).run st = match x.run st with
      | .ok (a, st') => .ok (g a, st')
      | .error e => .error e := by
  show StateT.map g x st = _
  unfold StateT.map
  simp only [StateT.run]
  rcases x st with e | ⟨a, s⟩ <;> rfl

theorem run_tick (n : ℕ) (st : St) : (tick n).run st = .ok ((), { st with work := st.work + n }) :=
  rfl

theorem run_tick1 (st : St) : (tick).run st = .ok ((), st.tick) := rfl

theorem run_pure {α} (a : α) (st : St) : (pure a : M α).run st = .ok (a, st) := rfl

theorem run_throw {α} (e : Abort) (st : St) : (throw e : M α).run st = .error e := rfl

theorem run_discard {α} (x : M α) (st : St) :
    (discard x).run st = match x.run st with
      | .ok (_, st') => .ok ((), st')
      | .error e => .error e := by
  unfold discard
  exact run_map _ x st

/-- A computation that never aborts and performs no work. -/
def Safe {α} (x : M α) : Prop := ∀ st : St, ∃ a h, x.run st = .ok (a, ⟨h, st.work⟩)

theorem Safe.pure {α} (a : α) : Safe (pure a : M α) := fun st => ⟨a, st.heap, rfl⟩

theorem Safe.bind {α β} {x : M α} {f : α → M β} (hx : Safe x) (hf : ∀ a, Safe (f a)) :
    Safe (x >>= f) := by
  intro st
  obtain ⟨a, h, e⟩ := hx st
  obtain ⟨b, h', e'⟩ := hf a ⟨h, st.work⟩
  exact ⟨b, h', by rw [run_bind, e]; exact e'⟩

theorem Safe.allocate (o : Obj) : Safe (allocate o) := fun _ => ⟨_, _, rfl⟩

theorem Safe.store (l : Loc) (o : Obj) : Safe (store l o) := fun _ => ⟨_, _, rfl⟩

theorem Safe.bindCell (env : Env) (x : Name) (v : Value) (τ : Ty) : Safe (bindCell env x v τ) :=
  Safe.bind (Safe.allocate _) fun _ => Safe.pure _

theorem Safe.bindParams : ∀ (env : Env) (ps : List (Name × Ty)) (args : List Value),
    Safe (bindParams env ps args)
  | env, [], _ => by simp only [Olint.Model.bindParams]; exact Safe.pure _
  | env, (x, τ) :: ps, args => by
    simp only [Olint.Model.bindParams]
    exact Safe.bind (Safe.bindCell _ _ _ _) fun env' => Safe.bindParams env' ps _

theorem Safe.enterFunc (f : Func) (env : Env) (self : Value) (args : List Value) :
    Safe (enterFunc f env self args) := by
  obtain ⟨params, body, arrow⟩ := f
  cases arrow
  · exact Safe.bind (Safe.bindCell _ _ _ _) fun env' => Safe.bindParams _ _ _
  · exact Safe.bind (Safe.pure _) fun env' => Safe.bindParams _ _ _

theorem Safe.forIn {α β} (l : List α) (init : β) (f : α → β → M (ForInStep β))
    (hf : ∀ a b, Safe (f a b)) : Safe (forIn l init f) := by
  induction l generalizing init with
  | nil => exact Safe.pure _
  | cons a as ih =>
    rw [List.forIn_cons]
    refine Safe.bind (hf a init) fun r => ?_
    cases r with
    | done b => exact Safe.pure _
    | yield b => exact ih b

/-- Binding a program's definitions never aborts and performs no work. -/
theorem Safe.bindProgram (p : Program) (env : Env) : Safe (bindProgram p env) := by
  unfold Olint.Model.bindProgram
  refine Safe.bind (Safe.forIn _ _ _ fun a b => ?_) fun env' => ?_
  · exact Safe.bind (Safe.bindCell _ _ _ _) fun _ => Safe.pure _
  · refine Safe.bind (Safe.forIn _ _ _ fun a b => ?_) fun _ => Safe.pure _
    obtain ⟨x, f⟩ := a
    dsimp only
    split
    · exact Safe.bind (Safe.allocate _) fun _ => Safe.bind (Safe.store _ _) fun _ => Safe.pure _
    · exact Safe.pure _

theorem bindProgram_safe (p : Program) (env : Env) (h : Heap) :
    ∃ a h', (bindProgram p env).run ⟨h, 0⟩ = .ok (a, ⟨h', 0⟩) :=
  Safe.bindProgram p env ⟨h, 0⟩

end Olint.Model
