import Olint.Axioms
import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# Work semantics

A big-step, fuel-indexed definitional interpreter over the syntax of `Olint.Model.Syntax` that
counts work. Every evaluation of an expression or statement charges one unit, every call one
unit, every built-in the work `Olint.Model.step` assigns it (§2.3), and every spec-internal
operation the step cost its world's `SpecOps` gives it (§2.1, the G52 drafts).

Fuel bounds the interpreter's recursion depth and loop iterations, so the interpreter is total.
A run ends normally, runs out of fuel, or aborts: on a TypeError or ReferenceError, on a
construct outside the model, on an implementation-defined built-in (§2.4), on a spec-internal
operation with no work definition, on a read of a value that does not conform to its declared
type (§2.5), or on consulting an intrinsic the analysed program modified (§2.2). A thrown
exception aborts the run too: exceptions are outside the model, and `Olint.Bound` requires
every run it bounds to complete.

**Scopes.** Bindings follow ECMA-262's declaration instantiation. Entering a function binds
`this`, the parameters, and every `var` of its body initialized to `undefined`
(§10.2.11 `FunctionDeclarationInstantiation`); entering a function body or a block creates its
`let`, `const` and `class` bindings uninitialized, in their temporal dead zone, and its function
declarations initialized to their closures (§14.2.3 `BlockDeclarationInstantiation`), so a
closure sees every binding of the scopes around it, whenever it was created. A declaration
statement initializes its binding; a function declaration statement does nothing (§15.2.6).
`for (let …)` copies its bindings into a fresh environment before the first test and after
every iteration (§14.7.4.4 `CreatePerIterationEnvironment`), so a closure created in an
iteration keeps that iteration's binding. The encoder (`src/lean_syntax.rs`) emits function
declarations only directly in function bodies, where strict and sloppy code agree.

**Objects.** Property reads follow the prototype chain (§10.1.8.1 `OrdinaryGet`): own
properties, then the class prototype's methods, then `%Object.prototype%`, whose members the
model does not run, so reading one aborts, and a name no object of the chain has reads as
`undefined`. Built-in objects reach their built-in prototype's modelled members; any other
property of them is outside the model.

`Work : World → Program → Instance → Entry → ℕ` is the model of work the spec's §1 defines for
an entry: the operations the entry performs in one instance, including those of its calls and
callbacks. A node inside an entry is costed over the configurations its entry's runs reach:
`Frame` names every recursive call of the interpreter, `Sub` relates a call to the calls it
makes, and `Reach` closes `Sub` from the entry's root call (`Olint.Bound`).
-/

namespace Olint.Model

/-- Why a run stops before completing. -/
inductive Abort where
  | fuel
  | typeError
  /-- A ReferenceError: an unresolvable name, or a binding read or written in its temporal
  dead zone. -/
  | referenceError
  | unmodelled
  | implementationDefined (b : Builtin)
  /-- A spec-internal operation with no work definition (§2.4, `Olint.Axioms`). -/
  | undefinedWork (op : String)
  /-- A variable read whose value does not conform to the variable's declared type (§2.5). -/
  | typeViolation
  /-- The run consulted an intrinsic the analysed program modified (§2.2). -/
  | modified (x : Intrinsic)
  deriving DecidableEq, Repr

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

/-- Charge the step cost the world's `SpecOps` gives a spec-internal operation. -/
def charge (W : World) (f : SpecOps → ℕ) : M Unit := tick (f W.ops)

/-- Consult an intrinsic, aborting when the analysed program modified it (§2.2). -/
def consult (W : World) (x : Intrinsic) : M Unit :=
  if W.modified x then throw (.modified x) else pure ()

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

/-- Read a variable binding's value and declared type, checking §2.5: a value that does not
conform to the declared type aborts the run, and a binding in its temporal dead zone throws a
ReferenceError. -/
def readVarTy (l : Loc) : M (Value × Ty) := do
  match ← load l with
  | .cell v τ => if conforms (← get).heap v τ then pure (v, τ) else throw .typeViolation
  | .uninit _ => throw .referenceError
  | _ => throw .typeError

/-- Read a variable (§2.5 checked, `readVarTy`). -/
def readVar (l : Loc) : M Value := do pure (← readVarTy l).1

/-- A variable binding's declared type, for a write; a binding in its temporal dead zone
throws a ReferenceError (§9.1.1.1.5 `SetMutableBinding`). -/
def cellType (l : Loc) : M Ty := do
  match ← load l with
  | .cell _ τ => pure τ
  | .uninit _ => throw .referenceError
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
def binop (W : World) : BinOp → Value → Value → M Value
  | .add, .str a, .str b => do charge W (·.stringConcat a b); pure (.str (a ++ b))
  | .add, .str _, _ | .add, _, .str _ => throw .unmodelled
  | .lt, .str _, .str _ | .le, .str _, .str _ | .gt, .str _, .str _ | .ge, .str _, .str _ =>
    throw .unmodelled
  | .strictEq, a, b => do charge W (valueEqWork · a b); pure (.bool (strictEquals a b))
  | .strictNe, a, b => do charge W (valueEqWork · a b); pure (.bool !(strictEquals a b))
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

/-- ECMAScript `typeof` of an object (ECMA-262 §13.5.3.1, Table 41): `"function"` when the object
implements `[[Call]]`, which a closure and a class constructor do (§10.2), and `"object"`
otherwise. -/
def typeofObj : Obj → String
  | .closure _ _ | .klass _ _ _ _ => "function"
  | _ => "object"

/-- Unary operators on the modelled values (ECMA-262 §13.5). -/
def unop : UnOp → Value → M Value
  | .not, v => pure (.bool !(truthy v))
  | .neg, v => do pure (.num (← toNumeric v).neg)
  | .bitNot, v => do pure (.num (Double.ofInt (-(← toNumeric v).toInt32 - 1)))
  | .typeof, .ref l => do pure (.str (typeofObj (← load l)))
  | .typeof, v => pure (.str (match v with
      | .undef => "undefined"
      | .null => "object"
      | .bool _ => "boolean"
      | .num _ => "number"
      | .str _ => "string"
      | .ref _ => "object"
      | .builtin _ => "function"))

/-! ## Bindings and declaration instantiation -/

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

/-- Bind names uninitialized, in their temporal dead zone. -/
def bindUninit (env : Env) : List (Name × Ty) → M Env
  | [] => pure env
  | (x, τ) :: bs => do
    let l ← allocate (.uninit τ)
    bindUninit ((x, l) :: env) bs

/-- The `let`, `const` and `class` declarations of a statement list, each with its declared
type (ECMA-262 §8.2.4 `LexicallyScopedDeclarations`, less function declarations). -/
def lexBindings : List Stmt → List (Name × Ty)
  | [] => []
  | .decl .«let» x τ _ :: ss | .decl .«const» x τ _ :: ss => (x, τ) :: lexBindings ss
  | .classDecl x _ :: ss => (x, .any) :: lexBindings ss
  | _ :: ss => lexBindings ss

/-- The function declarations of a statement list. -/
def funDecls : List Stmt → List (Name × Func)
  | [] => []
  | .funDecl x f :: ss => (x, f) :: funDecls ss
  | _ :: ss => funDecls ss

/-- Initialize one function declaration's binding to its closure over `env`. -/
def storeFun (env : Env) (x : Name) (f : Func) : M Unit :=
  match env.lookup x with
  | some l => do
    let c ← allocate (.closure f env)
    store l (.cell (.ref c) .any)
  | none => pure ()

/-- Initialize the bindings of function declarations to their closures over `env`, charging
the creation of each function object. A later declaration of a name overwrites an earlier one,
as ECMA-262's instantiation keeps the last. -/
def storeFuns (W : World) (env : Env) : List (Name × Func) → M Unit
  | [] => pure ()
  | (x, f) :: fs => do
    charge W (·.closureCreate)
    storeFun env x f
    storeFuns W env fs

/-- Bind function declarations, each initialized to its closure over the environment holding
all of them (§10.2.11 step 36, §14.2.3 step 3.b). -/
def bindFuns (W : World) (env : Env) (fs : List (Name × Func)) : M Env := do
  let env ← bindUninit env (fs.map fun d => (d.1, .any))
  storeFuns W env fs
  pure env

/-- Instantiate a function body's or block's declarations (§14.2.3
`BlockDeclarationInstantiation`): its `let`, `const` and `class` bindings uninitialized, then its
function declarations initialized. -/
def instantiate (W : World) (env : Env) (ss : List Stmt) : M Env := do
  let env ← bindUninit env (lexBindings ss)
  bindFuns W env (funDecls ss)

mutual

/-- The `var` declarations a statement contains, outside nested functions, in order
(§8.2.6 `VarScopedDeclarations`). -/
def varDecls : Stmt → List (Name × Ty)
  | .decl .var x τ _ => [(x, τ)]
  | .block ss => varDeclsList ss
  | .ite _ t e => varDecls t ++ optVarDecls e
  | .forLoop init _ _ body => optVarDecls init ++ varDecls body
  | .forOf _ _ body | .forIn _ _ body | .«while» _ body | .doWhile body _ => varDecls body
  | _ => []

/-- `varDecls` over a list. -/
def varDeclsList : List Stmt → List (Name × Ty)
  | [] => []
  | s :: ss => varDecls s ++ varDeclsList ss

/-- `varDecls` over an optional statement. -/
def optVarDecls : Option Stmt → List (Name × Ty)
  | none => []
  | some s => varDecls s

end

/-- Bind each `var` name not yet bound, initialized to `undefined` with the declared type of
its first declaration (§10.2.11 step 27); a name among `seen`, the parameters and the names
already bound, keeps its binding. -/
def hoistVars (env : Env) : List Name → List (Name × Ty) → M Env
  | _, [] => pure env
  | seen, (x, τ) :: vs =>
    if seen.contains x then hoistVars env seen vs
    else do
      let env ← bindCell env x .undef τ
      hoistVars env (x :: seen) vs

/-- Bind `this` to the receiver for a non-arrow function; an arrow function takes `this` from
its defining scope. -/
def bindThis (arrow : Bool) (env : Env) (self : Value) : M Env :=
  if arrow then pure env else bindCell env "this" self

/-- Enter a function (§10.2.11 `FunctionDeclarationInstantiation`): bind `this` for a
non-arrow function, then the parameters, then the body's `var` names, then instantiate the
body's lexical declarations. -/
def enterFunc (W : World) : Func → Env → Value → List Value → M Env
  | .mk params body arrow, env, self, args => do
    let env ← bindThis arrow env self
    let env ← bindParams env params args
    let env ← hoistVars env (params.map (·.1)) (varDeclsList body)
    instantiate W env body

/-- A declaration statement's effect on its binding: a `let` or `const` initializes the binding
its scope's instantiation created (§14.3.1.2), a `var` with an initializer assigns the hoisted
binding (§14.3.2.1), keeping the binding's declared type. A declaration whose binding no
instantiation created, which the encoder never emits, binds afresh. -/
def initBinding (env : Env) (k : DeclKind) (x : Name) (τ : Ty) (v : Option Value) : M Env := do
  match env.lookup x with
  | some l =>
    match (← get).heap.get l, k with
    | some (.uninit _), .«let» | some (.uninit _), .«const» => do
      store l (.cell (v.getD .undef) τ)
      pure env
    | some (.cell old τ'), .var => do
      store l (.cell (v.getD old) τ')
      pure env
    | _, _ => bindCell env x (v.getD .undef) τ
  | none => bindCell env x (v.getD .undef) τ

/-- The bindings a `for` statement's initializer declares in the loop's own scope: a `let` or
`const` declaration's (§14.7.4.2 step 1). -/
def forScope : Option Stmt → List (Name × Ty)
  | some (.decl .«let» x τ _) | some (.decl .«const» x τ _) => [(x, τ)]
  | _ => []

/-- The bindings a `for` statement copies per iteration: a `let` declaration's
(§14.7.4.2 step 3, `perIterationLets`). -/
def perIteration : Option Stmt → List Name
  | some (.decl .«let» x _ _) => [x]
  | _ => []

/-- `CreatePerIterationEnvironment` (§14.7.4.4): copy each binding into a fresh one holding its
current value, one unit per binding; a binding in its temporal dead zone throws a
ReferenceError. -/
def copyBindings (env : Env) : List Name → M Env
  | [] => pure env
  | x :: xs => do
    match env.lookup x with
    | some l =>
      match ← load l with
      | .cell v τ => do
        tick
        let env ← bindCell env x v τ
        copyBindings env xs
      | .uninit _ => throw .referenceError
      | _ => throw .typeError
    | none => copyBindings env xs

/-- Evaluate a class definition (§15.7.14 `ClassDefinitionEvaluation`): create one closure per
method, then the class's function object, charging each creation. -/
def makeMethods (W : World) (env : Env) : List (Name × Func) → M (List (Name × Loc))
  | [] => pure []
  | (x, f) :: ms => do
    charge W (·.closureCreate)
    let l ← allocate (.closure f env)
    pure ((x, l) :: (← makeMethods W env ms))

/-- Evaluate a class definition over `env`. -/
def makeClass (W : World) (env : Env) : Class → M Loc
  | .mk ctor methods => do
    let ms ← makeMethods W env methods
    charge W (·.closureCreate)
    allocate (.klass ctor ms [] env)

/-- Create the object `new` of a class constructs (§10.1.13 `OrdinaryCreateFromConstructor`). -/
def newObject (W : World) (cls : Loc) : M Loc := do
  charge W (·.objectCreate)
  allocate (.ordinary [] [] (some cls))

/-! ## Properties -/

/-- Set an own property, keeping creation order: overwrite in place, else append. -/
def setProp (props : List (Name × Value)) (x : Name) (v : Value) : List (Name × Value) :=
  if props.any (·.1 == x) then props.map fun p => if p.1 == x then (x, v) else p
  else props ++ [(x, v)]

/-- Consult the prototype an object's lookups reach after its own properties. -/
def consultProto (W : World) (o : Obj) : M Unit :=
  match protoOf o with
  | some x => consult W x
  | none => pure ()

/-- A property lookup reaching `%Object.prototype%`: its members are outside the model, and any
other name reads as `undefined`. -/
def objectProtoGet (W : World) (x : Name) : M Value := do
  consult W .objectPrototype
  charge W (·.propertyLookup)
  if objectProtoMembers.contains x then throw .unmodelled else pure .undef

/-- A property lookup continuing past an ordinary object's own properties (§10.1.8.1
`OrdinaryGet`): the class prototype's methods, then `%Object.prototype%`; an accessor, which
the model does not run, aborts. -/
def protoGet (W : World) (cls : Option Loc) (x : Name) : M Value := do
  match cls with
  | some c =>
    match ← load c with
    | .klass _ ms acc _ =>
      charge W (·.propertyLookup)
      match ms.lookup x with
      | some l => pure (.ref l)
      | none => if acc.contains x then throw .unmodelled else objectProtoGet W x
    | _ => throw .typeError
  | none => objectProtoGet W x

/-- Resolve a property read on an object (§2.2): an ordinary object's own properties, then its
prototype chain (`protoGet`); a built-in object's own `length`, then its built-in prototype's
modelled getters and methods. Each object the lookup visits costs one property lookup. -/
def readProp (W : World) (o : Obj) (x : Name) : M Value := do
  match o with
  | .ordinary props acc cls =>
    charge W (·.propertyLookup)
    match props.lookup x with
    | some v => pure v
    | none => if acc.contains x then throw .unmodelled else protoGet W cls x
  | _ =>
    match builtinGetter o x with
    | some (v, w) => do
      match o, x with
      | .array _, "length" => charge W (·.propertyLookup)
      | _, _ => do consultProto W o; charge W (2 * ·.propertyLookup)
      tick w
      pure v
    | none =>
      match builtinMethod o x with
      | some b => do
        consultProto W o
        charge W (2 * ·.propertyLookup)
        pure (.builtin b)
      | none => throw .unmodelled

/-- `v.x`: a property of an object, or a String's `length` in UTF-16 code units. Reading a
property of `undefined` or `null` throws a TypeError. -/
def getProp (W : World) (v : Value) (x : Name) : M Value :=
  match v with
  | .ref l => do readProp W (← load l) x
  | .str s => if x = "length" then pure (.num (Double.ofNat (utf16Length s))) else throw .unmodelled
  | .undef | .null => throw .typeError
  | _ => throw .unmodelled

/-- A read of an Array element past its length: the lookup walks `%Array.prototype%` and
`%Object.prototype%`, which carry no array index or numeric key, and reads `undefined`. -/
def arrayMiss (W : World) : M Value := do
  consult W .arrayPrototype
  consult W .objectPrototype
  charge W (3 * ·.propertyLookup)
  pure .undef

/-- Read an Array element. -/
def readElem (W : World) (elems : List Value) (i : ℕ) : M Value :=
  match elems[i]? with
  | some w => do charge W (·.propertyLookup); pure w
  | none => arrayMiss W

/-- `v[k]`. A Number key is its `ToString` (§7.1.19 `ToPropertyKey`, a `numberToKey` cost): an
Array reads the element at an array index and `undefined` at any other Number key, which names
no property of it or its prototypes. -/
def getIndex (W : World) (v k : Value) : M Value :=
  match v, k with
  | .ref l, .num d => do
    charge W (·.numberToKey)
    match ← load l with
    | .array elems => match d.toArrayIndex with
      | some i => readElem W elems i
      | none => arrayMiss W
    | o => match d.toPropertyString with
      | some x => readProp W o x
      | none => throw .unmodelled
  | .ref l, .str x => do
    match ← load l, arrayIndexKey x with
    | .array elems, some i => readElem W elems i
    | o, _ => readProp W o x
  | .str s, .str x => getProp W (.str s) x
  | .undef, _ | .null, _ => throw .typeError
  | _, _ => throw .unmodelled

/-- Write an Array element: overwrite within the length; at the length, a new own property,
for which `OrdinarySet` first walks the prototype chain for a setter (§10.1.9.2); a write past
the length, which leaves holes, is outside the model. -/
def putElem (W : World) (l : Loc) (elems : List Value) (i : ℕ) (v : Value) : M Unit := do
  charge W (·.propertyLookup)
  if i < elems.length then store l (.array (elems.set i v))
  else if i = elems.length then do
    consult W .arrayPrototype
    consult W .objectPrototype
    charge W fun o => 2 * o.propertyLookup + o.listAppend
    store l (.array (elems ++ [v]))
  else throw .unmodelled

/-- Write a property of an ordinary object (§10.1.9.2 `OrdinarySet`): overwrite an own data
property; else walk the prototype chain for a setter, which the model does not run, so an
accessor, `%Object.prototype%`'s `__proto__` included, aborts; then create an own property. -/
def putProp (W : World) (l : Loc) (props : List (Name × Value)) (acc : List Name) (cls : Option Loc)
    (x : Name) (v : Value) : M Unit := do
  charge W (·.propertyLookup)
  if props.any (·.1 == x) then store l (.ordinary (setProp props x v) acc cls)
  else if acc.contains x then throw .unmodelled
  else do
    match cls with
    | some c =>
      match ← load c with
      | .klass _ _ cacc _ => do
        charge W (·.propertyLookup)
        if cacc.contains x then throw .unmodelled
      | _ => throw .typeError
    | none => pure ()
    consult W .objectPrototype
    charge W (·.propertyLookup)
    if x = "__proto__" then throw .unmodelled
    store l (.ordinary (setProp props x v) acc cls)

/-- `v[k] = w`. -/
def putIndex (W : World) (v k w : Value) : M Unit :=
  match v with
  | .ref l => do
    match ← load l, k with
    | .array elems, .num d => do
      charge W (·.numberToKey)
      match d.toArrayIndex with
      | some i => putElem W l elems i w
      | none => throw .unmodelled
    | .array elems, .str x => match arrayIndexKey x with
      | some i => putElem W l elems i w
      | none => throw .unmodelled
    | .ordinary props acc cls, .str x => putProp W l props acc cls x w
    | .ordinary props acc cls, .num d => do
      charge W (·.numberToKey)
      match d.toPropertyString with
      | some x => putProp W l props acc cls x w
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
the List is exhausted, `some none` for a deleted entry the step skips. Each step runs the
built-in iterator's `next` on its iterator prototype; Map entries yield fresh `[key, value]`
Arrays (ECMA-262 §24.1.5.2.1, `CreateArrayFromList`). -/
def iterStep (W : World) (o : Obj) (i : ℕ) : M (Option (Option Value)) := do
  match o with
  | .array elems => do consult W .arrayPrototype; pure (elems[i]?.map some)
  | .set data => do consult W .setPrototype; pure (data[i]?)
  | .map data => do
    consult W .mapPrototype
    match data[i]? with
    | none => pure none
    | some none => pure (some none)
    | some (some (k, v)) => do
      charge W fun o => o.objectCreate + 2 * o.listAppend
      pure (some (some (.ref (← allocate (.array [k, v])))))
  | _ => throw .unmodelled

/-- An ordinary object's keys in `OrdinaryOwnPropertyKeys` order (§10.1.11.1): array indices
ascending, then the other String keys in creation order. -/
def ownKeysOrder (props : List (Name × Value)) : List Value :=
  let indices := props.filterMap fun p => (arrayIndexKey p.1).map fun i => (i, p.1)
  let sorted := indices.mergeSort fun a b => decide (a.1 ≤ b.1)
  sorted.map (fun p => Value.str p.2) ++
    (props.filter fun p => (arrayIndexKey p.1).isNone).map fun p => Value.str p.1

/-- The keys `for (x in o)` visits: its own enumerable String keys in property order (§14.7.5.9
`EnumerateObjectProperties`), after its classless prototype chain, which `%Object.prototype%`
ends, contributes no enumerable key; an Array's indices ascending. Accessors and class
instances are outside the model. -/
def forInKeys (W : World) (l : Loc) : M (List Value) := do
  match ← load l with
  | .ordinary props [] none => do consult W .objectPrototype; pure (ownKeysOrder props)
  | .array elems => do
    consult W .arrayPrototype
    consult W .objectPrototype
    pure ((List.range elems.length).map fun i => Value.str (toString i))
  | _ => throw .unmodelled

/-- Run a built-in through `Olint.Model.step` with the world's step costs, charging its work. -/
def runStep (W : World) : Builtin → Bool → Value → List Value → M Value
  | b, isNew, self, args => do
    (stepIntrinsics b isNew).forM (consult W)
    let s ← get
    match step W.ops b isNew s.heap self args with
    | .ok v h w => do modify fun s => { s with heap := h }; tick w; pure v
    | .typeError => throw .typeError
    | .unmodelled => throw .unmodelled
    | .implementationDefined => throw (.implementationDefined b)

mutual

/-- Evaluate an expression. -/
def evalExpr (W : World) : ℕ → Env → Expr → M Value
  | 0, _, _ => throw .fuel
  | fuel + 1, env, e => do
    tick
    match e with
    | .lit l => pure l.value
    | .ident x =>
      match env.lookup x with
      | some l => readVar l
      | none => match builtinGlobal x with
        | some (b, g) => do consult W g; pure (.builtin b)
        | none => throw .referenceError
    | .«this» =>
      match env.lookup "this" with
      | some l => readVar l
      | none => pure .undef
    | .unary op a => do unop op (← evalExpr W fuel env a)
    | .binary op a b => do
      let va ← evalExpr W fuel env a
      match op with
      | .and | .or | .nullish =>
        if evaluatesRight op va then evalExpr W fuel env b else pure va
      | _ => do
        let vb ← evalExpr W fuel env b
        binop W op va vb
    | .cond c t f => do
      if truthy (← evalExpr W fuel env c) then evalExpr W fuel env t else evalExpr W fuel env f
    | .assign x a => do
      let v ← evalExpr W fuel env a
      match env.lookup x with
      | some l => do
        let τ ← cellType l
        store l (.cell v τ)
        pure v
      | none => throw .referenceError
    | .assignIndex o k a => do
      let vo ← evalExpr W fuel env o
      let vk ← evalExpr W fuel env k
      let v ← evalExpr W fuel env a
      putIndex W vo vk v
      pure v
    | .assignOp op x a =>
      match env.lookup x with
      | some l => do
        let (lv, τ) ← readVarTy l
        if evaluatesRight op lv then do
          let rv ← evalExpr W fuel env a
          let r ← match op with
            | .and | .or | .nullish => pure rv
            | _ => binop W op lv rv
          store l (.cell r τ)
          pure r
        else pure lv
      | none => throw .referenceError
    | .assignOpIndex op o k a => do
      let vo ← evalExpr W fuel env o
      let vk ← evalExpr W fuel env k
      let lv ← getIndex W vo vk
      if evaluatesRight op lv then do
        let rv ← evalExpr W fuel env a
        let r ← match op with
          | .and | .or | .nullish => pure rv
          | _ => binop W op lv rv
        putIndex W vo vk r
        pure r
      else pure lv
    | .update inc pre x =>
      match env.lookup x with
      | some l => do
        let (v, τ) ← readVarTy l
        let old ← toNumeric v
        let new := if inc then old.add 1 else old.sub 1
        store l (.cell (.num new) τ)
        pure (.num (if pre then new else old))
      | none => throw .referenceError
    | .updateIndex inc pre o k => do
      let vo ← evalExpr W fuel env o
      let vk ← evalExpr W fuel env k
      let old ← toNumeric (← getIndex W vo vk)
      let new := if inc then old.add 1 else old.sub 1
      putIndex W vo vk (.num new)
      pure (.num (if pre then new else old))
    | .member o x => do getProp W (← evalExpr W fuel env o) x
    | .index o k => do
      let vo ← evalExpr W fuel env o
      let vk ← evalExpr W fuel env k
      getIndex W vo vk
    | .call (.member o x) args => do
      let self ← evalExpr W fuel env o
      let callee ← getProp W self x
      let vs ← evalArgs W fuel env args
      callValue W fuel callee self vs
    | .call (.index o k) args => do
      let self ← evalExpr W fuel env o
      let vk ← evalExpr W fuel env k
      let callee ← getIndex W self vk
      let vs ← evalArgs W fuel env args
      callValue W fuel callee self vs
    | .call f args => do
      let callee ← evalExpr W fuel env f
      let vs ← evalArgs W fuel env args
      callValue W fuel callee .undef vs
    | .new f args => do
      let callee ← evalExpr W fuel env f
      let vs ← evalArgs W fuel env args
      construct W fuel callee vs
    | .func f => do
      charge W (·.closureCreate)
      pure (.ref (← allocate (.closure f env)))
    | .klass c => do pure (.ref (← makeClass W env c))
    | .array elems => do
      let vs ← evalArgs W fuel env elems
      charge W fun o => o.objectCreate + vs.length * o.listAppend
      pure (.ref (← allocate (.array vs)))
    | .object props => do
      let ps ← evalProps W fuel env props
      -- `__proto__: v` sets the new object's prototype (§13.2.5.5), outside the model.
      if ps.any (·.1 == "__proto__") then throw .unmodelled
      charge W fun o => o.objectCreate + ps.length * o.propertyLookup
      pure (.ref (← allocate (.ordinary (ps.foldl (fun acc p => setProp acc p.1 p.2) []) [] none)))
    | .regex pattern flags => do
      charge W (·.regexCreate pattern flags)
      pure (.ref (← allocate (.regexp pattern flags)))

/-- Evaluate arguments left to right. -/
def evalArgs (W : World) : ℕ → Env → List Expr → M (List Value)
  | 0, _, _ => throw .fuel
  | _ + 1, _, [] => pure []
  | fuel + 1, env, e :: es => do
    let v ← evalExpr W fuel env e
    let vs ← evalArgs W fuel env es
    pure (v :: vs)

/-- Evaluate object literal properties left to right. -/
def evalProps (W : World) : ℕ → Env → List (Name × Expr) → M (List (Name × Value))
  | 0, _, _ => throw .fuel
  | _ + 1, _, [] => pure []
  | fuel + 1, env, (x, e) :: ps => do
    let v ← evalExpr W fuel env e
    let vs ← evalProps W fuel env ps
    pure ((x, v) :: vs)

/-- Call a function value with a receiver. A class called without `new` throws a TypeError
(§10.2.1 step 2). -/
def callValue (W : World) : ℕ → Value → Value → List Value → M Value
  | 0, _, _, _ => throw .fuel
  | fuel + 1, callee, self, args => do
    tick
    match callee with
    | .builtin b => runStep W b false self args
    | .ref l =>
      match ← load l with
      | .closure f env => callFunc W fuel f env self args
      | _ => throw .typeError
    | _ => throw .typeError

/-- `new` on a value: a class allocates its instance and runs its constructor, whose returned
object, if any, replaces the instance (§10.2.2 `[[Construct]]` steps 10-11). -/
def construct (W : World) : ℕ → Value → List Value → M Value
  | 0, _, _ => throw .fuel
  | fuel + 1, callee, args => do
    tick
    match callee with
    | .builtin b => runStep W b true .undef args
    | .ref l =>
      match ← load l with
      | .klass ctor _ _ env => do
        let self : Value := .ref (← newObject W l)
        match ctor with
        | some f => do
          match ← callFunc W fuel f env self args with
          | .ref r => pure (.ref r)
          | .builtin b => pure (.builtin b)
          | _ => pure self
        | none => pure self
      | _ => throw .typeError
    | _ => throw .typeError

/-- Run a function body. -/
def callFunc (W : World) : ℕ → Func → Env → Value → List Value → M Value
  | 0, _, _, _, _ => throw .fuel
  | fuel + 1, f, env, self, args => do
    let env ← enterFunc W f env self args
    match f with
    | .mk _ body _ =>
      match (← execStmts W fuel env body).2 with
      | .ret v => pure v
      | _ => pure .undef

/-- Execute a statement, returning the environment it extends. -/
def execStmt (W : World) : ℕ → Env → Stmt → M (Env × Completion)
  | 0, _, _ => throw .fuel
  | fuel + 1, env, s => do
    tick
    match s with
    | .expr e => do let _ ← evalExpr W fuel env e; pure (env, .normal)
    | .decl k x τ init => do
      let v ← match init with
        | some e => do pure (some (← evalExpr W fuel env e))
        | none => pure none
      pure (← initBinding env k x τ v, .normal)
    | .block body => do
      let env' ← instantiate W env body
      pure (env, (← execStmts W fuel env' body).2)
    | .ite c t f => do
      if truthy (← evalExpr W fuel env c) then pure (env, (← execStmt W fuel env t).2)
      else match f with
        | some f => pure (env, (← execStmt W fuel env f).2)
        | none => pure (env, .normal)
    | .forLoop init test update body => do
      let env1 ← bindUninit env (forScope init)
      let env2 ← match init with
        | some i => do pure (← execStmt W fuel env1 i).1
        | none => pure env1
      let env3 ← copyBindings env2 (perIteration init)
      pure (env, (← forLoop W fuel env3 (perIteration init) test update body))
    | .forOf x e body => do
      match ← evalExpr W fuel env e with
      | .ref l => pure (env, (← forOfLoop W fuel env x l 0 body))
      | _ => throw .typeError
    | .forIn x e body => do
      match ← evalExpr W fuel env e with
      | .ref l =>
        match W.ops.ownPropertyKeys with
        | none => throw (.undefinedWork "OrdinaryOwnPropertyKeys")
        | some w => do
          tick w
          let keys ← forInKeys W l
          pure (env, (← forEachValue W fuel env x keys body))
      | .undef | .null => pure (env, .normal)
      | _ => throw .unmodelled
    | .«while» c body => do pure (env, (← whileLoop W fuel env c body))
    | .doWhile body c => do
      let c' := (← execStmt W fuel env body).2
      if c'.continues then pure (env, (← whileLoop W fuel env c body))
      else match c' with
        | .ret v => pure (env, .ret v)
        | _ => pure (env, .normal)
    | .ret e => do
      match e with
      | some e => pure (env, .ret (← evalExpr W fuel env e))
      | none => pure (env, .ret .undef)
    | .brk => pure (env, .brk)
    | .cont => pure (env, .cont)
    | .funDecl x f => do
      match env.lookup x with
      | some _ => pure (env, .normal)
      | none => pure (← bindFuns W env [(x, f)], .normal)
    | .classDecl x c => do
      let l ← makeClass W env c
      pure (← initBinding env .«let» x .any (some (.ref l)), .normal)

/-- Execute a statement list in order, stopping at an abrupt completion. -/
def execStmts (W : World) : ℕ → Env → List Stmt → M (Env × Completion)
  | 0, _, _ => throw .fuel
  | _ + 1, env, [] => pure (env, .normal)
  | fuel + 1, env, s :: ss => do
    let (env', c) ← execStmt W fuel env s
    match c with
    | .normal => execStmts W fuel env' ss
    | c => pure (env', c)

/-- `while (c) body`, one fuel unit per iteration. -/
def whileLoop (W : World) : ℕ → Env → Expr → Stmt → M Completion
  | 0, _, _, _ => throw .fuel
  | fuel + 1, env, c, body => do
    if truthy (← evalExpr W fuel env c) then
      let c' := (← execStmt W fuel env body).2
      if c'.continues then whileLoop W fuel env c body
      else match c' with
        | .ret v => pure (.ret v)
        | _ => pure .normal
    else pure .normal

/-- `for (…; test; update) body` over the iteration environment `env`, one fuel unit per
iteration; after each iteration the bindings `names` are copied into a fresh environment
before the update runs (§14.7.4.2 `ForBodyEvaluation`). -/
def forLoop (W : World) : ℕ → Env → List Name → Option Expr → Option Expr → Stmt → M Completion
  | 0, _, _, _, _, _ => throw .fuel
  | fuel + 1, env, names, test, update, body => do
    let go ← match test with
      | some t => do pure (truthy (← evalExpr W fuel env t))
      | none => pure true
    if go then
      let c' := (← execStmt W fuel env body).2
      if c'.continues then do
        let env' ← copyBindings env names
        match update with
        | some u => discard <| evalExpr W fuel env' u
        | none => pure ()
        forLoop W fuel env' names test update body
      else match c' with
        | .ret v => pure (.ret v)
        | _ => pure .normal
    else pure .normal

/-- `for (const x of o) body` over the live List of an Array, Map or Set, reading it afresh at
each step as ECMAScript iterators do; a deleted entry costs its skip. -/
def forOfLoop (W : World) : ℕ → Env → Name → Loc → ℕ → Stmt → M Completion
  | 0, _, _, _, _, _ => throw .fuel
  | fuel + 1, env, x, l, i, body => do
    tick
    match ← iterStep W (← load l) i with
    | none => pure .normal
    | some none => forOfLoop W fuel env x l (i + 1) body
    | some (some v) => do
      let env' ← bindCell env x v
      let c' := (← execStmt W fuel env' body).2
      if c'.continues then forOfLoop W fuel env x l (i + 1) body
      else match c' with
        | .ret v => pure (.ret v)
        | _ => pure .normal

/-- Run `body` once per value, binding `x` afresh each time. -/
def forEachValue (W : World) : ℕ → Env → Name → List Value → Stmt → M Completion
  | 0, _, _, _, _ => throw .fuel
  | _ + 1, _, _, [], _ => pure .normal
  | fuel + 1, env, x, v :: vs, body => do
    let env' ← bindCell env x v
    let c' := (← execStmt W fuel env' body).2
    if c'.continues then forEachValue W fuel env x vs body
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
  | forLoop (env : Env) (names : List Name) (test update : Option Expr) (body : Stmt)
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
def Frame.run (W : World) (fuel : ℕ) : Frame → M Outcome
  | .expr env e => Outcome.val <$> evalExpr W fuel env e
  | .stmt env s => (fun r => Outcome.stmt r.1 r.2) <$> execStmt W fuel env s
  | .stmts env ss => (fun r => Outcome.stmt r.1 r.2) <$> execStmts W fuel env ss
  | .args env es => Outcome.vals <$> evalArgs W fuel env es
  | .props env ps => Outcome.props <$> evalProps W fuel env ps
  | .callValue callee self vs => Outcome.val <$> Olint.Model.callValue W fuel callee self vs
  | .construct callee vs => Outcome.val <$> Olint.Model.construct W fuel callee vs
  | .callFunc f env self vs => Outcome.val <$> Olint.Model.callFunc W fuel f env self vs
  | .whileLoop env c body => Outcome.compl <$> Olint.Model.whileLoop W fuel env c body
  | .forLoop env names test update body =>
    Outcome.compl <$> Olint.Model.forLoop W fuel env names test update body
  | .forOfLoop env x l i body => Outcome.compl <$> Olint.Model.forOfLoop W fuel env x l i body
  | .forEachValue env x vs body => Outcome.compl <$> Olint.Model.forEachValue W fuel env x vs body

/-- A configuration: a frame and the state it runs from. -/
structure Cfg where
  frame : Frame
  st : St

/-- The configuration completes with fuel `fuel`, returning `o` in state `st'`. -/
def Cfg.Runs (W : World) (c : Cfg) (fuel : ℕ) (o : Outcome) (st' : St) : Prop :=
  (c.frame.run W fuel).run c.st = .ok (o, st')

/-- A computation of `M` returns `a` in state `st'` from state `st`. -/
def Out {α : Type} (x : M α) (st : St) (a : α) (st' : St) : Prop := x.run st = .ok (a, st')

/-- Frame `fr` completes from `st` with some fuel, returning `o` in state `st'`. -/
def Ev (W : World) (fr : Frame) (st : St) (o : Outcome) (st' : St) : Prop :=
  ∃ fuel, Cfg.Runs W ⟨fr, st⟩ fuel o st'

/-- A `for` statement's test ran and let an iteration start: no test, or a truthy one. -/
def ForGo (W : World) (env : Env) (test : Option Expr) (st st1 : St) : Prop :=
  test = none ∧ st1 = st ∨ ∃ t v, test = some t ∧ Ev W (.expr env t) st (.val v) st1 ∧ truthy v = true

/-- `Sub c c'`: running configuration `c` calls configuration `c'`. One constructor per
recursive call of the interpreter; a call made after other calls of the same frame starts from
a state those calls reach. -/
inductive Sub (W : World) : Cfg → Cfg → Prop where
  | unary {env op a st} : Sub W ⟨.expr env (.unary op a), st⟩ ⟨.expr env a, st.tick⟩
  | binaryL {env op a b st} : Sub W ⟨.expr env (.binary op a b), st⟩ ⟨.expr env a, st.tick⟩
  | binaryR {env op a b st v st1} : Ev W (.expr env a) st.tick (.val v) st1 →
      evaluatesRight op v = true → Sub W ⟨.expr env (.binary op a b), st⟩ ⟨.expr env b, st1⟩
  | condTest {env c t f st} : Sub W ⟨.expr env (.cond c t f), st⟩ ⟨.expr env c, st.tick⟩
  | condThen {env c t f st v st1} : Ev W (.expr env c) st.tick (.val v) st1 → truthy v = true →
      Sub W ⟨.expr env (.cond c t f), st⟩ ⟨.expr env t, st1⟩
  | condElse {env c t f st v st1} : Ev W (.expr env c) st.tick (.val v) st1 → truthy v = false →
      Sub W ⟨.expr env (.cond c t f), st⟩ ⟨.expr env f, st1⟩
  | assign {env x a st} : Sub W ⟨.expr env (.assign x a), st⟩ ⟨.expr env a, st.tick⟩
  | assignIndexO {env o k a st} : Sub W ⟨.expr env (.assignIndex o k a), st⟩ ⟨.expr env o, st.tick⟩
  | assignIndexK {env o k a st vo st1} : Ev W (.expr env o) st.tick (.val vo) st1 →
      Sub W ⟨.expr env (.assignIndex o k a), st⟩ ⟨.expr env k, st1⟩
  | assignIndexA {env o k a st vo st1 vk st2} : Ev W (.expr env o) st.tick (.val vo) st1 →
      Ev W (.expr env k) st1 (.val vk) st2 → Sub W ⟨.expr env (.assignIndex o k a), st⟩ ⟨.expr env a, st2⟩
  | assignOp {env op x a st l lv τ} : env.lookup x = some l →
      Out (readVarTy l) st.tick (lv, τ) st.tick →
      evaluatesRight op lv = true → Sub W ⟨.expr env (.assignOp op x a), st⟩ ⟨.expr env a, st.tick⟩
  | assignOpIndexO {env op o k a st} :
      Sub W ⟨.expr env (.assignOpIndex op o k a), st⟩ ⟨.expr env o, st.tick⟩
  | assignOpIndexK {env op o k a st vo st1} : Ev W (.expr env o) st.tick (.val vo) st1 →
      Sub W ⟨.expr env (.assignOpIndex op o k a), st⟩ ⟨.expr env k, st1⟩
  | assignOpIndexA {env op o k a st vo st1 vk st2 lv st3} : Ev W (.expr env o) st.tick (.val vo) st1 →
      Ev W (.expr env k) st1 (.val vk) st2 → Out (getIndex W vo vk) st2 lv st3 →
      evaluatesRight op lv = true → Sub W ⟨.expr env (.assignOpIndex op o k a), st⟩ ⟨.expr env a, st3⟩
  | updateIndexO {env inc pre o k st} :
      Sub W ⟨.expr env (.updateIndex inc pre o k), st⟩ ⟨.expr env o, st.tick⟩
  | updateIndexK {env inc pre o k st vo st1} : Ev W (.expr env o) st.tick (.val vo) st1 →
      Sub W ⟨.expr env (.updateIndex inc pre o k), st⟩ ⟨.expr env k, st1⟩
  | memberO {env o x st} : Sub W ⟨.expr env (.member o x), st⟩ ⟨.expr env o, st.tick⟩
  | indexO {env o k st} : Sub W ⟨.expr env (.index o k), st⟩ ⟨.expr env o, st.tick⟩
  | indexK {env o k st vo st1} : Ev W (.expr env o) st.tick (.val vo) st1 →
      Sub W ⟨.expr env (.index o k), st⟩ ⟨.expr env k, st1⟩
  | callMemberO {env o x args st} :
      Sub W ⟨.expr env (.call (.member o x) args), st⟩ ⟨.expr env o, st.tick⟩
  | callMemberArgs {env o x args st self st1 callee st2} : Ev W (.expr env o) st.tick (.val self) st1 →
      Out (getProp W self x) st1 callee st2 →
      Sub W ⟨.expr env (.call (.member o x) args), st⟩ ⟨.args env args, st2⟩
  | callMemberCall {env o x args st self st1 callee st2 vs st3} :
      Ev W (.expr env o) st.tick (.val self) st1 → Out (getProp W self x) st1 callee st2 →
      Ev W (.args env args) st2 (.vals vs) st3 →
      Sub W ⟨.expr env (.call (.member o x) args), st⟩ ⟨.callValue callee self vs, st3⟩
  | callIndexO {env o k args st} :
      Sub W ⟨.expr env (.call (.index o k) args), st⟩ ⟨.expr env o, st.tick⟩
  | callIndexK {env o k args st self st1} : Ev W (.expr env o) st.tick (.val self) st1 →
      Sub W ⟨.expr env (.call (.index o k) args), st⟩ ⟨.expr env k, st1⟩
  | callIndexArgs {env o k args st self st1 vk st2 callee st3} :
      Ev W (.expr env o) st.tick (.val self) st1 → Ev W (.expr env k) st1 (.val vk) st2 →
      Out (getIndex W self vk) st2 callee st3 →
      Sub W ⟨.expr env (.call (.index o k) args), st⟩ ⟨.args env args, st3⟩
  | callIndexCall {env o k args st self st1 vk st2 callee st3 vs st4} :
      Ev W (.expr env o) st.tick (.val self) st1 → Ev W (.expr env k) st1 (.val vk) st2 →
      Out (getIndex W self vk) st2 callee st3 → Ev W (.args env args) st3 (.vals vs) st4 →
      Sub W ⟨.expr env (.call (.index o k) args), st⟩ ⟨.callValue callee self vs, st4⟩
  | callF {env f args st} : (∀ o x, f ≠ .member o x) → (∀ o k, f ≠ .index o k) →
      Sub W ⟨.expr env (.call f args), st⟩ ⟨.expr env f, st.tick⟩
  | callArgs {env f args st callee st1} : (∀ o x, f ≠ .member o x) → (∀ o k, f ≠ .index o k) →
      Ev W (.expr env f) st.tick (.val callee) st1 →
      Sub W ⟨.expr env (.call f args), st⟩ ⟨.args env args, st1⟩
  | callCall {env f args st callee st1 vs st2} : (∀ o x, f ≠ .member o x) →
      (∀ o k, f ≠ .index o k) → Ev W (.expr env f) st.tick (.val callee) st1 →
      Ev W (.args env args) st1 (.vals vs) st2 →
      Sub W ⟨.expr env (.call f args), st⟩ ⟨.callValue callee .undef vs, st2⟩
  | newF {env f args st} : Sub W ⟨.expr env (.new f args), st⟩ ⟨.expr env f, st.tick⟩
  | newArgs {env f args st callee st1} : Ev W (.expr env f) st.tick (.val callee) st1 →
      Sub W ⟨.expr env (.new f args), st⟩ ⟨.args env args, st1⟩
  | newConstruct {env f args st callee st1 vs st2} : Ev W (.expr env f) st.tick (.val callee) st1 →
      Ev W (.args env args) st1 (.vals vs) st2 →
      Sub W ⟨.expr env (.new f args), st⟩ ⟨.construct callee vs, st2⟩
  | arrayElems {env elems st} : Sub W ⟨.expr env (.array elems), st⟩ ⟨.args env elems, st.tick⟩
  | objectProps {env ps st} : Sub W ⟨.expr env (.object ps), st⟩ ⟨.props env ps, st.tick⟩
  | argsHead {env e es st} : Sub W ⟨.args env (e :: es), st⟩ ⟨.expr env e, st⟩
  | argsTail {env e es st v st1} : Ev W (.expr env e) st (.val v) st1 →
      Sub W ⟨.args env (e :: es), st⟩ ⟨.args env es, st1⟩
  | propsHead {env x e ps st} : Sub W ⟨.props env ((x, e) :: ps), st⟩ ⟨.expr env e, st⟩
  | propsTail {env x e ps st v st1} : Ev W (.expr env e) st (.val v) st1 →
      Sub W ⟨.props env ((x, e) :: ps), st⟩ ⟨.props env ps, st1⟩
  | callValue {l self args st f env} : st.heap.get l = some (.closure f env) →
      Sub W ⟨.callValue (.ref l) self args, st⟩ ⟨.callFunc f env self args, st.tick⟩
  | construct {l args st f ms acc env l' st1} :
      st.heap.get l = some (.klass (some f) ms acc env) →
      Out (newObject W l) st.tick l' st1 →
      Sub W ⟨.construct (.ref l) args, st⟩ ⟨.callFunc f env (.ref l') args, st1⟩
  | callFunc {params body arrow env self args st env' st1} :
      Out (enterFunc W (.mk params body arrow) env self args) st env' st1 →
      Sub W ⟨.callFunc (.mk params body arrow) env self args, st⟩ ⟨.stmts env' body, st1⟩
  | exprStmt {env e st} : Sub W ⟨.stmt env (.expr e), st⟩ ⟨.expr env e, st.tick⟩
  | declInit {env k x τ e st} : Sub W ⟨.stmt env (.decl k x τ (some e)), st⟩ ⟨.expr env e, st.tick⟩
  | block {env ss st env' st1} : Out (instantiate W env ss) st.tick env' st1 →
      Sub W ⟨.stmt env (.block ss), st⟩ ⟨.stmts env' ss, st1⟩
  | iteTest {env c t f st} : Sub W ⟨.stmt env (.ite c t f), st⟩ ⟨.expr env c, st.tick⟩
  | iteThen {env c t f st v st1} : Ev W (.expr env c) st.tick (.val v) st1 → truthy v = true →
      Sub W ⟨.stmt env (.ite c t f), st⟩ ⟨.stmt env t, st1⟩
  | iteElse {env c t f st v st1} : Ev W (.expr env c) st.tick (.val v) st1 → truthy v = false →
      Sub W ⟨.stmt env (.ite c t (some f)), st⟩ ⟨.stmt env f, st1⟩
  | forInit {env i test update body st env1 st1} :
      Out (bindUninit env (forScope (some i))) st.tick env1 st1 →
      Sub W ⟨.stmt env (.forLoop (some i) test update body), st⟩ ⟨.stmt env1 i, st1⟩
  | forStart {env i test update body st env1 st1 env2 c st2 env3 st3} :
      Out (bindUninit env (forScope (some i))) st.tick env1 st1 →
      Ev W (.stmt env1 i) st1 (.stmt env2 c) st2 →
      Out (copyBindings env2 (perIteration (some i))) st2 env3 st3 →
      Sub W ⟨.stmt env (.forLoop (some i) test update body), st⟩
        ⟨.forLoop env3 (perIteration (some i)) test update body, st3⟩
  | forStartBare {env test update body st} :
      Sub W ⟨.stmt env (.forLoop none test update body), st⟩ ⟨.forLoop env [] test update body, st.tick⟩
  | forOfExpr {env x e body st} : Sub W ⟨.stmt env (.forOf x e body), st⟩ ⟨.expr env e, st.tick⟩
  | forOfStart {env x e body st l st1} : Ev W (.expr env e) st.tick (.val (.ref l)) st1 →
      Sub W ⟨.stmt env (.forOf x e body), st⟩ ⟨.forOfLoop env x l 0 body, st1⟩
  | forInExpr {env x e body st} : Sub W ⟨.stmt env (.forIn x e body), st⟩ ⟨.expr env e, st.tick⟩
  | forInStart {env x e body st l st1 w keys st2} : Ev W (.expr env e) st.tick (.val (.ref l)) st1 →
      W.ops.ownPropertyKeys = some w →
      Out (forInKeys W l) { st1 with work := st1.work + w } keys st2 →
      Sub W ⟨.stmt env (.forIn x e body), st⟩ ⟨.forEachValue env x keys body, st2⟩
  | whileStart {env c body st} : Sub W ⟨.stmt env (.«while» c body), st⟩ ⟨.whileLoop env c body, st.tick⟩
  | doBody {env body c st} : Sub W ⟨.stmt env (.doWhile body c), st⟩ ⟨.stmt env body, st.tick⟩
  | doLoop {env body c st env' c' st1} : Ev W (.stmt env body) st.tick (.stmt env' c') st1 →
      c'.continues = true → Sub W ⟨.stmt env (.doWhile body c), st⟩ ⟨.whileLoop env c body, st1⟩
  | retExpr {env e st} : Sub W ⟨.stmt env (.ret (some e)), st⟩ ⟨.expr env e, st.tick⟩
  | stmtsHead {env s ss st} : Sub W ⟨.stmts env (s :: ss), st⟩ ⟨.stmt env s, st⟩
  | stmtsTail {env s ss st env' st1} : Ev W (.stmt env s) st (.stmt env' .normal) st1 →
      Sub W ⟨.stmts env (s :: ss), st⟩ ⟨.stmts env' ss, st1⟩
  | whileTest {env c body st} : Sub W ⟨.whileLoop env c body, st⟩ ⟨.expr env c, st⟩
  | whileBody {env c body st v st1} : Ev W (.expr env c) st (.val v) st1 → truthy v = true →
      Sub W ⟨.whileLoop env c body, st⟩ ⟨.stmt env body, st1⟩
  | whileNext {env c body st v st1 env' c' st2} : Ev W (.expr env c) st (.val v) st1 →
      truthy v = true → Ev W (.stmt env body) st1 (.stmt env' c') st2 → c'.continues = true →
      Sub W ⟨.whileLoop env c body, st⟩ ⟨.whileLoop env c body, st2⟩
  | forTest {env names t update body st} :
      Sub W ⟨.forLoop env names (some t) update body, st⟩ ⟨.expr env t, st⟩
  | forBody {env names test update body st st1} : ForGo W env test st st1 →
      Sub W ⟨.forLoop env names test update body, st⟩ ⟨.stmt env body, st1⟩
  | forUpdate {env names test u body st st1 env' c' st2 env2 st3} : ForGo W env test st st1 →
      Ev W (.stmt env body) st1 (.stmt env' c') st2 → c'.continues = true →
      Out (copyBindings env names) st2 env2 st3 →
      Sub W ⟨.forLoop env names test (some u) body, st⟩ ⟨.expr env2 u, st3⟩
  | forNext {env names test update body st st1 env' c' st2 env2 st3 st4} : ForGo W env test st st1 →
      Ev W (.stmt env body) st1 (.stmt env' c') st2 → c'.continues = true →
      Out (copyBindings env names) st2 env2 st3 →
      (update = none ∧ st4 = st3 ∨ ∃ u v, update = some u ∧ Ev W (.expr env2 u) st3 (.val v) st4) →
      Sub W ⟨.forLoop env names test update body, st⟩ ⟨.forLoop env2 names test update body, st4⟩
  | forOfSkip {env x l i body st st1} : Out (do iterStep W (← load l) i) st.tick (some none) st1 →
      Sub W ⟨.forOfLoop env x l i body, st⟩ ⟨.forOfLoop env x l (i + 1) body, st1⟩
  | forOfBody {env x l i body st v st1 env' st2} :
      Out (do iterStep W (← load l) i) st.tick (some (some v)) st1 →
      Out (bindCell env x v) st1 env' st2 → Sub W ⟨.forOfLoop env x l i body, st⟩ ⟨.stmt env' body, st2⟩
  | forOfNext {env x l i body st v st1 env' st2 env'' c' st3} :
      Out (do iterStep W (← load l) i) st.tick (some (some v)) st1 →
      Out (bindCell env x v) st1 env' st2 → Ev W (.stmt env' body) st2 (.stmt env'' c') st3 →
      c'.continues = true →
      Sub W ⟨.forOfLoop env x l i body, st⟩ ⟨.forOfLoop env x l (i + 1) body, st3⟩
  | eachBody {env x v vs body st env' st1} : Out (bindCell env x v) st env' st1 →
      Sub W ⟨.forEachValue env x (v :: vs) body, st⟩ ⟨.stmt env' body, st1⟩
  | eachNext {env x v vs body st env' st1 env'' c' st2} : Out (bindCell env x v) st env' st1 →
      Ev W (.stmt env' body) st1 (.stmt env'' c') st2 → c'.continues = true →
      Sub W ⟨.forEachValue env x (v :: vs) body, st⟩ ⟨.forEachValue env x vs body, st2⟩

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
  /-- A free variable of the entry, one of its `scope`. -/
  | var (x : Name)
  deriving DecidableEq, Repr

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

/-- An instance: the input values entering the entry and their input dimensions. `receiver` is
the `this` value the entry is called with, which a caller outside the program chooses as it
chooses the arguments. `envelope` is the value of olint's legacy size envelope, which §2 does
not constrain. -/
structure Instance where
  heap : Heap
  env : Env
  args : List Value
  receiver : Value
  dims : ℕ → ℝ
  envelope : ℝ

/-- The length a value measures, if it has one: a String's in UTF-16 code units, an Array's
element count, and the length `|D|` of a Map's `[[MapData]]` or a Set's `[[SetData]]` List. `|D|`
counts every entry ever added, deleted ones included (`Olint.Axioms`, *Size measure*); olint's
size tracking matches it because, by the G36 decision, any `delete` or `clear` makes olint's
size of the collection untracked. A structurally typed object standing in for an Array, Map or
Set (`Olint.Model.conforms`) has no measured length, so an instance that measures one is not
admitted: a dimension over such an argument covers the built-in collections only. -/
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

/-- An object a value can refer to: every heap object but a variable binding. -/
def Obj.isValue : Obj → Bool
  | .cell _ _ | .uninit _ => false
  | _ => true

/-- A value refers only to an object. -/
def Heap.valueOk (h : Heap) : Value → Bool
  | .ref l => match h.get l with
    | some o => o.isValue
    | none => false
  | _ => true

/-- A location holds the kind of object an environment, class or method list refers to. -/
def Heap.bindingOk (h : Heap) (l : Loc) : Bool :=
  match h.get l with
  | some (.cell _ _) | some (.uninit _) => true
  | _ => false

/-- A location holds a class. -/
def Heap.classOk (h : Heap) (l : Loc) : Bool :=
  match h.get l with
  | some (.klass _ _ _ _) => true
  | _ => false

/-- A location holds a closure. -/
def Heap.closureOk (h : Heap) (l : Loc) : Bool :=
  match h.get l with
  | some (.closure _ _) => true
  | _ => false

/-- Every reference an object holds points to an object of the kind it expects. -/
def Heap.objOk (h : Heap) : Obj → Bool
  | .cell v _ => h.valueOk v
  | .uninit _ => true
  | .ordinary props _ cls => props.all (fun p => h.valueOk p.2) && cls.all h.classOk
  | .array elems => elems.all h.valueOk
  | .map data => data.all fun e => e.all fun kv => h.valueOk kv.1 && h.valueOk kv.2
  | .set data => data.all fun e => e.all h.valueOk
  | .closure _ env => env.all fun b => h.bindingOk b.2
  | .klass _ ms _ env => ms.all (fun m => h.closureOk m.2) && env.all fun b => h.bindingOk b.2
  | .regexp _ _ => true

/-- A heap of ECMAScript values: every reference points to an allocated object of the kind it
expects, as every heap an ECMAScript program builds is. -/
def Heap.Closed (h : Heap) : Prop := ∀ l o, h.get l = some o → h.objOk o = true

/-- Bind the program's top-level definitions, which shadow built-ins of the same name (§2.2),
recursively over one another. The definitions' function objects exist before the entry runs,
so binding them charges nothing. -/
def bindProgram (p : Program) (env : Env) : M Env := do
  let mut env := env
  for (x, _) in p.defs do
    env ← bindCell env x .undef
  for (x, f) in p.defs do
    match env.lookup x with
    | some l => store l (.cell (.ref (← allocate (.closure f env))) .any)
    | none => pure ()
  pure env

/-- The root configuration of an entry's run in an instance and a world: the call of the entry
function with the instance's receiver and arguments, after the program's definitions are
bound. -/
def root (p : Program) (e : Entry) (i : Instance) : Cfg :=
  match (bindProgram p i.env).run ⟨i.heap, 0⟩ with
  | .ok (env, st) => ⟨.callFunc e.fn env i.receiver i.args, st⟩
  | .error _ => ⟨.callFunc e.fn i.env i.receiver i.args, ⟨i.heap, 0⟩⟩

/-- The configurations the entry's runs reach in an instance and a world. -/
def Reach (W : World) (p : Program) (e : Entry) (i : Instance) : Cfg → Prop :=
  Relation.ReflTransGen (Sub W) (root p e i)

/-- A configuration evaluates a node's syntax: the root for the entry itself, else any
evaluation of the node's expression or statement. -/
def Cfg.At (p : Program) (e : Entry) (i : Instance) : Site → Cfg → Prop
  | .entry, c => c = root p e i
  | .expr x, c => ∃ env, c.frame = .expr env x
  | .stmt s, c => ∃ env, c.frame = .stmt env s

/-- The instances §2 admits for an entry: a well-formed heap of ECMAScript values; arguments
conforming to the parameters' declared types and free variables bound to cells of their declared
types holding conforming values (§2.5); a receiver that is any ECMAScript value, as a parameter
of no declared type is, since a caller outside the program may call the entry as a method of any
object; and every dimension equal to the quantity it measures.

Admission constrains the entry's inputs only. §2.5 during the run is the read check of
`readVar`: a run that would read a non-conforming value aborts, so it never satisfies a bound,
and no program can make admission empty by violating its types. For a well-formed entry
(`Entry.wf`), admission is non-empty at every valuation of the dimensions
(`Olint.Model.Admitted.exists`). -/
def Admitted (e : Entry) (i : Instance) : Prop :=
  i.heap.WF ∧ i.heap.Closed ∧ (∀ v ∈ i.args, i.heap.valueOk v = true) ∧
  i.heap.valueOk i.receiver = true ∧
  (match e.fn with
    | .mk params _ _ =>
      ∀ k (x : Name) (τ : Ty), params[k]? = some (x, τ) → Conforms i.heap (arg0 (i.args.drop k)) τ) ∧
  (∀ x τ, (x, τ) ∈ e.scope →
    ∃ l v, i.env.lookup x = some l ∧ i.heap.get l = some (.cell v τ) ∧ Conforms i.heap v τ) ∧
  (∀ x l, (x, l) ∈ i.env → ∃ τ, (x, τ) ∈ e.scope) ∧
  (∀ j m, (j, m) ∈ e.dims → i.measure m = some ⌈i.dims j⌉₊ ∧ i.dims j = ⌈i.dims j⌉₊)

/-- No element occurs twice. -/
def distinct {α : Type} [BEq α] : List α → Bool
  | [] => true
  | x :: xs => !xs.contains x && distinct xs

/-- A dimension measures a quantity every admitted instance has: an argument within the
parameters whose declared type is measurable, or a free variable of the entry's scope of a
measurable type. -/
def Entry.dimOk (e : Entry) (m : Measure) : Bool :=
  match e.fn, m with
  | .mk params _ _, .arg k => match params[k]? with
    | some (_, τ) => τ.measurable
    | none => false
  | _, .var x => match e.scope.lookup x with
    | some τ => τ.measurable
    | none => false

/-- A well-formed entry: its parameter and scope types are well formed, its scope names each
free variable once and none that a program definition shadows, and its dimensions have distinct
ids, measure distinct quantities, and each measure a quantity admission can fix. Every
well-formed entry admits an instance at every valuation of its dimensions
(`Olint.Model.Admitted.exists`), so no bound over it holds vacuously. -/
def Entry.wf (p : Program) (e : Entry) : Bool :=
  (match e.fn with
    | .mk params _ _ => params.all fun q => q.2.wf) &&
  e.scope.all (fun s => s.2.wf) &&
  distinctNames (e.scope.map (·.1)) &&
  e.scope.all (fun s => !p.defs.any (·.1 == s.1)) &&
  distinct (e.dims.map (·.1)) && distinct (e.dims.map (·.2)) &&
  e.dims.all fun d => e.dimOk d.2

/-- Run an entry in an instance and a world with the given fuel, returning the work
performed. -/
def run (fuel : ℕ) (W : World) (p : Program) (i : Instance) (e : Entry) : Except Abort ℕ :=
  let c := root p e i
  ((c.frame.run W fuel).run c.st).map (·.2.work)

/-- The run halts normally with fuel `fuel`. -/
def HaltsWith (fuel : ℕ) (W : World) (p : Program) (i : Instance) (e : Entry) : Prop :=
  (run fuel W p i e).toBool = true

instance (fuel : ℕ) (W : World) (p : Program) (i : Instance) (e : Entry) :
    Decidable (HaltsWith fuel W p i e) :=
  inferInstanceAs (Decidable ((run fuel W p i e).toBool = true))

/-- Some fuel lets the entry's run in instance `i` halt normally. -/
def Halts (W : World) (p : Program) (i : Instance) (e : Entry) : Prop :=
  ∃ fuel, HaltsWith fuel W p i e

open Classical in
/-- The work entry `e` performs in instance `i` and world `W`: the work of its run at the least
fuel that halts, and `0` when none does (`Bound` requires halting separately). -/
noncomputable def Work (W : World) (p : Program) (i : Instance) (e : Entry) : ℕ :=
  if h : Halts W p i e then (run (Nat.find h) W p i e).toOption.getD 0 else 0

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

/-- A computation that never aborts and performs at most `w` work. -/
def SafeW {α} (x : M α) (w : ℕ) : Prop :=
  ∀ st : St, ∃ a h n, n ≤ w ∧ x.run st = .ok (a, ⟨h, st.work + n⟩)

/-- A computation that never aborts and performs no work. -/
def Safe {α} (x : M α) : Prop := ∀ st : St, ∃ a h, x.run st = .ok (a, ⟨h, st.work⟩)

theorem Safe.safeW {α} {x : M α} (h : Safe x) : SafeW x 0 := fun st => by
  obtain ⟨a, h', e⟩ := h st
  exact ⟨a, h', 0, le_rfl, by simpa using e⟩

theorem Safe.pure {α} (a : α) : Safe (pure a : M α) := fun st => ⟨a, st.heap, rfl⟩

theorem Safe.bind {α β} {x : M α} {f : α → M β} (hx : Safe x) (hf : ∀ a, Safe (f a)) :
    Safe (x >>= f) := by
  intro st
  obtain ⟨a, h, e⟩ := hx st
  obtain ⟨b, h', e'⟩ := hf a ⟨h, st.work⟩
  exact ⟨b, h', by rw [run_bind, e]; exact e'⟩

theorem Safe.get : Safe (get : M St) := fun st => ⟨st, st.heap, rfl⟩

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

theorem Safe.bindUninit : ∀ (env : Env) (bs : List (Name × Ty)), Safe (bindUninit env bs)
  | env, [] => by simp only [Olint.Model.bindUninit]; exact Safe.pure _
  | env, (x, τ) :: bs => by
    simp only [Olint.Model.bindUninit]
    exact Safe.bind (Safe.allocate _) fun l => Safe.bindUninit _ bs

theorem Safe.hoistVars : ∀ (env : Env) (seen : List Name) (vs : List (Name × Ty)),
    Safe (hoistVars env seen vs)
  | env, _, [] => by simp only [Olint.Model.hoistVars]; exact Safe.pure _
  | env, seen, (x, τ) :: vs => by
    simp only [Olint.Model.hoistVars]
    split
    · exact Safe.hoistVars env seen vs
    · exact Safe.bind (Safe.bindCell _ _ _ _) fun env' => Safe.hoistVars env' _ vs

theorem Safe.initBinding (env : Env) (k : DeclKind) (x : Name) (τ : Ty) (v : Option Value) :
    Safe (initBinding env k x τ v) := by
  unfold Olint.Model.initBinding
  split
  · refine Safe.bind Safe.get fun s => ?_
    split
    · exact Safe.bind (Safe.store _ _) fun _ => Safe.pure _
    · exact Safe.bind (Safe.store _ _) fun _ => Safe.pure _
    · exact Safe.bind (Safe.store _ _) fun _ => Safe.pure _
    · exact Safe.bindCell _ _ _ _
  · exact Safe.bindCell _ _ _ _

theorem SafeW.mono {α} {x : M α} {w w' : ℕ} (h : SafeW x w) (hw : w ≤ w') : SafeW x w' :=
  fun st => by
    obtain ⟨a, h', n, hn, e⟩ := h st
    exact ⟨a, h', n, le_trans hn hw, e⟩

theorem SafeW.bind {α β} {x : M α} {f : α → M β} {w1 w2 : ℕ} (hx : SafeW x w1)
    (hf : ∀ a, SafeW (f a) w2) : SafeW (x >>= f) (w1 + w2) := by
  intro st
  obtain ⟨a, h, n1, hn1, e⟩ := hx st
  obtain ⟨b, h', n2, hn2, e'⟩ := hf a ⟨h, st.work + n1⟩
  refine ⟨b, h', n1 + n2, Nat.add_le_add hn1 hn2, ?_⟩
  rw [run_bind, e]
  simpa [Nat.add_assoc] using e'

theorem SafeW.charge (W : World) (f : SpecOps → ℕ) : SafeW (charge W f) (f W.ops) :=
  fun st => ⟨(), st.heap, f W.ops, le_rfl, rfl⟩

theorem Safe.storeFun (env : Env) (x : Name) (f : Func) : Safe (storeFun env x f) := by
  unfold Olint.Model.storeFun
  split
  · exact Safe.bind (Safe.allocate _) fun _ => Safe.store _ _
  · exact Safe.pure _

theorem SafeW.storeFuns (W : World) (env : Env) : ∀ fs : List (Name × Func),
    SafeW (storeFuns W env fs) (fs.length * W.ops.closureCreate)
  | [] => by
    simp only [Olint.Model.storeFuns]
    exact (Safe.pure ()).safeW.mono (Nat.zero_le _)
  | (x, f) :: fs => by
    simp only [Olint.Model.storeFuns]
    refine (SafeW.bind (SafeW.charge W _) fun _ =>
      SafeW.bind (Safe.storeFun env x f).safeW fun _ => SafeW.storeFuns W env fs).mono ?_
    simp only [List.length_cons, Nat.succ_mul]
    omega

theorem SafeW.instantiate (W : World) (env : Env) (ss : List Stmt) :
    SafeW (instantiate W env ss) ((funDecls ss).length * W.ops.closureCreate) := by
  unfold Olint.Model.instantiate Olint.Model.bindFuns
  refine (SafeW.bind (Safe.bindUninit _ _).safeW fun env' =>
    SafeW.bind (Safe.bindUninit _ _).safeW fun env'' =>
      SafeW.bind (SafeW.storeFuns W env'' _) fun _ => (Safe.pure _).safeW).mono ?_
  simp

theorem SafeW.enterFunc (W : World) (params : List (Name × Ty)) (body : List Stmt)
    (arrow : Bool) (env : Env) (self : Value) (args : List Value) :
    SafeW (enterFunc W (.mk params body arrow) env self args)
      ((funDecls body).length * W.ops.closureCreate) := by
  rw [Olint.Model.enterFunc]
  have hthis : Safe (bindThis arrow env self) := by
    unfold bindThis
    split
    · exact Safe.pure _
    · exact Safe.bindCell _ _ _ _
  refine (SafeW.bind hthis.safeW fun env1 =>
    SafeW.bind (Safe.bindParams _ _ _).safeW fun env2 =>
      SafeW.bind (Safe.hoistVars _ _ _).safeW fun env3 =>
        SafeW.instantiate W env3 body).mono ?_
  simp

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
