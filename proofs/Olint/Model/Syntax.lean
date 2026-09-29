import Mathlib.Data.Nat.Notation
import Mathlib.Data.Int.Notation

/-!
# Syntax

The ECMAScript subset the proof record models, as an inductive AST mirroring the oxc node
kinds olint reasons about.

The subset is a first cut that grows construct by construct. A construct outside it has no
encoding, so a bound over it stays uncertified.

Statements and expressions are mutually inductive, as in oxc (`Statement`, `Expression`).
Functions and classes appear both as declarations and as expressions.
Map and Set have no literal syntax in ECMAScript; they enter through `new Map(…)` and
`new Set(…)`, which resolve to the built-in constructors of `Olint.Axioms`.
-/

namespace Olint.Model

/-- An identifier name. -/
abbrev Name := String

/-- An ECMAScript Number: an IEEE-754 binary64 value (ECMA-262 §6.1.6.1).

`fin neg m e` is the finite value `(-1)^neg · m · 2^e`, so `fin true 0 _` is `-0`. The
operations of `Olint.Model.Double` (in `Olint.Model.Value`) return the canonical form, where
`2^52 ≤ m < 2^53` and `-1074 ≤ e ≤ 971` for a normal value, and `e = -1074`, `m < 2^52` for a
subnormal value or a zero, and read every other `fin` by its exact value. -/
inductive Double where
  | nan
  | inf (neg : Bool)
  | fin (neg : Bool) (m : ℕ) (e : ℤ)
  deriving DecidableEq, Repr

/-- A literal (oxc `BooleanLiteral`, `NullLiteral`, `NumericLiteral`, `StringLiteral`, and the
`undefined` identifier). A numeric literal is the Number value of its source text. -/
inductive Lit where
  | undefined
  | null
  | bool (b : Bool)
  | num (n : Double)
  | str (s : String)
  deriving DecidableEq, Repr

/-- Unary operators (oxc `UnaryOperator`). -/
inductive UnOp where
  | not
  | neg
  | typeof
  /-- `~`. -/
  | bitNot
  deriving DecidableEq, Repr

/-- Binary and logical operators (oxc `BinaryOperator`, `LogicalOperator`). The logical
operators `and`, `or` and `nullish` short-circuit. -/
inductive BinOp where
  | add | sub | mul | div | mod
  | lt | le | gt | ge
  | strictEq | strictNe
  /-- `&`, `|`, `^`, `<<`, `>>` and `>>>`. -/
  | band | bor | bxor | shl | shr | ushr
  | and | or | nullish
  deriving DecidableEq, Repr

/-- Variable declaration kinds (oxc `VariableDeclarationKind`). -/
inductive DeclKind where
  | var | «let» | «const»
  deriving DecidableEq, Repr

/-- TypeScript types as declared (§2.5), for the subset the model covers. -/
inductive Ty where
  | any
  | undefined
  | null
  | boolean
  | number
  | string
  | array (elem : Ty)
  | map (key value : Ty)
  | set (elem : Ty)
  | object (fields : List (Name × Ty))
  | func

mutual

/-- Expressions (oxc `Expression`). -/
inductive Expr where
  /-- A literal. -/
  | lit (l : Lit)
  /-- An identifier reference (oxc `IdentifierReference`). -/
  | ident (x : Name)
  /-- `this` (oxc `ThisExpression`). -/
  | «this»
  /-- A unary expression. -/
  | unary (op : UnOp) (e : Expr)
  /-- A binary or logical expression. -/
  | binary (op : BinOp) (a b : Expr)
  /-- `c ? t : e` (oxc `ConditionalExpression`). -/
  | cond (c t e : Expr)
  /-- `x = e` for an identifier target (oxc `AssignmentExpression`). -/
  | assign (x : Name) (e : Expr)
  /-- `o.p = e` and `o[k] = e` (oxc `AssignmentExpression` with a member target). -/
  | assignIndex (o k e : Expr)
  /-- `x op= e` for an identifier target (oxc `AssignmentExpression` with a compound
  operator); `&&=`, `||=` and `??=` short-circuit. -/
  | assignOp (op : BinOp) (x : Name) (e : Expr)
  /-- `o.p op= e` and `o[k] op= e`. -/
  | assignOpIndex (op : BinOp) (o k e : Expr)
  /-- `x++`, `x--` (`pre = false`) and `++x`, `--x` (`pre = true`) for an identifier target
  (oxc `UpdateExpression`). -/
  | update (inc pre : Bool) (x : Name)
  /-- `o.p++`, `o[k]--`, `++o.p` and the other member-target updates. -/
  | updateIndex (inc pre : Bool) (o k : Expr)
  /-- `o.p` (oxc `StaticMemberExpression`). -/
  | member (o : Expr) (p : Name)
  /-- `o[k]` (oxc `ComputedMemberExpression`). -/
  | index (o k : Expr)
  /-- `f(args)` (oxc `CallExpression`); a `member` or `index` callee is a method call. -/
  | call (callee : Expr) (args : List Expr)
  /-- `new C(args)` (oxc `NewExpression`). -/
  | new (callee : Expr) (args : List Expr)
  /-- A function or arrow expression (oxc `Function`, `ArrowFunctionExpression`). -/
  | func (f : Func)
  /-- A class expression (oxc `Class`). -/
  | klass (c : Class)
  /-- `[e₁, …]` (oxc `ArrayExpression`). -/
  | array (elems : List Expr)
  /-- `{p₁: e₁, …}` (oxc `ObjectExpression`). -/
  | object (props : List (Name × Expr))
  /-- `/pattern/flags` (oxc `RegExpLiteral`). -/
  | regex (pattern flags : String)

/-- Statements (oxc `Statement`). -/
inductive Stmt where
  /-- An expression statement. -/
  | expr (e : Expr)
  /-- `let x: τ = e` (oxc `VariableDeclaration` with one declarator); `τ` is `any` when the
  declaration has no type annotation. -/
  | decl (kind : DeclKind) (x : Name) (ty : Ty) (init : Option Expr)
  /-- `{ … }` (oxc `BlockStatement`). -/
  | block (body : List Stmt)
  /-- `if (c) t else e` (oxc `IfStatement`). -/
  | ite (c : Expr) (t : Stmt) (e : Option Stmt)
  /-- `for (init; test; update) body` (oxc `ForStatement`). -/
  | forLoop (init : Option Stmt) (test : Option Expr) (update : Option Expr) (body : Stmt)
  /-- `for (const x of e) body` (oxc `ForOfStatement`). -/
  | forOf (x : Name) (e : Expr) (body : Stmt)
  /-- `for (const x in e) body` (oxc `ForInStatement`). -/
  | forIn (x : Name) (e : Expr) (body : Stmt)
  /-- `while (c) body` (oxc `WhileStatement`). -/
  | «while» (c : Expr) (body : Stmt)
  /-- `do body while (c)` (oxc `DoWhileStatement`). -/
  | doWhile (body : Stmt) (c : Expr)
  /-- `return e` (oxc `ReturnStatement`). -/
  | ret (e : Option Expr)
  /-- `break` (oxc `BreakStatement`, unlabelled). -/
  | brk
  /-- `continue` (oxc `ContinueStatement`, unlabelled). -/
  | cont
  /-- `function x(…) {…}` (oxc `Function` as a declaration). -/
  | funDecl (x : Name) (f : Func)
  /-- `class x {…}` (oxc `Class` as a declaration). -/
  | classDecl (x : Name) (c : Class)

/-- A function (oxc `Function`, `ArrowFunctionExpression`) with its parameters' declared types.
An arrow function takes `this` from its defining scope. -/
inductive Func where
  | mk (params : List (Name × Ty)) (body : List Stmt) (arrow : Bool)

/-- A class (oxc `Class`): an optional constructor and its methods. -/
inductive Class where
  | mk (ctor : Option Func) (methods : List (Name × Func))

end

/-- A program: its top-level function declarations, which shadow built-ins of the same name
(§2.2). -/
structure Program where
  defs : List (Name × Func)

end Olint.Model
