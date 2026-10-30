import TAS.Basic

/-
Flow-sensitive typing. `check here Γ c = some Γ'` means `c` is well typed at
core `here` and leaves the context `Γ'`.
-/
set_option autoImplicit false

namespace TAS

inductive Expr where
  | val (v : Val)
  | var (x : Nat)
  | add (e1 e2 : Expr)
  | splat (e : Expr)
  | vadd (e1 e2 : Expr)
  | vld (e : Expr)
  deriving DecidableEq, Repr

inductive Cmd where
  | skip
  | assign (x : Nat) (e : Expr)
  | seq (c1 c2 : Cmd)
  | scope (k : Core) (body : Cmd)
  | block (k : Core) (body : Cmd)
  | vst (b : Nat) (e : Expr)
  | copy (src dst : Nat)
  | mmad (a b acc : Nat)
  deriving DecidableEq, Repr

def inferVal (here : Option Core) (v : Val) : Option Ty :=
  match tyOk here (valTy v) with
  | true => some (valTy v)
  | false => none

def inferVar (here : Option Core) (Γ : Ctx) (x : Nat) : Option Ty :=
  match lookup Γ x with
  | some τ =>
      match tyOk here τ with
      | true => some τ
      | false => none
  | none => none

def inferAdd (t1 t2 : Option Ty) : Option Ty :=
  match t1, t2 with
  | some .scalar, some .scalar => some .scalar
  | _, _ => none

def inferSplat (here : Option Core) (t : Option Ty) : Option Ty :=
  match here, t with
  | some k, some .scalar => some (.reg k)
  | _, _ => none

def inferVadd (here : Option Core) (t1 t2 : Option Ty) : Option Ty :=
  match here, t1, t2 with
  | some k, some (.reg k1), some (.reg k2) =>
      if k = k1 ∧ k = k2 then some (.reg k) else none
  | _, _, _ => none

def inferVld (here : Option Core) (t : Option Ty) : Option Ty :=
  match here, t with
  | some .vec, some (.buf .ub) => some (.reg .vec)
  | _, _ => none

def infer (here : Option Core) (Γ : Ctx) : Expr → Option Ty
  | .val v => inferVal here v
  | .var x => inferVar here Γ x
  | .add e1 e2 => inferAdd (infer here Γ e1) (infer here Γ e2)
  | .splat e => inferSplat here (infer here Γ e)
  | .vadd e1 e2 => inferVadd here (infer here Γ e1) (infer here Γ e2)
  | .vld e => inferVld here (infer here Γ e)

def checkAssign (here : Option Core) (Γ : Ctx) (x : Nat) (e : Expr) : Option Ctx :=
  match infer here Γ e with
  | some τ => some (update Γ x τ)
  | none => none

def checkVst (here : Option Core) (Γ : Ctx) (b : Nat) (e : Expr) : Option Ctx :=
  match here, lookup Γ b, infer here Γ e with
  | some .vec, some (.buf .ub), some (.reg .vec) => some Γ
  | _, _, _ => none

def checkCopy (here : Option Core) (Γ : Ctx) (src dst : Nat) : Option Ctx :=
  match lookup Γ src, lookup Γ dst with
  | some (.buf s), some (.buf d) =>
      match copyOk here s d with
      | true => some Γ
      | false => none
  | _, _ => none

def checkMmad (here : Option Core) (Γ : Ctx) (a b acc : Nat) : Option Ctx :=
  match here, lookup Γ a, lookup Γ b, lookup Γ acc with
  | some .cube, some (.buf .l1), some (.buf .l1), some (.buf .l0c) => some Γ
  | _, _, _, _ => none

def check (here : Option Core) (Γ : Ctx) : Cmd → Option Ctx
  | .skip => some Γ
  | .assign x e => checkAssign here Γ x e
  | .seq c1 c2 =>
      match check here Γ c1 with
      | some Γ1 => check here Γ1 c2
      | none => none
  | .scope k body => check (some k) Γ body
  | .block k body => check (some k) Γ body
  | .vst b e => checkVst here Γ b e
  | .copy src dst => checkCopy here Γ src dst
  | .mmad a b acc => checkMmad here Γ a b acc

end TAS
