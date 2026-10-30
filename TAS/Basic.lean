/-
TAS (Triton-Ascend Small): cores, memory spaces, values, and contexts.

A buffer carries one abstract cell. That cell is enough to give `copy`,
`vld`, and `vst` a value to move. It is not a tile.
-/
set_option autoImplicit false

namespace TAS

inductive Core where
  | vec
  | cube
  deriving DecidableEq, Repr, BEq

inductive Space where
  | gm
  | ub
  | l1
  | l0c
  deriving DecidableEq, Repr, BEq

inductive Ty where
  | scalar
  | reg (k : Core)
  | buf (s : Space)
  deriving DecidableEq, Repr, BEq

inductive Val where
  | scalar (n : Int)
  | reg (k : Core) (n : Int)
  | buf (s : Space) (n : Int)
  deriving DecidableEq, Repr

def valTy : Val → Ty
  | .scalar _ => .scalar
  | .reg k _ => .reg k
  | .buf s _ => .buf s

abbrev Ctx := List (Nat × Ty)
abbrev Env := List (Nat × Val)

def lookup {α : Type} : List (Nat × α) → Nat → Option α
  | [], _ => none
  | (y, a) :: rest, x => if y = x then some a else lookup rest x

def update (Γ : Ctx) (x : Nat) (τ : Ty) : Ctx :=
  (x, τ) :: Γ

/-- A register born in core `k` may be read outside any core, or inside `k`. -/
def regOk (here : Option Core) (k : Core) : Bool :=
  match here, k with
  | none, _ => true
  | some .vec, .vec => true
  | some .cube, .cube => true
  | _, _ => false

def tyOk (here : Option Core) (τ : Ty) : Bool :=
  match τ with
  | .reg k => regOk here k
  | _ => true

/-- Directions used by the mixed cube-then-vector kernel. -/
def copyOk (here : Option Core) (src dst : Space) : Bool :=
  match here, src, dst with
  | some .cube, .gm, .l1 => true
  | some .cube, .l0c, .ub => true
  | some .cube, .l0c, .gm => true
  | none, .gm, .ub => true
  | none, .ub, .gm => true
  | _, _, _ => false

def models (env : Env) (Γ : Ctx) : Prop :=
  forall (x : Nat) (t : Ty),
    (lookup Γ x = some t) ->
      (Exists (fun v => And (lookup env x = some v) (valTy v = t)))

theorem lookup_head {α : Type} (x : Nat) (a : α) (xs : List (Nat × α)) :
    lookup ((x, a) :: xs) x = some a := by
  simp [lookup]

theorem lookup_skip {α : Type} (y x : Nat) (a : α) (xs : List (Nat × α))
    (h : y ≠ x) : lookup ((y, a) :: xs) x = lookup xs x := by
  simp [lookup, h]

theorem eq_of_valTy_scalar {v : Val} (h : valTy v = .scalar) : ∃ n, v = .scalar n := by
  cases v with
  | scalar n => exact ⟨n, rfl⟩
  | reg _ _ => cases h
  | buf _ _ => cases h

theorem eq_of_valTy_reg {v : Val} {k : Core} (h : valTy v = .reg k) :
    ∃ n, v = .reg k n := by
  cases v with
  | scalar _ => cases h
  | reg k' n =>
      simp [valTy] at h
      cases h
      exact ⟨n, rfl⟩
  | buf _ _ => cases h

theorem eq_of_valTy_buf {v : Val} {s : Space} (h : valTy v = .buf s) :
    ∃ n, v = .buf s n := by
  cases v with
  | scalar _ => cases h
  | reg _ _ => cases h
  | buf s' n =>
      simp [valTy] at h
      cases h
      exact ⟨n, rfl⟩

theorem reg_here_ok (k : Core) : tyOk (some k) (.reg k) = true := by
  cases k <;> rfl

theorem tyOk_reg {k k' : Core} (h : tyOk (some k) (.reg k') = true) : k = k' := by
  cases k <;> cases k' <;> first
    | rfl
    | simp [tyOk, regOk] at h

theorem models_assign (env : Env) (Γ : Ctx) (x : Nat) (v : Val) (τ : Ty)
    (hm : models env Γ) (hv : valTy v = τ) :
    models ((x, v) :: env) (update Γ x τ) := by
  intro y τ' hy
  by_cases hyx : y = x
  · subst hyx
    unfold update at hy
    rw [lookup_head y τ Γ] at hy
    cases hy
    exact ⟨v, lookup_head y v env, hv⟩
  · unfold update at hy
    rw [lookup_skip x y τ Γ (Ne.symm hyx)] at hy
    obtain ⟨v', hl, hty⟩ := hm y τ' hy
    have hl' : lookup ((x, v) :: env) y = some v' := by
      rw [lookup_skip x y v env (Ne.symm hyx), hl]
    exact ⟨v', hl', hty⟩

theorem models_write (env : Env) (Γ : Ctx) (x : Nat) (v : Val) (τ : Ty)
    (hm : models env Γ) (hΓ : lookup Γ x = some τ) (hv : valTy v = τ) :
    models ((x, v) :: env) Γ := by
  intro y τ' hy
  by_cases hyx : y = x
  · subst hyx
    rw [hΓ] at hy
    cases hy
    exact ⟨v, lookup_head y v env, hv⟩
  · have hskip : lookup ((x, v) :: env) y = lookup env y :=
      lookup_skip x y v env (Ne.symm hyx)
    obtain ⟨v', hl, hty⟩ := hm y τ' hy
    exact ⟨v', hskip.trans hl, hty⟩

end TAS
