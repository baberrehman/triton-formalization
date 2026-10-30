/-
Triton: dtypes, shapes, and the broadcast rule used by `tl` elementwise ops.
-/
import Init.Data.List.Basic

set_option autoImplicit false

namespace Triton

def maxNumel : Nat := 1048576

inductive DType where
  | bool
  | i1 | i8 | i16 | i32 | i64
  | u8 | u16 | u32 | u64
  | pi32
  | f16 | bf16 | f32 | f64
  | f8e4nv | f8e4b8 | f8e4b15 | f8e5 | f8e5b16
  deriving DecidableEq, Repr, BEq

def isFloat : DType → Bool
  | .f16 | .bf16 | .f32 | .f64 | .f8e4nv | .f8e4b8 | .f8e4b15 | .f8e5 | .f8e5b16 => true
  | _ => false

def isInt : DType → Bool
  | .i1 | .i8 | .i16 | .i32 | .i64 | .u8 | .u16 | .u32 | .u64 | .pi32 => true
  | _ => false

def isNumeric : DType → Bool
  | .bool => false
  | _ => true

abbrev Shape := List Nat

def numel : Shape → Nat
  | [] => 1
  | d :: s => d * numel s

def matchDim (a b : Nat) : Option Nat :=
  if a = b then some a
  else if a = 1 then some b
  else if b = 1 then some a
  else none

def replicate1 : Nat → List Nat
  | 0 => []
  | n + 1 => 1 :: replicate1 n

def broadcastAligned : List Nat → List Nat → Option (List Nat)
  | [], [] => some []
  | a :: as, b :: bs =>
      match matchDim a b with
      | none => none
      | some d =>
          match broadcastAligned as bs with
          | none => none
          | some rest => some (d :: rest)
  | _, _ => none

/-- NumPy-style broadcast, which is the rule `semantic.py` uses. Scalars are `[]`. -/
def broadcastShape : List Nat → List Nat → Option (List Nat)
  | [], s => some s
  | s, [] => some s
  | a, b =>
      let a' := if a.length ≤ b.length then replicate1 (b.length - a.length) ++ a else a
      let b' := if b.length < a.length then replicate1 (a.length - b.length) ++ b else b
      broadcastAligned a' b'

def dropAxis : Nat → Shape → Option Shape
  | 0, _ :: rest => some rest
  | n + 1, d :: rest =>
      match dropAxis n rest with
      | none => none
      | some s => some (d :: s)
  | _, [] => none

def keepAxis : Nat → Shape → Option Shape
  | 0, _ :: rest => some (1 :: rest)
  | n + 1, d :: rest =>
      match keepAxis n rest with
      | none => none
      | some s => some (d :: s)
  | _, [] => none

def reduceShape (keep : Bool) (axis : Nat) (s : Shape) : Option Shape :=
  if keep then keepAxis axis s else dropAxis axis s

def replaceAxis : Nat → Nat → Shape → Option Shape
  | 0, k, d :: rest => if k > 0 ∧ k ≤ d then some (k :: rest) else none
  | n + 1, k, d :: rest =>
      match replaceAxis n k rest with
      | none => none
      | some s => some (d :: s)
  | _, _, [] => none

def insert1 : Nat → Shape → Shape
  | 0, s => 1 :: s
  | n + 1, d :: s => d :: insert1 n s
  | n + 1, [] => if n = 0 then [1] else []

def expandShape (axis : Nat) (s : Shape) : Option Shape :=
  if axis ≤ s.length then some (insert1 axis s) else none

def sliceDim : Nat → Nat → Nat → Shape → Option Shape
  | 0, start, finish, d :: rest =>
      if start ≤ finish ∧ finish ≤ d then some ((finish - start) :: rest) else none
  | n + 1, start, finish, d :: rest =>
      match sliceDim n start finish rest with
      | none => none
      | some s => some (d :: s)
  | _, _, _, [] => none

def doubleLast : Shape → Option Shape
  | [] => none
  | [d] => some [d * 2]
  | d :: s =>
      match doubleLast s with
      | none => none
      | some s' => some (d :: s')

def catShape : Nat → Shape → Shape → Option Shape
  | 0, d1 :: r1, d2 :: r2 => if r1 = r2 then some ((d1 + d2) :: r1) else none
  | n + 1, d1 :: r1, d2 :: r2 =>
      if d1 = d2 then
        match catShape n r1 r2 with
        | none => none
        | some s => some (d1 :: s)
      else none
  | _, _, _ => none

def splitShape (s : Shape) : Option Shape :=
  match s.reverse with
  | 2 :: rest => some rest.reverse
  | _ => none

def listAllLt (rank : Nat) : List Nat → Bool
  | [] => true
  | x :: xs => x < rank && listAllLt rank xs

def listNodup : List Nat → Bool
  | [] => true
  | x :: xs => !(xs.contains x) && listNodup xs

def isPerm (rank : Nat) (dims : List Nat) : Bool :=
  dims.length == rank && listNodup dims && listAllLt rank dims

def applyPerm (s dims : List Nat) : List Nat :=
  dims.map fun i => s.getD i 0

inductive Ty where
  | scalar (d : DType)
  | tensor (d : DType) (s : Shape)
  | ptr (d : DType)
  | ptrs (d : DType) (s : Shape)
  | blockPtr (d : DType) (block : Shape)
  | tdesc (d : DType) (block : Shape)
  | pair (a b : Ty)
  deriving DecidableEq, Repr

inductive Val where
  | scalar (d : DType) (n : Int)
  | tensor (d : DType) (s : Shape) (n : Int)
  | ptr (d : DType) (addr : Nat)
  | ptrs (d : DType) (s : Shape) (addr : Nat)
  | blockPtr (d : DType) (block : Shape) (addr : Nat)
  | tdesc (d : DType) (block : Shape) (addr : Nat)
  | pair (a b : Val)
  deriving DecidableEq, Repr

def valTy : Val → Ty
  | .scalar d _ => .scalar d
  | .tensor d s _ => .tensor d s
  | .ptr d _ => .ptr d
  | .ptrs d s _ => .ptrs d s
  | .blockPtr d b _ => .blockPtr d b
  | .tdesc d b _ => .tdesc d b
  | .pair a b => .pair (valTy a) (valTy b)

def payload : Val → Int
  | .scalar _ n => n
  | .tensor _ _ n => n
  | .ptr _ a => Int.ofNat a
  | .ptrs _ _ a => Int.ofNat a
  | .blockPtr _ _ a => Int.ofNat a
  | .tdesc _ _ a => Int.ofNat a
  | .pair a _ => payload a

def pack : Ty → Int → Val
  | .scalar d, n => .scalar d n
  | .tensor d s, n => .tensor d s n
  | .ptr d, n => .ptr d n.toNat
  | .ptrs d s, n => .ptrs d s n.toNat
  | .blockPtr d b, n => .blockPtr d b n.toNat
  | .tdesc d b, n => .tdesc d b n.toNat
  | .pair t1 t2, n => .pair (pack t1 n) (pack t2 n)

def asTensor (d : DType) : Shape → Ty
  | [] => .scalar d
  | s => .tensor d s

def sameDtype : Ty → Option DType
  | .scalar d => some d
  | .tensor d _ => some d
  | _ => none

def shapeOf : Ty → Shape
  | .tensor _ s => s
  | .ptrs _ s => s
  | .blockPtr _ b => b
  | .tdesc _ b => b
  | _ => []

def broadcastVal (a b : Ty) : Option Ty :=
  match sameDtype a, sameDtype b with
  | some d1, some d2 =>
      if d1 = d2 then
        match broadcastShape (shapeOf a) (shapeOf b) with
        | some s => some (asTensor d1 s)
        | none => none
      else none
  | _, _ => none

def broadcast3 (a b c : Ty) : Option Ty :=
  match broadcastVal a b with
  | some t => broadcastVal t c
  | none => none

abbrev Ctx := List (Nat × Ty)
abbrev Env := List (Nat × Val)

def lookup {α : Type} : List (Nat × α) → Nat → Option α
  | [], _ => none
  | (y, a) :: rest, x => if y = x then some a else lookup rest x

/-- Replace the first binding of `x`, or append it. A reassignment of the same type
leaves the context list unchanged, which is what a loop body is required to do. -/
def update : Ctx → Nat → Ty → Ctx
  | [], x, τ => [(x, τ)]
  | (y, t) :: rest, x, τ =>
      if y = x then (x, τ) :: rest else (y, t) :: update rest x τ

structure Cfg where
  pid0 : Nat
  pid1 : Nat
  pid2 : Nat
  nprog0 : Nat
  nprog1 : Nat
  nprog2 : Nat

def pid : Cfg → Nat → Nat
  | c, 0 => c.pid0
  | c, 1 => c.pid1
  | c, _ => c.pid2

def nprog : Cfg → Nat → Nat
  | c, 0 => c.nprog0
  | c, 1 => c.nprog1
  | c, _ => c.nprog2

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

theorem valTy_pack (t : Ty) (n : Int) : valTy (pack t n) = t := by
  induction t with
  | pair t1 t2 ih1 ih2 => simp [pack, valTy, ih1, ih2]
  | _ => simp [pack, valTy]

theorem lookup_update_same (Γ : Ctx) (x : Nat) (τ : Ty) :
    lookup (update Γ x τ) x = some τ := by
  induction Γ with
  | nil => simp [update, lookup]
  | cons hd rest ih =>
      cases hd with
      | mk y t =>
          by_cases h : y = x
          · simp [update, lookup, h]
          · simp [update, lookup, h, ih]

theorem lookup_update_other (Γ : Ctx) (x y : Nat) (τ : Ty) (h : y ≠ x) :
    lookup (update Γ x τ) y = lookup Γ y := by
  induction Γ with
  | nil =>
      simp [update, lookup, Ne.symm h]
  | cons hd rest ih =>
      cases hd with
      | mk z t =>
          by_cases hz : z = x
          · subst hz
            simp [update, lookup, Ne.symm h, h]
          · by_cases hyz : z = y
            · subst hyz
              simp [update, lookup, hz, h]
            · simp [update, lookup, hz, hyz, Ne.symm hyz, ih]

theorem models_assign (env : Env) (Γ : Ctx) (x : Nat) (v : Val) (τ : Ty)
    (hm : models env Γ) (hv : valTy v = τ) :
    models ((x, v) :: env) (update Γ x τ) := by
  intro y τ' hy
  by_cases hyx : y = x
  · subst hyx
    rw [lookup_update_same Γ y τ] at hy
    cases hy
    exact ⟨v, lookup_head y v env, hv⟩
  · rw [lookup_update_other Γ x y τ hyx] at hy
    obtain ⟨v', hl, hty⟩ := hm y τ' hy
    have hl' : lookup ((x, v) :: env) y = some v' := by
      rw [lookup_skip x y v env (Ne.symm hyx), hl]
    exact ⟨v', hl', hty⟩

end Triton
