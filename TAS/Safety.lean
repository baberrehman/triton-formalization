import TAS.Step

/-
Progress, preservation, and the scope rule.
-/
set_option autoImplicit false

namespace TAS

theorem scope_isolation {k k' : Core} {Γ : Ctx} {x : Nat}
    (h : infer (some k) Γ (.var x) = some (.reg k')) : k = k' := by
  unfold infer inferVar at h
  split at h
  · rename_i τ hlook
    split at h
    · cases h
      exact tyOk_reg (by assumption)
    · cases h
  · cases h

theorem splat_birth {k : Core} {Γ : Ctx} {e : Expr} {τ : Ty}
    (h : infer (some k) Γ (.splat e) = some τ) : τ = .reg k := by
  unfold infer inferSplat at h
  split at h
  · rename_i here t k' hk he
    cases hk
    cases h
    rfl
  · cases h

theorem vld_requires_ub {Γ : Ctx} {e : Expr} {τ : Ty}
    (h : infer (some .vec) Γ (.vld e) = some τ) :
    τ = .reg .vec ∧ infer (some .vec) Γ e = some (.buf .ub) := by
  unfold infer inferVld at h
  split at h
  · cases h
    rename_i heq
    exact ⟨rfl, heq⟩
  · cases h

theorem check_copy_inv {here : Option Core} {Γ : Ctx} {src dst : Nat} {Γout : Ctx}
    (h : check here Γ (.copy src dst) = some Γout) :
    ∃ s d, lookup Γ src = some (.buf s) ∧ lookup Γ dst = some (.buf d) ∧
      copyOk here s d = true ∧ Γout = Γ := by
  unfold check checkCopy at h
  split at h
  · rename_i s d hsrc hdst
    split at h
    · cases h
      exact ⟨s, d, hsrc, hdst, by assumption, rfl⟩
    · cases h
  · cases h

theorem copy_respects_direction {here : Option Core} {Γ : Ctx} {src dst : Nat} {Γout : Ctx}
    (h : check here Γ (.copy src dst) = some Γout) :
    ∃ s d, lookup Γ src = some (.buf s) ∧ lookup Γ dst = some (.buf d) ∧
      copyOk here s d = true := by
  obtain ⟨s, d, hs, hd, hok, _⟩ := check_copy_inv h
  exact ⟨s, d, hs, hd, hok⟩

theorem check_mmad_inv {here : Option Core} {Γ : Ctx} {a b acc : Nat} {Γout : Ctx}
    (h : check here Γ (.mmad a b acc) = some Γout) :
    here = some .cube ∧ lookup Γ a = some (.buf .l1) ∧ lookup Γ b = some (.buf .l1) ∧
      lookup Γ acc = some (.buf .l0c) ∧ Γout = Γ := by
  unfold check checkMmad at h
  split at h
  · cases h
    rename_i ha hb hc
    exact ⟨rfl, ha, hb, hc, rfl⟩
  · cases h

theorem mmad_requires_cube {here : Option Core} {Γ : Ctx} {a b acc : Nat} {Γout : Ctx}
    (h : check here Γ (.mmad a b acc) = some Γout) :
    here = some .cube ∧ lookup Γ a = some (.buf .l1) ∧ lookup Γ b = some (.buf .l1) ∧
      lookup Γ acc = some (.buf .l0c) := by
  obtain ⟨hh, ha, hb, hc, _⟩ := check_mmad_inv h
  exact ⟨hh, ha, hb, hc⟩

theorem stepE_add_left {here : Option Core} {env : Env} {e1 e2 e1' : Expr}
    (hs : stepE here env e1 = some e1') :
    stepE here env (.add e1 e2) = some (.add e1' e2) := by
  unfold stepE
  cases e1 with
  | val v =>
      unfold stepE at hs
      cases hs
  | var x => rw [hs]
  | add a b => rw [hs]
  | splat e => rw [hs]
  | vadd a b => rw [hs]
  | vld e => rw [hs]

theorem stepE_add_right {here : Option Core} {env : Env} {n : Int} {e2 e2' : Expr}
    (hs : stepE here env e2 = some e2') :
    stepE here env (.add (.val (.scalar n)) e2) = some (.add (.val (.scalar n)) e2') := by
  unfold stepE
  cases e2 with
  | val v =>
      unfold stepE at hs
      cases hs
  | var x => rw [hs]
  | add a b => rw [hs]
  | splat e => rw [hs]
  | vadd a b => rw [hs]
  | vld e => rw [hs]

theorem stepE_add_values {here : Option Core} {env : Env} {n m : Int} :
    stepE here env (.add (.val (.scalar n)) (.val (.scalar m))) =
      some (.val (.scalar (n + m))) := by
  unfold stepE
  rfl

theorem stepE_splat_arg {here : Option Core} {env : Env} {e e' : Expr}
    (hs : stepE here env e = some e') :
    stepE here env (.splat e) = some (.splat e') := by
  unfold stepE
  cases e with
  | val v =>
      unfold stepE at hs
      cases hs
  | var x => rw [hs]
  | add a b => rw [hs]
  | splat e => rw [hs]
  | vadd a b => rw [hs]
  | vld e => rw [hs]

theorem stepE_splat_value {env : Env} {k : Core} {n : Int} :
    stepE (some k) env (.splat (.val (.scalar n))) = some (.val (.reg k n)) := by
  unfold stepE
  rfl

theorem stepE_vadd_left {here : Option Core} {env : Env} {e1 e2 e1' : Expr}
    (hs : stepE here env e1 = some e1') :
    stepE here env (.vadd e1 e2) = some (.vadd e1' e2) := by
  unfold stepE
  cases e1 with
  | val v =>
      unfold stepE at hs
      cases hs
  | var x => rw [hs]
  | add a b => rw [hs]
  | splat e => rw [hs]
  | vadd a b => rw [hs]
  | vld e => rw [hs]

theorem stepE_vadd_right {here : Option Core} {env : Env} {k : Core} {n : Int} {e2 e2' : Expr}
    (hs : stepE here env e2 = some e2') :
    stepE here env (.vadd (.val (.reg k n)) e2) = some (.vadd (.val (.reg k n)) e2') := by
  unfold stepE
  cases e2 with
  | val v =>
      unfold stepE at hs
      cases hs
  | var x => rw [hs]
  | add a b => rw [hs]
  | splat e => rw [hs]
  | vadd a b => rw [hs]
  | vld e => rw [hs]

theorem stepE_vadd_values {k : Core} {env : Env} {n m : Int} :
    stepE (some k) env (.vadd (.val (.reg k n)) (.val (.reg k m))) =
      some (.val (.reg k (n + m))) := by
  unfold stepE
  cases k <;> rfl

theorem stepE_vld_arg {here : Option Core} {env : Env} {e e' : Expr}
    (hs : stepE here env e = some e') :
    stepE here env (.vld e) = some (.vld e') := by
  unfold stepE
  cases e with
  | val v =>
      unfold stepE at hs
      cases hs
  | var x => rw [hs]
  | add a b => rw [hs]
  | splat e => rw [hs]
  | vadd a b => rw [hs]
  | vld e => rw [hs]

theorem stepE_vld_value {env : Env} {n : Int} :
    stepE (some .vec) env (.vld (.val (.buf .ub n))) = some (.val (.reg .vec n)) := by
  unfold stepE
  rfl

theorem infer_val_ty {here : Option Core} {Γ : Ctx} {v : Val} {τ : Ty}
    (h : infer here Γ (.val v) = some τ) : valTy v = τ := by
  unfold infer inferVal at h
  split at h
  · cases h
    rfl
  · cases h

theorem expr_progress {here : Option Core} {Γ : Ctx} {env : Env}
    (hm : models env Γ) {e : Expr} {τ : Ty}
    (ht : infer here Γ e = some τ) :
    (∃ v, e = .val v) ∨ ∃ e', stepE here env e = some e' := by
  induction e generalizing τ with
  | val v => exact Or.inl ⟨v, rfl⟩
  | var x =>
      cases hlook : lookup Γ x with
      | none =>
          unfold infer inferVar at ht
          simp [hlook] at ht
      | some τ0 =>
          cases hok : tyOk here τ0 with
          | false =>
              unfold infer inferVar at ht
              simp [hlook, hok] at ht
          | true =>
              unfold infer inferVar at ht
              simp [hlook, hok] at ht
              cases ht
              obtain ⟨v, hv, hty⟩ := hm x τ hlook
              refine Or.inr ⟨.val v, ?_⟩
              unfold stepE
              simp [hv, hty, hok]
  | add e1 e2 ih1 ih2 =>
      unfold infer inferAdd at ht
      split at ht
      · rename_i h1 h2
        cases ht
        cases ih1 h1 with
        | inl hv =>
            obtain ⟨v1, rfl⟩ := hv
            obtain ⟨n, rfl⟩ := eq_of_valTy_scalar (infer_val_ty h1)
            cases ih2 h2 with
            | inl hv =>
                obtain ⟨v2, rfl⟩ := hv
                obtain ⟨m, rfl⟩ := eq_of_valTy_scalar (infer_val_ty h2)
                exact Or.inr ⟨.val (.scalar (n + m)), stepE_add_values⟩
            | inr hs =>
                obtain ⟨e2', hs⟩ := hs
                exact Or.inr ⟨.add (.val (.scalar n)) e2', stepE_add_right hs⟩
        | inr hs =>
            obtain ⟨e1', hs⟩ := hs
            exact Or.inr ⟨.add e1' e2, stepE_add_left hs⟩
      · cases ht
  | splat e ih =>
      cases hhere : here with
      | none =>
          unfold infer inferSplat at ht
          simp [hhere] at ht
      | some k =>
          subst hhere
          unfold infer inferSplat at ht
          split at ht
          · rename_i k2 hk he
            cases hk
            cases ht
            cases ih he with
            | inl hv =>
                obtain ⟨v, rfl⟩ := hv
                obtain ⟨n, rfl⟩ := eq_of_valTy_scalar (infer_val_ty he)
                exact Or.inr ⟨.val (.reg k n), stepE_splat_value⟩
            | inr hs =>
                obtain ⟨e', hs⟩ := hs
                exact Or.inr ⟨.splat e', stepE_splat_arg hs⟩
          · cases ht
  | vadd e1 e2 ih1 ih2 =>
      cases hhere : here with
      | none =>
          unfold infer inferVadd at ht
          simp [hhere] at ht
      | some k =>
          subst hhere
          unfold infer inferVadd at ht
          split at ht
          · rename_i here t1 t2 k' k1 k2 hk h1 h2
            cases hk
            split at ht
            · rename_i heq
              obtain ⟨hk1, hk2⟩ := heq
              subst hk1
              subst hk2
              cases ht
              cases ih1 h1 with
              | inl hv =>
                  obtain ⟨v1, rfl⟩ := hv
                  obtain ⟨n, rfl⟩ := eq_of_valTy_reg (infer_val_ty h1)
                  cases ih2 h2 with
                  | inl hv =>
                      obtain ⟨v2, rfl⟩ := hv
                      obtain ⟨m, rfl⟩ := eq_of_valTy_reg (infer_val_ty h2)
                      exact Or.inr ⟨.val (.reg k (n + m)), stepE_vadd_values⟩
                  | inr hs =>
                      obtain ⟨e2', hs⟩ := hs
                      exact Or.inr ⟨.vadd (.val (.reg k n)) e2', stepE_vadd_right hs⟩
              | inr hs =>
                  obtain ⟨e1', hs⟩ := hs
                  exact Or.inr ⟨.vadd e1' e2, stepE_vadd_left hs⟩
            · cases ht
          · cases ht
  | vld e ih =>
      cases hhere : here with
      | none =>
          unfold infer inferVld at ht
          simp [hhere] at ht
      | some k =>
          cases k with
          | cube =>
              subst hhere
              unfold infer inferVld at ht
              simp at ht
          | vec =>
              subst hhere
              unfold infer inferVld at ht
              split at ht
              · rename_i he
                cases ht
                cases ih he with
                | inl hv =>
                    obtain ⟨v, rfl⟩ := hv
                    obtain ⟨n, rfl⟩ := eq_of_valTy_buf (infer_val_ty he)
                    exact Or.inr ⟨.val (.reg .vec n), stepE_vld_value⟩
                | inr hs =>
                    obtain ⟨e', hs⟩ := hs
                    exact Or.inr ⟨.vld e', stepE_vld_arg hs⟩
              · cases ht

theorem add_right {here : Option Core} {env : Env} {n : Int} {e2 e' : Expr}
    (hs : stepE here env (.add (.val (.scalar n)) e2) = some e')
    (hnot : ∀ m, e2 ≠ .val (.scalar m)) :
    ∃ e2', stepE here env e2 = some e2' ∧ e' = .add (.val (.scalar n)) e2' := by
  cases e2 with
  | val v =>
      cases v with
      | scalar m => exact absurd rfl (hnot m)
      | reg _ _ =>
          dsimp [stepE] at hs
          cases hs
      | buf _ _ =>
          dsimp [stepE] at hs
          cases hs
  | var _ =>
      dsimp [stepE] at hs
      split at hs
      · rename_i e2' hsub
        cases hs
        exact ⟨e2', hsub, rfl⟩
      · cases hs
  | add _ _ =>
      dsimp [stepE] at hs
      split at hs
      · rename_i e2' hsub
        cases hs
        exact ⟨e2', hsub, rfl⟩
      · cases hs
  | splat _ =>
      dsimp [stepE] at hs
      split at hs
      · rename_i e2' hsub
        cases hs
        exact ⟨e2', hsub, rfl⟩
      · cases hs
  | vadd _ _ =>
      dsimp [stepE] at hs
      split at hs
      · rename_i e2' hsub
        cases hs
        exact ⟨e2', hsub, rfl⟩
      · cases hs
  | vld _ =>
      dsimp [stepE] at hs
      split at hs
      · rename_i e2' hsub
        cases hs
        exact ⟨e2', hsub, rfl⟩
      · cases hs

theorem add_left {here : Option Core} {env : Env} {e1 e2 e' : Expr}
    (hs : stepE here env (.add e1 e2) = some e')
    (hnot : ∀ v, e1 ≠ .val v) :
    ∃ e1', stepE here env e1 = some e1' ∧ e' = .add e1' e2 := by
  cases e1 with
  | val v => exact absurd rfl (hnot v)
  | var _ =>
      dsimp [stepE] at hs
      split at hs
      · rename_i e1' hsub
        cases hs
        exact ⟨e1', hsub, rfl⟩
      · cases hs
  | add _ _ =>
      dsimp [stepE] at hs
      split at hs
      · rename_i e1' hsub
        cases hs
        exact ⟨e1', hsub, rfl⟩
      · cases hs
  | splat _ =>
      dsimp [stepE] at hs
      split at hs
      · rename_i e1' hsub
        cases hs
        exact ⟨e1', hsub, rfl⟩
      · cases hs
  | vadd _ _ =>
      dsimp [stepE] at hs
      split at hs
      · rename_i e1' hsub
        cases hs
        exact ⟨e1', hsub, rfl⟩
      · cases hs
  | vld _ =>
      dsimp [stepE] at hs
      split at hs
      · rename_i e1' hsub
        cases hs
        exact ⟨e1', hsub, rfl⟩
      · cases hs

theorem splat_arg {env : Env} {k : Core} {e e' : Expr}
    (hs : stepE (some k) env (.splat e) = some e')
    (hnot : ∀ n, e ≠ .val (.scalar n)) :
    ∃ e0, stepE (some k) env e = some e0 ∧ e' = .splat e0 := by
  cases e with
  | val v =>
      cases v with
      | scalar n => exact absurd rfl (hnot n)
      | reg _ _ =>
          dsimp [stepE] at hs
          cases hs
      | buf _ _ =>
          dsimp [stepE] at hs
          cases hs
  | var _ =>
      dsimp [stepE] at hs
      split at hs
      · rename_i e0 hsub
        cases hs
        exact ⟨e0, hsub, rfl⟩
      · cases hs
  | add _ _ =>
      dsimp [stepE] at hs
      split at hs
      · rename_i e0 hsub
        cases hs
        exact ⟨e0, hsub, rfl⟩
      · cases hs
  | splat _ =>
      dsimp [stepE] at hs
      split at hs
      · rename_i e0 hsub
        cases hs
        exact ⟨e0, hsub, rfl⟩
      · cases hs
  | vadd _ _ =>
      dsimp [stepE] at hs
      split at hs
      · rename_i e0 hsub
        cases hs
        exact ⟨e0, hsub, rfl⟩
      · cases hs
  | vld _ =>
      dsimp [stepE] at hs
      split at hs
      · rename_i e0 hsub
        cases hs
        exact ⟨e0, hsub, rfl⟩
      · cases hs

theorem vadd_values {env : Env} {k : Core} {n m : Int} {e' : Expr}
    (hs : stepE (some k) env (.vadd (.val (.reg k n)) (.val (.reg k m))) = some e') :
    e' = .val (.reg k (n + m)) := by
  cases k <;> (dsimp [stepE] at hs; cases hs; rfl)

theorem vadd_right {env : Env} {k : Core} {n : Int} {e2 e' : Expr}
    (hs : stepE (some k) env (.vadd (.val (.reg k n)) e2) = some e')
    (hnot : ∀ m, e2 ≠ .val (.reg k m)) :
    ∃ e2', stepE (some k) env e2 = some e2' ∧ e' = .vadd (.val (.reg k n)) e2' := by
  cases e2 with
  | val v =>
      cases v with
      | reg k2 m =>
          cases k <;> cases k2 <;> first
            | (exact absurd rfl (hnot m))
            | (dsimp [stepE] at hs; cases hs)
      | scalar _ =>
          dsimp [stepE] at hs
          cases hs
      | buf _ _ =>
          dsimp [stepE] at hs
          cases hs
  | var _ =>
      dsimp [stepE] at hs
      split at hs
      · rename_i e2' hsub
        cases hs
        exact ⟨e2', hsub, rfl⟩
      · cases hs
  | add _ _ =>
      dsimp [stepE] at hs
      split at hs
      · rename_i e2' hsub
        cases hs
        exact ⟨e2', hsub, rfl⟩
      · cases hs
  | splat _ =>
      dsimp [stepE] at hs
      split at hs
      · rename_i e2' hsub
        cases hs
        exact ⟨e2', hsub, rfl⟩
      · cases hs
  | vadd _ _ =>
      dsimp [stepE] at hs
      split at hs
      · rename_i e2' hsub
        cases hs
        exact ⟨e2', hsub, rfl⟩
      · cases hs
  | vld _ =>
      dsimp [stepE] at hs
      split at hs
      · rename_i e2' hsub
        cases hs
        exact ⟨e2', hsub, rfl⟩
      · cases hs

theorem vld_arg {env : Env} {e e' : Expr}
    (hs : stepE (some .vec) env (.vld e) = some e')
    (hnot : ∀ n, e ≠ .val (.buf .ub n)) :
    ∃ e0, stepE (some .vec) env e = some e0 ∧ e' = .vld e0 := by
  cases e with
  | val v =>
      cases v with
      | buf s n =>
          cases s with
          | ub => exact absurd rfl (hnot n)
          | gm =>
              dsimp [stepE] at hs
              cases hs
          | l1 =>
              dsimp [stepE] at hs
              cases hs
          | l0c =>
              dsimp [stepE] at hs
              cases hs
      | scalar _ =>
          dsimp [stepE] at hs
          cases hs
      | reg _ _ =>
          dsimp [stepE] at hs
          cases hs
  | var _ =>
      dsimp [stepE] at hs
      split at hs
      · rename_i e0 hsub
        cases hs
        exact ⟨e0, hsub, rfl⟩
      · cases hs
  | add _ _ =>
      dsimp [stepE] at hs
      split at hs
      · rename_i e0 hsub
        cases hs
        exact ⟨e0, hsub, rfl⟩
      · cases hs
  | splat _ =>
      dsimp [stepE] at hs
      split at hs
      · rename_i e0 hsub
        cases hs
        exact ⟨e0, hsub, rfl⟩
      · cases hs
  | vadd _ _ =>
      dsimp [stepE] at hs
      split at hs
      · rename_i e0 hsub
        cases hs
        exact ⟨e0, hsub, rfl⟩
      · cases hs
  | vld _ =>
      dsimp [stepE] at hs
      split at hs
      · rename_i e0 hsub
        cases hs
        exact ⟨e0, hsub, rfl⟩
      · cases hs

theorem vadd_left {env : Env} {k : Core} {e1 e2 e' : Expr}
    (hs : stepE (some k) env (.vadd e1 e2) = some e')
    (hnot : ∀ v, e1 ≠ .val v) :
    ∃ e1', stepE (some k) env e1 = some e1' ∧ e' = .vadd e1' e2 := by
  cases e1 with
  | val v => exact absurd rfl (hnot v)
  | var _ =>
      dsimp [stepE] at hs
      split at hs
      · rename_i e1' hsub
        cases hs
        exact ⟨e1', hsub, rfl⟩
      · cases hs
  | add _ _ =>
      dsimp [stepE] at hs
      split at hs
      · rename_i e1' hsub
        cases hs
        exact ⟨e1', hsub, rfl⟩
      · cases hs
  | splat _ =>
      dsimp [stepE] at hs
      split at hs
      · rename_i e1' hsub
        cases hs
        exact ⟨e1', hsub, rfl⟩
      · cases hs
  | vadd _ _ =>
      dsimp [stepE] at hs
      split at hs
      · rename_i e1' hsub
        cases hs
        exact ⟨e1', hsub, rfl⟩
      · cases hs
  | vld _ =>
      dsimp [stepE] at hs
      split at hs
      · rename_i e1' hsub
        cases hs
        exact ⟨e1', hsub, rfl⟩
      · cases hs

theorem infer_val_ok {here : Option Core} {Γ : Ctx} {v : Val}
    (h : tyOk here (valTy v) = true) :
    infer here Γ (.val v) = some (valTy v) := by
  unfold infer inferVal
  simp [h]

theorem expr_preservation {here : Option Core} {Γ : Ctx} {env : Env}
    (hm : models env Γ) {e e' : Expr} {τ : Ty}
    (ht : infer here Γ e = some τ) (hs : stepE here env e = some e') :
    infer here Γ e' = some τ := by
  induction e generalizing e' τ with
  | val v =>
      unfold stepE at hs
      cases hs
  | var x =>
      unfold stepE at hs
      split at hs
      · rename_i v hv
        split at hs
        · rename_i hok
          cases hs
          cases hlook : lookup Γ x with
          | none =>
              unfold infer inferVar at ht
              simp [hlook] at ht
          | some τ0 =>
              cases htyk : tyOk here τ0 with
              | false =>
                  unfold infer inferVar at ht
                  simp [hlook, htyk] at ht
              | true =>
                  unfold infer inferVar at ht
                  simp [hlook, htyk] at ht
                  cases ht
                  obtain ⟨v', hv', hty⟩ := hm x τ hlook
                  have : v' = v := by
                    rw [hv] at hv'
                    cases hv'
                    rfl
                  subst this
                  simpa [hty] using infer_val_ok (Γ := Γ) hok
        · cases hs
      · cases hs
  | add e1 e2 ih1 ih2 =>
      unfold infer inferAdd at ht
      split at ht
      · rename_i h1 h2
        cases ht
        cases e1 with
        | val v1 =>
            cases v1 with
            | scalar n =>
                cases e2 with
                | val v2 =>
                    cases v2 with
                    | scalar _ =>
                        dsimp [stepE] at hs
                        cases hs
                        unfold infer inferVal
                        simp [tyOk, valTy]
                    | reg _ _ =>
                        dsimp [stepE] at hs
                        cases hs
                    | buf _ _ =>
                        dsimp [stepE] at hs
                        cases hs
                | var _ =>
                    obtain ⟨e2', hsub, rfl⟩ := add_right hs (by intro m h; cases h)
                    have h2' := ih2 h2 hsub
                    unfold infer inferAdd
                    simp [h1, h2']
                | add _ _ =>
                    obtain ⟨e2', hsub, rfl⟩ := add_right hs (by intro m h; cases h)
                    have h2' := ih2 h2 hsub
                    unfold infer inferAdd
                    simp [h1, h2']
                | splat _ =>
                    obtain ⟨e2', hsub, rfl⟩ := add_right hs (by intro m h; cases h)
                    have h2' := ih2 h2 hsub
                    unfold infer inferAdd
                    simp [h1, h2']
                | vadd _ _ =>
                    obtain ⟨e2', hsub, rfl⟩ := add_right hs (by intro m h; cases h)
                    have h2' := ih2 h2 hsub
                    unfold infer inferAdd
                    simp [h1, h2']
                | vld _ =>
                    obtain ⟨e2', hsub, rfl⟩ := add_right hs (by intro m h; cases h)
                    have h2' := ih2 h2 hsub
                    unfold infer inferAdd
                    simp [h1, h2']
            | reg _ _ =>
                unfold infer inferVal at h1
                split at h1 <;> cases h1
            | buf _ _ =>
                unfold infer inferVal at h1
                split at h1 <;> cases h1
        | var _ =>
            obtain ⟨e1', hsub, rfl⟩ := add_left hs (by intro v h; cases h)
            have h1' := ih1 h1 hsub
            unfold infer inferAdd
            simp [h1', h2]
        | add _ _ =>
            obtain ⟨e1', hsub, rfl⟩ := add_left hs (by intro v h; cases h)
            have h1' := ih1 h1 hsub
            unfold infer inferAdd
            simp [h1', h2]
        | splat _ =>
            obtain ⟨e1', hsub, rfl⟩ := add_left hs (by intro v h; cases h)
            have h1' := ih1 h1 hsub
            unfold infer inferAdd
            simp [h1', h2]
        | vadd _ _ =>
            obtain ⟨e1', hsub, rfl⟩ := add_left hs (by intro v h; cases h)
            have h1' := ih1 h1 hsub
            unfold infer inferAdd
            simp [h1', h2]
        | vld _ =>
            obtain ⟨e1', hsub, rfl⟩ := add_left hs (by intro v h; cases h)
            have h1' := ih1 h1 hsub
            unfold infer inferAdd
            simp [h1', h2]
      · cases ht
  | splat e ih =>
      cases here with
      | none =>
          unfold infer inferSplat at ht
          simp at ht
      | some k =>
          unfold infer inferSplat at ht
          split at ht
          · rename_i k' he
            cases k'
            cases ht
            cases e with
            | val v =>
                cases v with
                | scalar _ =>
                    dsimp [stepE] at hs
                    cases hs
                    exact infer_val_ok (Γ := Γ) (by simpa [valTy] using reg_here_ok k)
                | reg _ _ =>
                    dsimp [stepE] at hs
                    cases hs
                | buf _ _ =>
                    dsimp [stepE] at hs
                    cases hs
            | var _ =>
                obtain ⟨e0, hsub, rfl⟩ := splat_arg hs (by intro n h; cases h)
                have h' := ih he hsub
                unfold infer inferSplat
                simp [h']
            | add _ _ =>
                obtain ⟨e0, hsub, rfl⟩ := splat_arg hs (by intro n h; cases h)
                have h' := ih he hsub
                unfold infer inferSplat
                simp [h']
            | splat _ =>
                obtain ⟨e0, hsub, rfl⟩ := splat_arg hs (by intro n h; cases h)
                have h' := ih he hsub
                unfold infer inferSplat
                simp [h']
            | vadd _ _ =>
                obtain ⟨e0, hsub, rfl⟩ := splat_arg hs (by intro n h; cases h)
                have h' := ih he hsub
                unfold infer inferSplat
                simp [h']
            | vld _ =>
                obtain ⟨e0, hsub, rfl⟩ := splat_arg hs (by intro n h; cases h)
                have h' := ih he hsub
                unfold infer inferSplat
                simp [h']
          · cases ht
  | vadd e1 e2 ih1 ih2 =>
      cases here with
      | none =>
          unfold infer inferVadd at ht
          simp at ht
      | some k =>
          unfold infer inferVadd at ht
          split at ht
          · rename_i here t1 t2 k' k1 k2 hk h1 h2
            cases hk
            split at ht
            · rename_i heq
              obtain ⟨hk1, hk2⟩ := heq
              subst hk1
              subst hk2
              cases ht
              cases e1 with
              | val v1 =>
                  cases v1 with
                  | reg _ n =>
                      obtain ⟨n0, hv1⟩ := eq_of_valTy_reg (infer_val_ty h1)
                      cases hv1
                      cases e2 with
                      | val v2 =>
                          cases v2 with
                          | reg _ _ =>
                              obtain ⟨_, hv2⟩ := eq_of_valTy_reg (infer_val_ty h2)
                              cases hv2
                              have hr := vadd_values hs
                              cases hr
                              exact infer_val_ok (Γ := Γ) (by simpa [valTy] using reg_here_ok k)
                          | scalar _ =>
                              unfold infer inferVal at h2
                              split at h2 <;> cases h2
                          | buf _ _ =>
                              unfold infer inferVal at h2
                              split at h2 <;> cases h2
                      | var _ =>
                          obtain ⟨e2', hsub, rfl⟩ := vadd_right hs (by intro m h; cases h)
                          have h2' := ih2 h2 hsub
                          unfold infer inferVadd
                          simp [h1, h2']
                      | add _ _ =>
                          obtain ⟨e2', hsub, rfl⟩ := vadd_right hs (by intro m h; cases h)
                          have h2' := ih2 h2 hsub
                          unfold infer inferVadd
                          simp [h1, h2']
                      | splat _ =>
                          obtain ⟨e2', hsub, rfl⟩ := vadd_right hs (by intro m h; cases h)
                          have h2' := ih2 h2 hsub
                          unfold infer inferVadd
                          simp [h1, h2']
                      | vadd _ _ =>
                          obtain ⟨e2', hsub, rfl⟩ := vadd_right hs (by intro m h; cases h)
                          have h2' := ih2 h2 hsub
                          unfold infer inferVadd
                          simp [h1, h2']
                      | vld _ =>
                          obtain ⟨e2', hsub, rfl⟩ := vadd_right hs (by intro m h; cases h)
                          have h2' := ih2 h2 hsub
                          unfold infer inferVadd
                          simp [h1, h2']
                  | scalar _ =>
                      unfold infer inferVal at h1
                      split at h1 <;> cases h1
                  | buf _ _ =>
                      unfold infer inferVal at h1
                      split at h1 <;> cases h1
              | var _ =>
                  obtain ⟨e1', hsub, rfl⟩ := vadd_left hs (by intro v h; cases h)
                  have h1' := ih1 h1 hsub
                  unfold infer inferVadd
                  simp [h1', h2]
              | add _ _ =>
                  obtain ⟨e1', hsub, rfl⟩ := vadd_left hs (by intro v h; cases h)
                  have h1' := ih1 h1 hsub
                  unfold infer inferVadd
                  simp [h1', h2]
              | splat _ =>
                  obtain ⟨e1', hsub, rfl⟩ := vadd_left hs (by intro v h; cases h)
                  have h1' := ih1 h1 hsub
                  unfold infer inferVadd
                  simp [h1', h2]
              | vadd _ _ =>
                  obtain ⟨e1', hsub, rfl⟩ := vadd_left hs (by intro v h; cases h)
                  have h1' := ih1 h1 hsub
                  unfold infer inferVadd
                  simp [h1', h2]
              | vld _ =>
                  obtain ⟨e1', hsub, rfl⟩ := vadd_left hs (by intro v h; cases h)
                  have h1' := ih1 h1 hsub
                  unfold infer inferVadd
                  simp [h1', h2]
            · cases ht
          · cases ht
  | vld e ih =>
      cases here with
      | none =>
          unfold infer inferVld at ht
          simp at ht
      | some k =>
          cases k with
          | cube =>
              unfold infer inferVld at ht
              simp at ht
          | vec =>
              unfold infer inferVld at ht
              split at ht
              · rename_i he
                cases ht
                cases e with
                | val v =>
                    cases v with
                    | buf s _ =>
                        cases s with
                        | ub =>
                            dsimp [stepE] at hs
                            cases hs
                            exact infer_val_ok (Γ := Γ) (by simpa [valTy] using reg_here_ok .vec)
                        | gm =>
                            dsimp [stepE] at hs
                            cases hs
                        | l1 =>
                            dsimp [stepE] at hs
                            cases hs
                        | l0c =>
                            dsimp [stepE] at hs
                            cases hs
                    | scalar _ =>
                        dsimp [stepE] at hs
                        cases hs
                    | reg _ _ =>
                        dsimp [stepE] at hs
                        cases hs
                | var _ =>
                    obtain ⟨e0, hsub, rfl⟩ := vld_arg hs (by intro n h; cases h)
                    have h' := ih he hsub
                    unfold infer inferVld
                    simp [h']
                | add _ _ =>
                    obtain ⟨e0, hsub, rfl⟩ := vld_arg hs (by intro n h; cases h)
                    have h' := ih he hsub
                    unfold infer inferVld
                    simp [h']
                | splat _ =>
                    obtain ⟨e0, hsub, rfl⟩ := vld_arg hs (by intro n h; cases h)
                    have h' := ih he hsub
                    unfold infer inferVld
                    simp [h']
                | vadd _ _ =>
                    obtain ⟨e0, hsub, rfl⟩ := vld_arg hs (by intro n h; cases h)
                    have h' := ih he hsub
                    unfold infer inferVld
                    simp [h']
                | vld _ =>
                    obtain ⟨e0, hsub, rfl⟩ := vld_arg hs (by intro n h; cases h)
                    have h' := ih he hsub
                    unfold infer inferVld
                    simp [h']
              · cases ht

theorem step_assign_expr {here : Option Core} {env : Env} {x : Nat} {e e' : Expr}
    (hs : stepE here env e = some e') :
    step here env (.assign x e) = some (env, .assign x e') := by
  cases e <;> first
    | (unfold stepE at hs; cases hs; done)
    | (unfold step; rw [hs])

theorem step_vst_expr {here : Option Core} {env : Env} {b : Nat} {e e' : Expr}
    (hs : stepE here env e = some e') :
    step here env (.vst b e) = some (env, .vst b e') := by
  cases e <;> first
    | (unfold stepE at hs; cases hs; done)
    | (unfold step; rw [hs])

theorem step_seq_cmd {here : Option Core} {env env' : Env} {c1 c2 c1' : Cmd}
    (hs : step here env c1 = some (env', c1')) :
    step here env (.seq c1 c2) = some (env', .seq c1' c2) := by
  cases c1 <;> first
    | (unfold step at hs; cases hs; done)
    | (unfold step; rw [hs])

theorem step_block_cmd {env env' : Env} {k : Core} {body body' : Cmd}
    (hs : step (some k) env body = some (env', body')) :
    step (some k) env (.block k body) = some (env', .block k body') := by
  cases body <;> first
    | (unfold step at hs; cases hs; done)
    | (unfold step; rw [hs])

/-- A typed command has finished, or it takes one step. -/
theorem progress {here : Option Core} {Γ Γout : Ctx} {env : Env} {c : Cmd}
    (hm : models env Γ) (ht : check here Γ c = some Γout) :
    c = .skip ∨ ∃ env' c', step here env c = some (env', c') := by
  induction c generalizing here Γ Γout with
  | skip => exact Or.inl rfl
  | scope k body =>
      exact Or.inr ⟨env, .block k body, by unfold step; rfl⟩
  | assign x e =>
      unfold check checkAssign at ht
      split at ht
      · rename_i τ he
        cases ht
        cases expr_progress hm he with
        | inl hv =>
            obtain ⟨v, rfl⟩ := hv
            exact Or.inr ⟨(x, v) :: env, .skip, by unfold step; rfl⟩
        | inr hs =>
            obtain ⟨e', hs⟩ := hs
            exact Or.inr ⟨env, .assign x e', step_assign_expr hs⟩
      · cases ht
  | seq c1 c2 ih1 _ =>
      unfold check at ht
      split at ht
      · rename_i Γ1 h1
        cases ih1 hm h1 with
        | inl hsk =>
            cases hsk
            exact Or.inr ⟨env, c2, by unfold step; rfl⟩
        | inr hs =>
            obtain ⟨env', c1', hs⟩ := hs
            exact Or.inr ⟨env', .seq c1' c2, step_seq_cmd hs⟩
      · cases ht
  | block k body ih =>
      unfold check at ht
      cases ih (here := some k) hm ht with
      | inl hsk =>
          cases hsk
          exact Or.inr ⟨env, .skip, by unfold step; rfl⟩
      | inr hs =>
          obtain ⟨env', body', hs⟩ := hs
          exact Or.inr ⟨env', .block k body', step_block_cmd hs⟩
  | vst b e =>
      unfold check checkVst at ht
      split at ht
      · cases ht
        rename_i hb he
        cases expr_progress hm he with
        | inl hv =>
            obtain ⟨v, rfl⟩ := hv
            obtain ⟨n, rfl⟩ := eq_of_valTy_reg (infer_val_ty he)
            obtain ⟨_, hvb, htyb⟩ := hm b (.buf .ub) hb
            obtain ⟨_, rfl⟩ := eq_of_valTy_buf htyb
            exact Or.inr ⟨(b, .buf .ub n) :: env, .skip, by unfold step; simp [hvb]⟩
        | inr hs =>
            obtain ⟨e', hs⟩ := hs
            exact Or.inr ⟨env, .vst b e', step_vst_expr hs⟩
      · cases ht
  | copy src dst =>
      obtain ⟨s, d, hsrc, hdst, hok, _⟩ := check_copy_inv ht
      obtain ⟨vs, hvs, htys⟩ := hm src (.buf s) hsrc
      obtain ⟨_, hvd, htyd⟩ := hm dst (.buf d) hdst
      obtain ⟨n, rfl⟩ := eq_of_valTy_buf htys
      obtain ⟨_, rfl⟩ := eq_of_valTy_buf htyd
      exact Or.inr ⟨(dst, .buf d n) :: env, .skip, by unfold step; simp [hvs, hvd, hok]⟩
  | mmad a b acc =>
      obtain ⟨hh, ha, hb, hc, _⟩ := check_mmad_inv ht
      obtain ⟨_, hva, htya⟩ := hm a (.buf .l1) ha
      obtain ⟨_, hvb, htyb⟩ := hm b (.buf .l1) hb
      obtain ⟨_, hvc, htyc⟩ := hm acc (.buf .l0c) hc
      obtain ⟨_, rfl⟩ := eq_of_valTy_buf htya
      obtain ⟨_, rfl⟩ := eq_of_valTy_buf htyb
      obtain ⟨_, rfl⟩ := eq_of_valTy_buf htyc
      cases hh
      exact Or.inr ⟨env, .skip, by unfold step; simp [hva, hvb, hvc]⟩

theorem seq_step_inv {here : Option Core} {env env' : Env} {c1 c2 c' : Cmd}
    (hs : step here env (.seq c1 c2) = some (env', c')) :
    (c1 = .skip ∧ env' = env ∧ c' = c2) ∨
      ∃ c1', step here env c1 = some (env', c1') ∧ c' = .seq c1' c2 := by
  cases c1 with
  | skip =>
      dsimp [step] at hs
      cases hs
      exact Or.inl ⟨rfl, rfl, rfl⟩
  | assign _ _ =>
      dsimp [step] at hs
      split at hs
      · rename_i env1 c1' hsub
        cases hs
        exact Or.inr ⟨c1', hsub, rfl⟩
      · cases hs
  | seq _ _ =>
      dsimp [step] at hs
      split at hs
      · rename_i env1 c1' hsub
        cases hs
        exact Or.inr ⟨c1', hsub, rfl⟩
      · cases hs
  | scope k body =>
      dsimp [step] at hs
      cases hs
      exact Or.inr ⟨.block k body, by unfold step; rfl, rfl⟩
  | block _ _ =>
      dsimp [step] at hs
      split at hs
      · rename_i env1 c1' hsub
        cases hs
        exact Or.inr ⟨c1', hsub, rfl⟩
      · cases hs
  | vst _ _ =>
      dsimp [step] at hs
      split at hs
      · rename_i env1 c1' hsub
        cases hs
        exact Or.inr ⟨c1', hsub, rfl⟩
      · cases hs
  | copy _ _ =>
      dsimp [step] at hs
      split at hs
      · rename_i env1 c1' hsub
        cases hs
        exact Or.inr ⟨c1', hsub, rfl⟩
      · cases hs
  | mmad _ _ _ =>
      dsimp [step] at hs
      split at hs
      · rename_i env1 c1' hsub
        cases hs
        exact Or.inr ⟨c1', hsub, rfl⟩
      · cases hs

theorem block_step_inv {here : Option Core} {env env' : Env} {k : Core} {body c' : Cmd}
    (hs : step here env (.block k body) = some (env', c')) :
    (body = .skip ∧ env' = env ∧ c' = .skip) ∨
      ∃ body', step (some k) env body = some (env', body') ∧ c' = .block k body' := by
  cases body with
  | skip =>
      dsimp [step] at hs
      cases hs
      exact Or.inl ⟨rfl, rfl, rfl⟩
  | assign _ _ =>
      dsimp [step] at hs
      split at hs
      · rename_i env1 body' hsub
        cases hs
        exact Or.inr ⟨body', hsub, rfl⟩
      · cases hs
  | seq _ _ =>
      dsimp [step] at hs
      split at hs
      · rename_i env1 body' hsub
        cases hs
        exact Or.inr ⟨body', hsub, rfl⟩
      · cases hs
  | scope k2 body2 =>
      dsimp [step] at hs
      cases hs
      exact Or.inr ⟨.block k2 body2, by unfold step; rfl, rfl⟩
  | block _ _ =>
      dsimp [step] at hs
      split at hs
      · rename_i env1 body' hsub
        cases hs
        exact Or.inr ⟨body', hsub, rfl⟩
      · cases hs
  | vst _ _ =>
      dsimp [step] at hs
      split at hs
      · rename_i env1 body' hsub
        cases hs
        exact Or.inr ⟨body', hsub, rfl⟩
      · cases hs
  | copy _ _ =>
      dsimp [step] at hs
      split at hs
      · rename_i env1 body' hsub
        cases hs
        exact Or.inr ⟨body', hsub, rfl⟩
      · cases hs
  | mmad _ _ _ =>
      dsimp [step] at hs
      split at hs
      · rename_i env1 body' hsub
        cases hs
        exact Or.inr ⟨body', hsub, rfl⟩
      · cases hs

/-- One step of a typed command is typed, and the original result context is kept. -/
theorem preservation {here : Option Core} {env env' : Env} {Γ Γout : Ctx} {c c' : Cmd}
    (hm : models env Γ) (ht : check here Γ c = some Γout)
    (hs : step here env c = some (env', c')) :
    ∃ Γ', models env' Γ' ∧ check here Γ' c' = some Γout := by
  induction c generalizing here Γ Γout env' c' with
  | skip =>
      unfold step at hs
      cases hs
  | scope _ _ =>
      dsimp [step] at hs
      cases hs
      exact ⟨Γ, hm, ht⟩
  | assign x e =>
      unfold check checkAssign at ht
      cases e with
      | val v =>
          dsimp [step] at hs
          cases hs
          split at ht
          · rename_i τ he
            cases ht
            exact ⟨update Γ x τ, models_assign env Γ x v τ hm (infer_val_ty he), by
              unfold check; rfl⟩
          · cases ht
      | var _ =>
          dsimp [step] at hs
          split at hs
          · rename_i e0 hsub
            cases hs
            split at ht
            · rename_i τ he
              cases ht
              have he' := expr_preservation hm he hsub
              exact ⟨Γ, hm, by unfold check checkAssign; simp [he']⟩
            · cases ht
          · cases hs
      | add _ _ =>
          dsimp [step] at hs
          split at hs
          · rename_i e0 hsub
            cases hs
            split at ht
            · rename_i τ he
              cases ht
              have he' := expr_preservation hm he hsub
              exact ⟨Γ, hm, by unfold check checkAssign; simp [he']⟩
            · cases ht
          · cases hs
      | splat _ =>
          dsimp [step] at hs
          split at hs
          · rename_i e0 hsub
            cases hs
            split at ht
            · rename_i τ he
              cases ht
              have he' := expr_preservation hm he hsub
              exact ⟨Γ, hm, by unfold check checkAssign; simp [he']⟩
            · cases ht
          · cases hs
      | vadd _ _ =>
          dsimp [step] at hs
          split at hs
          · rename_i e0 hsub
            cases hs
            split at ht
            · rename_i τ he
              cases ht
              have he' := expr_preservation hm he hsub
              exact ⟨Γ, hm, by unfold check checkAssign; simp [he']⟩
            · cases ht
          · cases hs
      | vld _ =>
          dsimp [step] at hs
          split at hs
          · rename_i e0 hsub
            cases hs
            split at ht
            · rename_i τ he
              cases ht
              have he' := expr_preservation hm he hsub
              exact ⟨Γ, hm, by unfold check checkAssign; simp [he']⟩
            · cases ht
          · cases hs
  | seq c1 c2 ih1 _ =>
      unfold check at ht
      split at ht
      · rename_i Γ1 h1
        cases seq_step_inv hs with
        | inl hsk =>
            obtain ⟨rfl, rfl, rfl⟩ := hsk
            unfold check at h1
            cases h1
            exact ⟨Γ, hm, ht⟩
        | inr hstep =>
            obtain ⟨c1', hsub, rfl⟩ := hstep
            obtain ⟨Γ', hm', ht'⟩ := ih1 hm h1 hsub
            exact ⟨Γ', hm', by unfold check; simp [ht', ht]⟩
      · cases ht
  | block k _ ih =>
      unfold check at ht
      cases block_step_inv hs with
      | inl hsk =>
          obtain ⟨rfl, rfl, rfl⟩ := hsk
          unfold check at ht
          cases ht
          exact ⟨Γ, hm, by unfold check; rfl⟩
      | inr hstep =>
          obtain ⟨body', hsub, rfl⟩ := hstep
          obtain ⟨Γ', hm', ht'⟩ := ih (here := some k) hm ht hsub
          exact ⟨Γ', hm', by unfold check; simp [ht']⟩
  | vst b e =>
      unfold check checkVst at ht
      cases e with
      | val v =>
          dsimp [step] at hs
          split at hs
          · cases hs
            split at ht
            · cases ht
              rename_i hb _
              exact ⟨Γ, models_write env Γ b _ (.buf .ub) hm hb rfl, by unfold check; rfl⟩
            · cases ht
          · cases hs
      | var _ =>
          dsimp [step] at hs
          split at hs
          · rename_i e0 hsub
            cases hs
            split at ht
            · cases ht
              rename_i hb he
              have he' := expr_preservation hm he hsub
              exact ⟨Γ, hm, by unfold check checkVst; simp [hb, he']⟩
            · cases ht
          · cases hs
      | add _ _ =>
          dsimp [step] at hs
          split at hs
          · rename_i e0 hsub
            cases hs
            split at ht
            · cases ht
              rename_i hb he
              have he' := expr_preservation hm he hsub
              exact ⟨Γ, hm, by unfold check checkVst; simp [hb, he']⟩
            · cases ht
          · cases hs
      | splat _ =>
          dsimp [step] at hs
          split at hs
          · rename_i e0 hsub
            cases hs
            split at ht
            · cases ht
              rename_i hb he
              have he' := expr_preservation hm he hsub
              exact ⟨Γ, hm, by unfold check checkVst; simp [hb, he']⟩
            · cases ht
          · cases hs
      | vadd _ _ =>
          dsimp [step] at hs
          split at hs
          · rename_i e0 hsub
            cases hs
            split at ht
            · cases ht
              rename_i hb he
              have he' := expr_preservation hm he hsub
              exact ⟨Γ, hm, by unfold check checkVst; simp [hb, he']⟩
            · cases ht
          · cases hs
      | vld _ =>
          dsimp [step] at hs
          split at hs
          · rename_i e0 hsub
            cases hs
            split at ht
            · cases ht
              rename_i hb he
              have he' := expr_preservation hm he hsub
              exact ⟨Γ, hm, by unfold check checkVst; simp [hb, he']⟩
            · cases ht
          · cases hs
  | copy src dst =>
      obtain ⟨s, d, hsrc, hdst, hok, hΓ⟩ := check_copy_inv ht
      cases hΓ
      obtain ⟨vs, hvs, htys⟩ := hm src (.buf s) hsrc
      obtain ⟨vd, hvd, htyd⟩ := hm dst (.buf d) hdst
      obtain ⟨n, rfl⟩ := eq_of_valTy_buf htys
      obtain ⟨_, rfl⟩ := eq_of_valTy_buf htyd
      have hstep : step here env (.copy src dst) = some ((dst, .buf d n) :: env, .skip) := by
        unfold step
        simp [hvs, hvd, hok]
      rw [hstep] at hs
      cases hs
      exact ⟨Γ, models_write env Γ dst (.buf d n) (.buf d) hm hdst rfl, by unfold check; rfl⟩
  | mmad a b acc =>
      obtain ⟨hh, ha, hb, hc, hΓ⟩ := check_mmad_inv ht
      cases hΓ
      obtain ⟨_, hva, htya⟩ := hm a (.buf .l1) ha
      obtain ⟨_, hvb, htyb⟩ := hm b (.buf .l1) hb
      obtain ⟨_, hvc, htyc⟩ := hm acc (.buf .l0c) hc
      obtain ⟨_, rfl⟩ := eq_of_valTy_buf htya
      obtain ⟨_, rfl⟩ := eq_of_valTy_buf htyb
      obtain ⟨_, rfl⟩ := eq_of_valTy_buf htyc
      cases hh
      have hstep : step (some .cube) env (.mmad a b acc) = some (env, .skip) := by
        unfold step
        simp [hva, hvb, hvc]
      rw [hstep] at hs
      cases hs
      exact ⟨Γ, hm, by unfold check; rfl⟩

/-- Every configuration reachable from a typed command is typed at the same result context. -/
theorem type_safety {here : Option Core} {env env2 : Env} {c c2 : Cmd} {Γ Γout : Ctx}
    (hm : models env Γ) (ht : check here Γ c = some Γout)
    (hr : Steps here env c env2 c2) :
    ∃ Γ2, models env2 Γ2 ∧ check here Γ2 c2 = some Γout := by
  induction hr generalizing Γ with
  | refl _ _ => exact ⟨Γ, hm, ht⟩
  | tail _ _ _ _ _ _ hs _ ih =>
      obtain ⟨Γ1, hm1, ht1⟩ := preservation hm ht hs
      exact ih hm1 ht1

end TAS
