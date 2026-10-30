/-
Progress and preservation for the Triton language calculus.
A typed expression is a value or steps, and the successor has the same type.
A typed command is `skip` or steps, and the successor is typed at the same
result context. `type_safety` lifts that across `Steps`.
-/
import Triton.Step

set_option autoImplicit false

namespace Triton

theorem stepE_unary_arg {cfg : Cfg} {env : Env} {op : Unary} {e e' : Expr}
    (hs : stepE cfg env e = some e') :
    stepE cfg env (.unary op e) = some (.unary op e') := by
  cases e <;> first
    | (unfold stepE at hs; cases hs; done)
    | (unfold stepE; rw [hs])

theorem stepE_binary_right {cfg : Cfg} {env : Env} {op : Binary} {v : Val} {e2 e2' : Expr}
    (hs : stepE cfg env e2 = some e2') :
    stepE cfg env (.binary op (.val v) e2) = some (.binary op (.val v) e2') := by
  cases e2 <;> first
    | (unfold stepE at hs; cases hs; done)
    | (unfold stepE; rw [hs])

theorem stepE_binary_left {cfg : Cfg} {env : Env} {op : Binary} {e1 e2 e1' : Expr}
    (hs : stepE cfg env e1 = some e1') :
    stepE cfg env (.binary op e1 e2) = some (.binary op e1' e2) := by
  cases e1 <;> first
    | (unfold stepE at hs; cases hs; done)
    | (unfold stepE; rw [hs])

theorem stepE_ternary_3 {cfg : Cfg} {env : Env} {op : Ternary} {v1 v2 : Val} {e3 e3' : Expr}
    (hs : stepE cfg env e3 = some e3') :
    stepE cfg env (.ternary op (.val v1) (.val v2) e3) =
      some (.ternary op (.val v1) (.val v2) e3') := by
  cases e3 <;> first
    | (unfold stepE at hs; cases hs; done)
    | (unfold stepE; rw [hs])

theorem stepE_ternary_2 {cfg : Cfg} {env : Env} {op : Ternary} {v1 : Val} {e2 e3 e2' : Expr}
    (hs : stepE cfg env e2 = some e2') :
    stepE cfg env (.ternary op (.val v1) e2 e3) =
      some (.ternary op (.val v1) e2' e3) := by
  cases e2 <;> first
    | (unfold stepE at hs; cases hs; done)
    | (unfold stepE; rw [hs])

theorem stepE_ternary_1 {cfg : Cfg} {env : Env} {op : Ternary} {e1 e2 e3 e1' : Expr}
    (hs : stepE cfg env e1 = some e1') :
    stepE cfg env (.ternary op e1 e2 e3) = some (.ternary op e1' e2 e3) := by
  cases e1 <;> first
    | (unfold stepE at hs; cases hs; done)
    | (unfold stepE; rw [hs])

theorem unary_child {cfg : Cfg} {env : Env} {op : Unary} {e e' : Expr}
    (hs : stepE cfg env (.unary op e) = some e')
    (hnot : ∀ v, e ≠ .val v) :
    ∃ e0, stepE cfg env e = some e0 ∧ e' = .unary op e0 := by
  cases e with
  | val v => exact absurd rfl (hnot v)
  | _ =>
      dsimp [stepE] at hs
      split at hs
      · rename_i e0 hsub
        cases hs
        exact ⟨e0, hsub, rfl⟩
      · cases hs

theorem binary_right {cfg : Cfg} {env : Env} {op : Binary} {v : Val} {e2 e' : Expr}
    (hs : stepE cfg env (.binary op (.val v) e2) = some e')
    (hnot : ∀ w, e2 ≠ .val w) :
    ∃ e2', stepE cfg env e2 = some e2' ∧ e' = .binary op (.val v) e2' := by
  cases e2 with
  | val w => exact absurd rfl (hnot w)
  | _ =>
      dsimp [stepE] at hs
      split at hs
      · rename_i e2' hsub
        cases hs
        exact ⟨e2', hsub, rfl⟩
      · cases hs

theorem binary_left {cfg : Cfg} {env : Env} {op : Binary} {e1 e2 e' : Expr}
    (hs : stepE cfg env (.binary op e1 e2) = some e')
    (hnot : ∀ v, e1 ≠ .val v) :
    ∃ e1', stepE cfg env e1 = some e1' ∧ e' = .binary op e1' e2 := by
  cases e1 with
  | val v => exact absurd rfl (hnot v)
  | _ =>
      dsimp [stepE] at hs
      split at hs
      · rename_i e1' hsub
        cases hs
        exact ⟨e1', hsub, rfl⟩
      · cases hs

theorem ternary_3 {cfg : Cfg} {env : Env} {op : Ternary} {v1 v2 : Val} {e3 e' : Expr}
    (hs : stepE cfg env (.ternary op (.val v1) (.val v2) e3) = some e')
    (hnot : ∀ w, e3 ≠ .val w) :
    ∃ e3', stepE cfg env e3 = some e3' ∧ e' = .ternary op (.val v1) (.val v2) e3' := by
  cases e3 with
  | val w => exact absurd rfl (hnot w)
  | _ =>
      dsimp [stepE] at hs
      split at hs
      · rename_i e3' hsub
        cases hs
        exact ⟨e3', hsub, rfl⟩
      · cases hs

theorem ternary_2 {cfg : Cfg} {env : Env} {op : Ternary} {v1 : Val} {e2 e3 e' : Expr}
    (hs : stepE cfg env (.ternary op (.val v1) e2 e3) = some e')
    (hnot : ∀ w, e2 ≠ .val w) :
    ∃ e2', stepE cfg env e2 = some e2' ∧ e' = .ternary op (.val v1) e2' e3 := by
  cases e2 with
  | val w => exact absurd rfl (hnot w)
  | _ =>
      dsimp [stepE] at hs
      split at hs
      · rename_i e2' hsub
        cases hs
        exact ⟨e2', hsub, rfl⟩
      · cases hs

theorem ternary_1 {cfg : Cfg} {env : Env} {op : Ternary} {e1 e2 e3 e' : Expr}
    (hs : stepE cfg env (.ternary op e1 e2 e3) = some e')
    (hnot : ∀ v, e1 ≠ .val v) :
    ∃ e1', stepE cfg env e1 = some e1' ∧ e' = .ternary op e1' e2 e3 := by
  cases e1 with
  | val v => exact absurd rfl (hnot v)
  | _ =>
      dsimp [stepE] at hs
      split at hs
      · rename_i e1' hsub
        cases hs
        exact ⟨e1', hsub, rfl⟩
      · cases hs

theorem evalUnary_spec {op : Unary} {v : Val} {t : Ty}
    (h : unaryTy op (valTy v) = some t) :
    evalUnary op v = some (pack t (payload v)) := by
  unfold evalUnary
  rw [h]

theorem evalBinary_spec {op : Binary} {v1 v2 : Val} {t : Ty}
    (h : binaryTy op (valTy v1) (valTy v2) = some t) :
    evalBinary op v1 v2 = some (pack t (payload v1 + payload v2)) := by
  unfold evalBinary
  rw [h]

theorem evalTernary_spec {op : Ternary} {v1 v2 v3 : Val} {t : Ty}
    (h : ternaryTy op (valTy v1) (valTy v2) (valTy v3) = some t) :
    evalTernary op v1 v2 v3 = some (pack t (payload v1 + payload v2 + payload v3)) := by
  unfold evalTernary
  rw [h]

theorem expr_progress {cfg : Cfg} {env : Env} {Γ : Ctx}
    (hm : models env Γ) {e : Expr} {τ : Ty}
    (ht : infer Γ e = some τ) :
    (∃ v, e = .val v) ∨ ∃ e', stepE cfg env e = some e' := by
  induction e generalizing τ with
  | val v => exact Or.inl ⟨v, rfl⟩
  | var x =>
      cases hlook : lookup Γ x with
      | none => simp [infer, hlook] at ht
      | some t =>
          simp [infer, hlook] at ht
          cases ht
          obtain ⟨v, hv, _⟩ := hm x τ hlook
          exact Or.inr ⟨.val v, by unfold stepE; simp [hv]⟩
  | programId axis =>
      unfold infer at ht
      split at ht
      · rename_i hlt
        cases ht
        exact Or.inr ⟨.val (.scalar .i32 (Int.ofNat (pid cfg axis))), by
          unfold stepE; rw [if_pos hlt]⟩
      · cases ht
  | numPrograms axis =>
      unfold infer at ht
      split at ht
      · rename_i hlt
        cases ht
        exact Or.inr ⟨.val (.scalar .i32 (Int.ofNat (nprog cfg axis))), by
          unfold stepE; rw [if_pos hlt]⟩
      · cases ht
  | arange start finish =>
      unfold infer at ht
      split at ht
      · rename_i hcond
        cases ht
        exact Or.inr ⟨.val (.tensor .i32 [finish - start] 0), by
          unfold stepE; rw [if_pos hcond]⟩
      · cases ht
  | full s d n =>
      unfold infer at ht
      split at ht
      · rename_i hsz
        cases ht
        exact Or.inr ⟨.val (.tensor d s n), by unfold stepE; rw [if_pos hsz]⟩
      · cases ht
  | zeros s d =>
      unfold infer at ht
      split at ht
      · rename_i hsz
        cases ht
        exact Or.inr ⟨.val (.tensor d s 0), by unfold stepE; rw [if_pos hsz]⟩
      · cases ht
  | unary op e ih =>
      unfold infer at ht
      split at ht
      · rename_i t he
        cases ih he with
        | inl hv =>
            obtain ⟨v, rfl⟩ := hv
            simp [infer] at he
            cases he
            exact Or.inr ⟨.val (pack τ (payload v)), by
              have hev := evalUnary_spec ht
              dsimp [stepE]
              simp [hev]⟩
        | inr hs =>
            obtain ⟨e', hs⟩ := hs
            exact Or.inr ⟨.unary op e', stepE_unary_arg hs⟩
      · cases ht
  | binary op e1 e2 ih1 ih2 =>
      unfold infer at ht
      split at ht
      · rename_i t1 t2 h1 h2
        cases ih1 h1 with
        | inl hv =>
            obtain ⟨v1, rfl⟩ := hv
            simp [infer] at h1
            cases h1
            cases ih2 h2 with
            | inl hv =>
                obtain ⟨v2, rfl⟩ := hv
                simp [infer] at h2
                cases h2
                exact Or.inr ⟨.val (pack τ (payload v1 + payload v2)), by
                  have hev := evalBinary_spec ht
                  dsimp [stepE]
                  simp [hev]⟩
            | inr hs =>
                obtain ⟨e2', hs⟩ := hs
                exact Or.inr ⟨.binary op (.val v1) e2', stepE_binary_right hs⟩
        | inr hs =>
            obtain ⟨e1', hs⟩ := hs
            exact Or.inr ⟨.binary op e1' e2, stepE_binary_left hs⟩
      · cases ht
  | ternary op e1 e2 e3 ih1 ih2 ih3 =>
      unfold infer at ht
      split at ht
      · rename_i t1 t2 t3 h1 h2 h3
        cases ih1 h1 with
        | inl hv =>
            obtain ⟨v1, rfl⟩ := hv
            simp [infer] at h1
            cases h1
            cases ih2 h2 with
            | inl hv =>
                obtain ⟨v2, rfl⟩ := hv
                simp [infer] at h2
                cases h2
                cases ih3 h3 with
                | inl hv =>
                    obtain ⟨v3, rfl⟩ := hv
                    simp [infer] at h3
                    cases h3
                    exact Or.inr ⟨.val (pack τ (payload v1 + payload v2 + payload v3)), by
                      have hev := evalTernary_spec ht
                      dsimp [stepE]
                      simp [hev]⟩
                | inr hs =>
                    obtain ⟨e3', hs⟩ := hs
                    exact Or.inr ⟨.ternary op (.val v1) (.val v2) e3', stepE_ternary_3 hs⟩
            | inr hs =>
                obtain ⟨e2', hs⟩ := hs
                exact Or.inr ⟨.ternary op (.val v1) e2' e3, stepE_ternary_2 hs⟩
        | inr hs =>
            obtain ⟨e1', hs⟩ := hs
            exact Or.inr ⟨.ternary op e1' e2 e3, stepE_ternary_1 hs⟩
      · cases ht

theorem expr_preservation {cfg : Cfg} {env : Env} {Γ : Ctx} {e e' : Expr} {τ : Ty}
    (hm : models env Γ) (ht : infer Γ e = some τ) (hs : stepE cfg env e = some e') :
    infer Γ e' = some τ := by
  induction e generalizing e' τ with
  | val _ =>
      unfold stepE at hs
      cases hs
  | var x =>
      unfold stepE at hs
      split at hs
      · rename_i v hv
        cases hs
        cases hlook : lookup Γ x with
        | none => simp [infer, hlook] at ht
        | some t =>
            simp [infer, hlook] at ht
            cases ht
            obtain ⟨v', hv', hty⟩ := hm x τ hlook
            rw [hv] at hv'
            cases hv'
            simp [infer, hty]
      · cases hs
  | programId axis =>
      unfold infer at ht
      split at ht
      · rename_i hlt
        cases ht
        unfold stepE at hs
        rw [if_pos hlt] at hs
        cases hs
        simp [infer, valTy]
      · cases ht
  | numPrograms axis =>
      unfold infer at ht
      split at ht
      · rename_i hlt
        cases ht
        unfold stepE at hs
        rw [if_pos hlt] at hs
        cases hs
        simp [infer, valTy]
      · cases ht
  | arange start finish =>
      unfold infer at ht
      split at ht
      · rename_i hcond
        cases ht
        unfold stepE at hs
        rw [if_pos hcond] at hs
        cases hs
        simp [infer, valTy]
      · cases ht
  | full s d n =>
      unfold infer at ht
      split at ht
      · rename_i hsz
        cases ht
        unfold stepE at hs
        rw [if_pos hsz] at hs
        cases hs
        simp [infer, valTy]
      · cases ht
  | zeros s d =>
      unfold infer at ht
      split at ht
      · rename_i hsz
        cases ht
        unfold stepE at hs
        rw [if_pos hsz] at hs
        cases hs
        simp [infer, valTy]
      · cases ht
  | unary op e ih =>
      unfold infer at ht
      split at ht
      · rename_i t he
        cases e with
        | val v =>
            simp [infer] at he
            cases he
            have hev := evalUnary_spec ht
            dsimp [stepE] at hs
            simp [hev] at hs
            cases hs
            simp [infer, valTy_pack]
        | _ =>
            obtain ⟨e0, hsub, rfl⟩ := unary_child hs (by intro v h; cases h)
            have h' := ih he hsub
            unfold infer
            simp [h']
            exact ht
      · cases ht
  | binary op e1 e2 ih1 ih2 =>
      unfold infer at ht
      split at ht
      · rename_i t1 t2 h1 h2
        cases e1 with
        | val v1 =>
            simp [infer] at h1
            cases h1
            cases e2 with
            | val v2 =>
                simp [infer] at h2
                cases h2
                have hev := evalBinary_spec ht
                dsimp [stepE] at hs
                simp [hev] at hs
                cases hs
                simp [infer, valTy_pack]
            | _ =>
                obtain ⟨e2', hsub, rfl⟩ := binary_right hs (by intro v h; cases h)
                have h2' := ih2 h2 hsub
                unfold infer
                simp [infer, h2']
                exact ht
        | _ =>
            obtain ⟨e1', hsub, rfl⟩ := binary_left hs (by intro v h; cases h)
            have h1' := ih1 h1 hsub
            unfold infer
            simp [h1', h2]
            exact ht
      · cases ht
  | ternary op e1 e2 e3 ih1 ih2 ih3 =>
      unfold infer at ht
      split at ht
      · rename_i t1 t2 t3 h1 h2 h3
        cases e1 with
        | val v1 =>
            simp [infer] at h1
            cases h1
            cases e2 with
            | val v2 =>
                simp [infer] at h2
                cases h2
                cases e3 with
                | val v3 =>
                    simp [infer] at h3
                    cases h3
                    have hev := evalTernary_spec ht
                    dsimp [stepE] at hs
                    simp [hev] at hs
                    cases hs
                    simp [infer, valTy_pack]
                | _ =>
                    obtain ⟨e3', hsub, rfl⟩ := ternary_3 hs (by intro v h; cases h)
                    have h3' := ih3 h3 hsub
                    unfold infer
                    simp [infer, h3']
                    exact ht
            | _ =>
                obtain ⟨e2', hsub, rfl⟩ := ternary_2 hs (by intro v h; cases h)
                have h2' := ih2 h2 hsub
                unfold infer
                simp [infer, h2', h3]
                exact ht
        | _ =>
            obtain ⟨e1', hsub, rfl⟩ := ternary_1 hs (by intro v h; cases h)
            have h1' := ih1 h1 hsub
            unfold infer
            simp [h1', h2, h3]
            exact ht
      · cases ht

theorem step_assign_expr {cfg : Cfg} {env : Env} {x : Nat} {e e' : Expr}
    (hs : stepE cfg env e = some e') :
    step cfg env (.assign x e) = some (env, .assign x e') := by
  cases e <;> first
    | (unfold stepE at hs; cases hs; done)
    | (unfold step; rw [hs])

theorem step_seq_cmd {cfg : Cfg} {env env' : Env} {c1 c2 c1' : Cmd}
    (hs : step cfg env c1 = some (env', c1')) :
    step cfg env (.seq c1 c2) = some (env', .seq c1' c2) := by
  cases c1 <;> first
    | (unfold step at hs; cases hs; done)
    | (unfold step; rw [hs])

theorem step_block_cmd {cfg : Cfg} {env env' : Env} {body body' : Cmd}
    (hs : step cfg env body = some (env', body')) :
    step cfg env (.block body) = some (env', .block body') := by
  cases body <;> first
    | (unfold step at hs; cases hs; done)
    | (unfold step; rw [hs])

theorem step_branch_cond {cfg : Cfg} {env : Env} {cond cond' : Expr} {c1 c2 : Cmd}
    (hs : stepE cfg env cond = some cond') :
    step cfg env (.branch cond c1 c2) = some (env, .branch cond' c1 c2) := by
  cases cond <;> first
    | (unfold stepE at hs; cases hs; done)
    | (unfold step; rw [hs])

theorem step_store_right {cfg : Cfg} {env : Env} {vp : Val} {v v' : Expr}
    (hs : stepE cfg env v = some v') :
    step cfg env (.store (.val vp) v) = some (env, .store (.val vp) v') := by
  cases v <;> first
    | (unfold stepE at hs; cases hs; done)
    | (unfold step; rw [hs])

theorem step_store_left {cfg : Cfg} {env : Env} {p v p' : Expr}
    (hs : stepE cfg env p = some p') :
    step cfg env (.store p v) = some (env, .store p' v) := by
  cases p <;> first
    | (unfold stepE at hs; cases hs; done)
    | (unfold step; rw [hs])

theorem seq_step_inv {cfg : Cfg} {env env' : Env} {c1 c2 c' : Cmd}
    (hs : step cfg env (.seq c1 c2) = some (env', c')) :
    (c1 = .skip ∧ env' = env ∧ c' = c2) ∨
      ∃ c1', step cfg env c1 = some (env', c1') ∧ c' = .seq c1' c2 := by
  cases c1 with
  | skip =>
      dsimp [step] at hs
      cases hs
      exact Or.inl ⟨rfl, rfl, rfl⟩
  | loop n body =>
      cases n with
      | zero =>
          dsimp [step] at hs
          cases hs
          exact Or.inr ⟨.skip, by unfold step; rfl, rfl⟩
      | succ n' =>
          dsimp [step] at hs
          cases hs
          exact Or.inr ⟨.seq body (.loop n' body), by unfold step; rfl, rfl⟩
  | barrier =>
      dsimp [step] at hs
      cases hs
      exact Or.inr ⟨.skip, by unfold step; rfl, rfl⟩
  | _ =>
      dsimp [step] at hs
      split at hs
      · rename_i c1' hsub
        cases hs
        exact Or.inr ⟨c1', hsub, rfl⟩
      · cases hs

theorem block_step_inv {cfg : Cfg} {env env' : Env} {body c' : Cmd}
    (hs : step cfg env (.block body) = some (env', c')) :
    (body = .skip ∧ env' = env ∧ c' = .skip) ∨
      ∃ body', step cfg env body = some (env', body') ∧ c' = .block body' := by
  cases body with
  | skip =>
      dsimp [step] at hs
      cases hs
      exact Or.inl ⟨rfl, rfl, rfl⟩
  | loop n body =>
      cases n with
      | zero =>
          dsimp [step] at hs
          cases hs
          exact Or.inr ⟨.skip, by unfold step; rfl, rfl⟩
      | succ n' =>
          dsimp [step] at hs
          cases hs
          exact Or.inr ⟨.seq body (.loop n' body), by unfold step; rfl, rfl⟩
  | barrier =>
      dsimp [step] at hs
      cases hs
      exact Or.inr ⟨.skip, by unfold step; rfl, rfl⟩
  | _ =>
      dsimp [step] at hs
      split at hs
      · rename_i body' hsub
        cases hs
        exact Or.inr ⟨body', hsub, rfl⟩
      · cases hs

theorem branch_child {cfg : Cfg} {env env' : Env} {cond : Expr} {c1 c2 c' : Cmd}
    (hs : step cfg env (.branch cond c1 c2) = some (env', c'))
    (hnot : ∀ v, cond ≠ .val v) :
    ∃ cond', stepE cfg env cond = some cond' ∧ env' = env ∧ c' = .branch cond' c1 c2 := by
  cases cond with
  | val v => exact absurd rfl (hnot v)
  | _ =>
      dsimp [step] at hs
      split at hs
      · rename_i cond' hsub
        cases hs
        exact ⟨cond', hsub, rfl, rfl⟩
      · cases hs

theorem assert_child {cfg : Cfg} {env env' : Env} {wrap : Expr → Cmd} {c : Expr} {c' : Cmd}
    (hs : step.stepAssert cfg env wrap c = some (env', c'))
    (hnot : ∀ v, c ≠ .val v) :
    ∃ c0, stepE cfg env c = some c0 ∧ env' = env ∧ c' = wrap c0 := by
  cases c with
  | val v => exact absurd rfl (hnot v)
  | _ =>
      dsimp [step.stepAssert] at hs
      split at hs
      · rename_i c0 hsub
        cases hs
        exact ⟨c0, hsub, rfl, rfl⟩
      · cases hs

theorem print_child {cfg : Cfg} {env env' : Env} {wrap : Expr → Cmd} {e : Expr} {c' : Cmd}
    (hs : step.stepPrint cfg env wrap e = some (env', c'))
    (hnot : ∀ v, e ≠ .val v) :
    ∃ e0, stepE cfg env e = some e0 ∧ env' = env ∧ c' = wrap e0 := by
  cases e with
  | val v => exact absurd rfl (hnot v)
  | _ =>
      dsimp [step.stepPrint] at hs
      split at hs
      · rename_i e0 hsub
        cases hs
        exact ⟨e0, hsub, rfl, rfl⟩
      · cases hs

theorem progress {cfg : Cfg} {env : Env} {Γ Γout : Ctx} {c : Cmd}
    (hm : models env Γ) (ht : check Γ c = some Γout) :
    c = .skip ∨ ∃ env' c', step cfg env c = some (env', c') := by
  induction c generalizing Γ Γout with
  | skip => exact Or.inl rfl
  | assign x e =>
      unfold check at ht
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
  | seq c1 c2 ih _ =>
      unfold check at ht
      split at ht
      · rename_i Γ1 h1
        cases ih hm h1 with
        | inl hsk =>
            cases hsk
            exact Or.inr ⟨env, c2, by unfold step; rfl⟩
        | inr hs =>
            obtain ⟨env', c1', hs⟩ := hs
            exact Or.inr ⟨env', .seq c1' c2, step_seq_cmd hs⟩
      · cases ht
  | block body ih =>
      have ht' : check Γ body = some Γout := by
        unfold check at ht
        exact ht
      cases ih hm ht' with
      | inl hsk =>
          cases hsk
          exact Or.inr ⟨env, .skip, by unfold step; rfl⟩
      | inr hs =>
          obtain ⟨env', body', hs⟩ := hs
          exact Or.inr ⟨env', .block body', step_block_cmd hs⟩
  | branch cond c1 c2 _ _ =>
      unfold check at ht
      split at ht
      · rename_i Γ1 Γ2 hcond _ _
        split at ht
        · cases ht
          cases expr_progress hm hcond with
          | inl hv =>
              obtain ⟨v, rfl⟩ := hv
              simp [infer] at hcond
              cases v with
              | scalar d n =>
                  cases d with
                  | bool =>
                      exact Or.inr ⟨env, if n = 0 then c2 else c1, by
                        unfold step
                        unfold stepBool
                        by_cases hn : n = 0 <;> simp [hn]⟩
                  | _ => simp [valTy] at hcond
              | _ => simp [valTy] at hcond
          | inr hs =>
              obtain ⟨e', hs⟩ := hs
              exact Or.inr ⟨env, .branch e' c1 c2, step_branch_cond hs⟩
        · cases ht
      · cases ht
  | loop n body _ =>
      unfold check at ht
      split at ht
      · rename_i Γ' hb
        split at ht
        · rename_i heq
          cases ht
          cases n with
          | zero => exact Or.inr ⟨env, .skip, by unfold step; rfl⟩
          | succ n' => exact Or.inr ⟨env, .seq body (.loop n' body), by unfold step; rfl⟩
        · cases ht
      · cases ht
  | store p v =>
      unfold check at ht
      split at ht
      · rename_i tp tv hp hv
        split at ht
        · rename_i hok
          cases ht
          cases expr_progress hm hp with
          | inl hvp =>
              obtain ⟨vp, rfl⟩ := hvp
              cases expr_progress hm hv with
              | inl hvv =>
                  obtain ⟨vv, rfl⟩ := hvv
                  simp [infer] at hp hv
                  cases hp
                  cases hv
                  exact Or.inr ⟨env, .skip, by dsimp [step]; simp [hok]⟩
              | inr hs =>
                  obtain ⟨v', hs⟩ := hs
                  exact Or.inr ⟨env, .store (.val vp) v', step_store_right hs⟩
          | inr hs =>
              obtain ⟨p', hs⟩ := hs
              exact Or.inr ⟨env, .store p' v, step_store_left hs⟩
        · cases ht
      · cases ht
  | storeMask p v m =>
      unfold check at ht
      split at ht <;> try cases ht
      rename_i tp tv tm hp hv htm
      split at ht <;> try cases ht
      rename_i r hok hr
      split at ht
      · rename_i hmask
        cases ht
        cases expr_progress hm hp with
        | inl hvp =>
            obtain ⟨vp, rfl⟩ := hvp
            cases expr_progress hm hv with
            | inl hvv =>
                obtain ⟨vv, rfl⟩ := hvv
                cases expr_progress hm htm with
                | inl hvm =>
                    obtain ⟨vm, rfl⟩ := hvm
                    simp [infer] at hp hv htm
                    cases hp; cases hv; cases htm
                    exact Or.inr ⟨env, .skip, by
                      dsimp [step]
                      simp [hok, hr, hmask]⟩
                | inr hs =>
                    obtain ⟨m', hs⟩ := hs
                    exact Or.inr ⟨env, .storeMask (.val vp) (.val vv) m', by
                      cases m <;> first
                        | (unfold stepE at hs; cases hs; done)
                        | (unfold step; rw [hs])⟩
            | inr hs =>
                obtain ⟨v', hs⟩ := hs
                exact Or.inr ⟨env, .storeMask (.val vp) v' m, by
                  cases v <;> first
                    | (unfold stepE at hs; cases hs; done)
                    | (unfold step; rw [hs])⟩
        | inr hs =>
            obtain ⟨p', hs⟩ := hs
            exact Or.inr ⟨env, .storeMask p' v m, by
              cases p <;> first
                | (unfold stepE at hs; cases hs; done)
                | (unfold step; rw [hs])⟩
      · cases ht
  | storeTDesc d offs val =>
      unfold check at ht
      split at ht <;> try cases ht
      rename_i b s tv hd ho hv
      split at ht <;> try cases ht
      rename_i hlen
      split at ht
      · rename_i hok
        cases ht
        cases expr_progress hm hd with
        | inl hvd =>
            obtain ⟨vd, rfl⟩ := hvd
            cases expr_progress hm ho with
            | inl hvo =>
                obtain ⟨vo, rfl⟩ := hvo
                cases expr_progress hm hv with
                | inl hvv =>
                    obtain ⟨vv, rfl⟩ := hvv
                    simp [infer] at hd ho hv
                    exact Or.inr ⟨env, .skip, by
                      dsimp [step]
                      simp [hd, ho, hv, hok, hlen]⟩
                | inr hs =>
                    obtain ⟨val', hs⟩ := hs
                    exact Or.inr ⟨env, .storeTDesc (.val vd) (.val vo) val', by
                      cases val <;> first
                        | (unfold stepE at hs; cases hs; done)
                        | (unfold step; rw [hs])⟩
            | inr hs =>
                obtain ⟨offs', hs⟩ := hs
                exact Or.inr ⟨env, .storeTDesc (.val vd) offs' val, by
                  cases offs <;> first
                    | (unfold stepE at hs; cases hs; done)
                    | (unfold step; rw [hs])⟩
        | inr hs =>
            obtain ⟨d', hs⟩ := hs
            exact Or.inr ⟨env, .storeTDesc d' offs val, by
              cases d <;> first
                | (unfold stepE at hs; cases hs; done)
                | (unfold step; rw [hs])⟩
      · cases ht
  | atomic x op p v =>
      unfold check at ht
      split at ht <;> try cases ht
      rename_i tp tv hp hv
      split at ht
      · rename_i tr hok htr
        cases ht
        cases expr_progress hm hp with
        | inl hvp =>
            obtain ⟨vp, rfl⟩ := hvp
            cases expr_progress hm hv with
            | inl hvv =>
                obtain ⟨vv, rfl⟩ := hvv
                simp [infer] at hp hv
                cases hp; cases hv
                exact Or.inr ⟨(x, pack tr (payload vp)) :: env, .skip, by
                  dsimp [step]; simp [hok, htr]⟩
            | inr hs =>
                obtain ⟨v', hs⟩ := hs
                exact Or.inr ⟨env, .atomic x op (.val vp) v', by
                  cases v <;> first
                    | (unfold stepE at hs; cases hs; done)
                    | (unfold step; rw [hs])⟩
        | inr hs =>
            obtain ⟨p', hs⟩ := hs
            exact Or.inr ⟨env, .atomic x op p' v, by
              cases p <;> first
                | (unfold stepE at hs; cases hs; done)
                | (unfold step; rw [hs])⟩
      · cases ht
  | cas x p cmp val =>
      unfold check at ht
      split at ht <;> try cases ht
      rename_i tp tc tv hp hc hv
      split at ht <;> try cases ht
      rename_i tr htr
      split at ht
      · rename_i heq
        cases ht
        cases expr_progress hm hp with
        | inl hvp =>
            obtain ⟨vp, rfl⟩ := hvp
            cases expr_progress hm hc with
            | inl hvc =>
                obtain ⟨vc, rfl⟩ := hvc
                cases expr_progress hm hv with
                | inl hvv =>
                    obtain ⟨vv, rfl⟩ := hvv
                    simp [infer] at hp hc hv
                    cases hp; cases hc; cases hv
                    exact Or.inr ⟨(x, pack tr (payload vc)) :: env, .skip, by
                      dsimp [step]; simp [htr, heq]⟩
                | inr hs =>
                    obtain ⟨val', hs⟩ := hs
                    exact Or.inr ⟨env, .cas x (.val vp) (.val vc) val', by
                      cases val <;> first
                        | (unfold stepE at hs; cases hs; done)
                        | (unfold step; rw [hs])⟩
            | inr hs =>
                obtain ⟨cmp', hs⟩ := hs
                exact Or.inr ⟨env, .cas x (.val vp) cmp' val, by
                  cases cmp <;> first
                    | (unfold stepE at hs; cases hs; done)
                    | (unfold step; rw [hs])⟩
        | inr hs =>
            obtain ⟨p', hs⟩ := hs
            exact Or.inr ⟨env, .cas x p' cmp val, by
              cases p <;> first
                | (unfold stepE at hs; cases hs; done)
                | (unfold step; rw [hs])⟩
      · cases ht
  | barrier =>
      exact Or.inr ⟨env, .skip, by unfold step; rfl⟩
  | deviceAssert c =>
      unfold check at ht
      split at ht <;> try cases ht
      rename_i hcond
      cases expr_progress hm hcond with
      | inl hv =>
          obtain ⟨v, rfl⟩ := hv
          simp [infer] at hcond
          cases v with
          | scalar d n =>
              cases d with
              | bool => exact Or.inr ⟨env, .skip, by unfold step; unfold step.stepAssert; rfl⟩
              | _ => simp [valTy] at hcond
          | _ => simp [valTy] at hcond
      | inr hs =>
          obtain ⟨c', hs⟩ := hs
          exact Or.inr ⟨env, .deviceAssert c', by
            cases c <;> first
              | (unfold stepE at hs; cases hs; done)
              | (unfold step; unfold step.stepAssert; rw [hs])⟩
  | staticAssert c =>
      unfold check at ht
      split at ht <;> try cases ht
      rename_i hcond
      cases expr_progress hm hcond with
      | inl hv =>
          obtain ⟨v, rfl⟩ := hv
          simp [infer] at hcond
          cases v with
          | scalar d n =>
              cases d with
              | bool => exact Or.inr ⟨env, .skip, by unfold step; unfold step.stepAssert; rfl⟩
              | _ => simp [valTy] at hcond
          | _ => simp [valTy] at hcond
      | inr hs =>
          obtain ⟨c', hs⟩ := hs
          exact Or.inr ⟨env, .staticAssert c', by
            cases c <;> first
              | (unfold stepE at hs; cases hs; done)
              | (unfold step; unfold step.stepAssert; rw [hs])⟩
  | assume c =>
      unfold check at ht
      split at ht <;> try cases ht
      rename_i hcond
      cases expr_progress hm hcond with
      | inl hv =>
          obtain ⟨v, rfl⟩ := hv
          simp [infer] at hcond
          cases v with
          | scalar d n =>
              cases d with
              | bool => exact Or.inr ⟨env, .skip, by unfold step; unfold step.stepAssert; rfl⟩
              | _ => simp [valTy] at hcond
          | _ => simp [valTy] at hcond
      | inr hs =>
          obtain ⟨c', hs⟩ := hs
          exact Or.inr ⟨env, .assume c', by
            cases c <;> first
              | (unfold stepE at hs; cases hs; done)
              | (unfold step; unfold step.stepAssert; rw [hs])⟩
  | devicePrint e =>
      unfold check at ht
      split at ht <;> try cases ht
      rename_i _ he
      cases expr_progress hm he with
      | inl hv =>
          obtain ⟨v, rfl⟩ := hv
          exact Or.inr ⟨env, .skip, by unfold step; unfold step.stepPrint; rfl⟩
      | inr hs =>
          obtain ⟨e', hs⟩ := hs
          exact Or.inr ⟨env, .devicePrint e', by
            cases e <;> first
              | (unfold stepE at hs; cases hs; done)
              | (unfold step; unfold step.stepPrint; rw [hs])⟩
  | staticPrint e =>
      unfold check at ht
      split at ht <;> try cases ht
      rename_i _ he
      cases expr_progress hm he with
      | inl hv =>
          obtain ⟨v, rfl⟩ := hv
          exact Or.inr ⟨env, .skip, by unfold step; unfold step.stepPrint; rfl⟩
      | inr hs =>
          obtain ⟨e', hs⟩ := hs
          exact Or.inr ⟨env, .staticPrint e', by
            cases e <;> first
              | (unfold stepE at hs; cases hs; done)
              | (unfold step; unfold step.stepPrint; rw [hs])⟩

theorem preservation {cfg : Cfg} {env env' : Env} {Γ Γout : Ctx} {c c' : Cmd}
    (hm : models env Γ) (ht : check Γ c = some Γout)
    (hs : step cfg env c = some (env', c')) :
    ∃ Γ', models env' Γ' ∧ check Γ' c' = some Γout := by
  induction c generalizing Γ Γout env' c' with
  | skip =>
      unfold step at hs
      cases hs
  | assign x e =>
      unfold check at ht
      split at ht
      · rename_i τ he
        cases ht
        cases e with
        | val v =>
            dsimp [step] at hs
            cases hs
            exact ⟨update Γ x τ,
              models_assign env Γ x v τ hm (by simp [infer] at he; exact he),
              by unfold check; rfl⟩
        | _ =>
            dsimp [step] at hs
            split at hs
            · rename_i e0 hsub
              cases hs
              have he' := expr_preservation hm he hsub
              exact ⟨Γ, hm, by unfold check; simp [he']⟩
            · cases hs
      · cases ht
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
  | block body ih =>
      have ht' : check Γ body = some Γout := by
        unfold check at ht
        exact ht
      cases block_step_inv hs with
      | inl hsk =>
          obtain ⟨rfl, rfl, rfl⟩ := hsk
          unfold check at ht'
          cases ht'
          exact ⟨Γ, hm, by unfold check; rfl⟩
      | inr hstep =>
          obtain ⟨body', hsub, rfl⟩ := hstep
          obtain ⟨Γ', hm', hbody⟩ := ih hm ht' hsub
          exact ⟨Γ', hm', by unfold check; exact hbody⟩
  | branch cond c1 c2 _ _ =>
      unfold check at ht
      split at ht
      · rename_i Γ1 Γ2 hcond hc1 hc2
        split at ht
        · rename_i heq
          cases ht
          cases cond with
          | val v =>
              simp [infer] at hcond
              cases v with
              | scalar d n =>
                  cases d with
                  | bool =>
                      by_cases hn : n = 0
                      · have hstep :
                            step cfg env (.branch (.val (.scalar .bool n)) c1 c2) =
                              some (env, c2) := by
                          unfold step; unfold stepBool; simp [hn]
                        rw [hstep] at hs
                        cases hs
                        exact ⟨Γ, hm, by simpa [heq] using hc2⟩
                      · have hstep :
                            step cfg env (.branch (.val (.scalar .bool n)) c1 c2) =
                              some (env, c1) := by
                          unfold step; unfold stepBool; simp [hn]
                        rw [hstep] at hs
                        cases hs
                        exact ⟨Γ, hm, hc1⟩
                  | _ => simp [valTy] at hcond
              | _ => simp [valTy] at hcond
          | _ =>
              obtain ⟨cond', hsub, rfl, rfl⟩ := branch_child hs (by intro v h; cases h)
              have h' := expr_preservation hm hcond hsub
              exact ⟨Γ, hm, by unfold check; simp [h', hc1, hc2, heq]⟩
        · cases ht
      · cases ht
  | loop n body _ =>
      unfold check at ht
      split at ht
      · rename_i Γ' hb
        split at ht
        · rename_i heq
          cases ht
          cases heq
          cases n with
          | zero =>
              dsimp [step] at hs
              cases hs
              exact ⟨Γ, hm, by unfold check; rfl⟩
          | succ n' =>
              dsimp [step] at hs
              cases hs
              have hloop : check Γ (.loop n' body) = some Γ := by
                unfold check
                rw [hb]
                simp
              refine ⟨Γ, hm, ?_⟩
              unfold check
              rw [hb]
              exact hloop
        · cases ht
      · cases ht
  | store p v =>
      unfold check at ht
      split at ht
      · rename_i tp tv hp hv
        split at ht
        · rename_i hok
          cases ht
          cases p with
          | val vp =>
              simp [infer] at hp
              cases v with
              | val vv =>
                  simp [infer] at hv
                  have hstep : step cfg env (.store (.val vp) (.val vv)) = some (env, .skip) := by
                    dsimp [step]
                    simp [hp, hv, hok]
                  rw [hstep] at hs
                  cases hs
                  exact ⟨Γ, hm, by unfold check; rfl⟩
              | _ =>
                  dsimp [step] at hs
                  split at hs
                  · rename_i v' hsub
                    cases hs
                    have hv' := expr_preservation hm hv hsub
                    exact ⟨Γ, hm, by unfold check; simp [infer, hp, hv', hok]⟩
                  · cases hs
          | _ =>
              dsimp [step] at hs
              split at hs
              · rename_i p' hsub
                cases hs
                have hp' := expr_preservation hm hp hsub
                exact ⟨Γ, hm, by unfold check; simp [hp', hv, hok]⟩
              · cases hs
        · cases ht
      · cases ht
  | storeMask p v m =>
      unfold check at ht
      split at ht <;> try cases ht
      rename_i tp tv tm hp hv htm
      split at ht <;> try cases ht
      rename_i r hok hr
      split at ht
      · rename_i hmask
        cases ht
        cases p with
        | val vp =>
            simp [infer] at hp
            cases v with
            | val vv =>
                simp [infer] at hv
                cases m with
                | val vm =>
                    simp [infer] at htm
                    have hstep :
                        step cfg env (.storeMask (.val vp) (.val vv) (.val vm)) = some (env, .skip) := by
                      dsimp [step]
                      simp [hp, hv, htm, hok, hr, hmask]
                    rw [hstep] at hs
                    cases hs
                    exact ⟨Γ, hm, by unfold check; rfl⟩
                | _ =>
                    dsimp [step] at hs
                    split at hs
                    · rename_i m' hsub
                      cases hs
                      have hm' := expr_preservation hm htm hsub
                      exact ⟨Γ, hm, by unfold check; simp [infer, hp, hv, hm', hok, hr, hmask]⟩
                    · cases hs
            | _ =>
                dsimp [step] at hs
                split at hs
                · rename_i v' hsub
                  cases hs
                  have hv' := expr_preservation hm hv hsub
                  exact ⟨Γ, hm, by unfold check; simp [infer, hp, hv', htm, hok, hr, hmask]⟩
                · cases hs
        | _ =>
            dsimp [step] at hs
            split at hs
            · rename_i p' hsub
              cases hs
              have hp' := expr_preservation hm hp hsub
              exact ⟨Γ, hm, by unfold check; simp [hp', hv, htm, hok, hr, hmask]⟩
            · cases hs
      · cases ht
  | storeTDesc d offs val =>
      unfold check at ht
      split at ht <;> try cases ht
      rename_i b s tv hd ho hv
      split at ht <;> try cases ht
      rename_i hlen
      split at ht
      · rename_i hok
        cases ht
        cases d with
        | val vd =>
            simp [infer] at hd
            cases offs with
            | val vo =>
                simp [infer] at ho
                cases val with
                | val vv =>
                    simp [infer] at hv
                    have hstep :
                        step cfg env (.storeTDesc (.val vd) (.val vo) (.val vv)) = some (env, .skip) := by
                      dsimp [step]
                      simp [hd, ho, hv, hok, hlen]
                    rw [hstep] at hs
                    cases hs
                    exact ⟨Γ, hm, by unfold check; rfl⟩
                | _ =>
                    dsimp [step] at hs
                    split at hs
                    · rename_i val' hsub
                      cases hs
                      have hv' := expr_preservation hm hv hsub
                      exact ⟨Γ, hm, by unfold check; simp [infer, hd, ho, hv', hlen, hok]⟩
                    · cases hs
            | _ =>
                dsimp [step] at hs
                split at hs
                · rename_i offs' hsub
                  cases hs
                  have ho' := expr_preservation hm ho hsub
                  exact ⟨Γ, hm, by unfold check; simp [infer, hd, ho', hv, hlen, hok]⟩
                · cases hs
        | _ =>
            dsimp [step] at hs
            split at hs
            · rename_i d' hsub
              cases hs
              have hd' := expr_preservation hm hd hsub
              exact ⟨Γ, hm, by unfold check; simp [infer, hd', ho, hv, hlen, hok]⟩
            · cases hs
      · cases ht
  | atomic x op p v =>
      unfold check at ht
      split at ht <;> try cases ht
      rename_i tp tv hp hv
      split at ht
      · rename_i tr hok htr
        cases ht
        cases p with
        | val vp =>
            simp [infer] at hp
            cases v with
            | val vv =>
                simp [infer] at hv
                have hstep :
                    step cfg env (.atomic x op (.val vp) (.val vv)) =
                      some ((x, pack tr (payload vp)) :: env, .skip) := by
                  dsimp [step]
                  simp [hp, hv, hok, htr]
                rw [hstep] at hs
                cases hs
                exact ⟨update Γ x tr,
                  models_assign env Γ x (pack tr (payload vp)) tr hm (valTy_pack _ _),
                  by unfold check; rfl⟩
            | _ =>
                dsimp [step] at hs
                split at hs
                · rename_i v' hsub
                  cases hs
                  have hv' := expr_preservation hm hv hsub
                  exact ⟨Γ, hm, by unfold check; simp [infer, hp, hv', hok, htr]⟩
                · cases hs
        | _ =>
            dsimp [step] at hs
            split at hs
            · rename_i p' hsub
              cases hs
              have hp' := expr_preservation hm hp hsub
              exact ⟨Γ, hm, by unfold check; simp [hp', hv, hok, htr]⟩
            · cases hs
      · cases ht
  | cas x p cmp val =>
      unfold check at ht
      split at ht <;> try cases ht
      rename_i tp tc tv hp hc hv
      split at ht <;> try cases ht
      rename_i tr htr
      split at ht
      · rename_i heq
        cases ht
        cases p with
        | val vp =>
            simp [infer] at hp
            cases cmp with
            | val vc =>
                simp [infer] at hc
                cases val with
                | val vv =>
                    simp [infer] at hv
                    have hstep :
                        step cfg env (.cas x (.val vp) (.val vc) (.val vv)) =
                          some ((x, pack tr (payload vc)) :: env, .skip) := by
                      dsimp [step]
                      simp [hp, hc, hv, htr, heq]
                    rw [hstep] at hs
                    cases hs
                    exact ⟨update Γ x tr,
                      models_assign env Γ x (pack tr (payload vc)) tr hm (valTy_pack _ _),
                      by unfold check; rfl⟩
                | _ =>
                    dsimp [step] at hs
                    split at hs
                    · rename_i val' hsub
                      cases hs
                      have hv' := expr_preservation hm hv hsub
                      exact ⟨Γ, hm, by unfold check; simp [infer, hp, hc, hv', htr, heq]⟩
                    · cases hs
            | _ =>
                dsimp [step] at hs
                split at hs
                · rename_i cmp' hsub
                  cases hs
                  have hc' := expr_preservation hm hc hsub
                  exact ⟨Γ, hm, by unfold check; simp [infer, hp, hc', hv, htr, heq]⟩
                · cases hs
        | _ =>
            dsimp [step] at hs
            split at hs
            · rename_i p' hsub
              cases hs
              have hp' := expr_preservation hm hp hsub
              exact ⟨Γ, hm, by unfold check; simp [hp', hc, hv, htr, heq]⟩
            · cases hs
      · cases ht
  | barrier =>
      unfold check at ht
      cases ht
      dsimp [step] at hs
      cases hs
      exact ⟨Γ, hm, by unfold check; rfl⟩
  | deviceAssert e =>
      unfold check at ht
      split at ht <;> try cases ht
      rename_i hcond
      cases e with
      | val v =>
          simp [infer] at hcond
          cases v with
          | scalar d n =>
              cases d with
              | bool =>
                  have hstep :
                      step cfg env (.deviceAssert (.val (.scalar .bool n))) = some (env, .skip) := by
                    unfold step; unfold step.stepAssert; rfl
                  rw [hstep] at hs
                  cases hs
                  exact ⟨Γ, hm, by unfold check; rfl⟩
              | _ => simp [valTy] at hcond
          | _ => simp [valTy] at hcond
      | _ =>
          dsimp [step] at hs
          obtain ⟨e0, hsub, rfl, rfl⟩ := assert_child hs (by intro v h; cases h)
          have h' := expr_preservation hm hcond hsub
          exact ⟨Γ, hm, by unfold check; simp [h']⟩
  | staticAssert e =>
      unfold check at ht
      split at ht <;> try cases ht
      rename_i hcond
      cases e with
      | val v =>
          simp [infer] at hcond
          cases v with
          | scalar d n =>
              cases d with
              | bool =>
                  have hstep :
                      step cfg env (.staticAssert (.val (.scalar .bool n))) = some (env, .skip) := by
                    unfold step; unfold step.stepAssert; rfl
                  rw [hstep] at hs
                  cases hs
                  exact ⟨Γ, hm, by unfold check; rfl⟩
              | _ => simp [valTy] at hcond
          | _ => simp [valTy] at hcond
      | _ =>
          dsimp [step] at hs
          obtain ⟨e0, hsub, rfl, rfl⟩ := assert_child hs (by intro v h; cases h)
          have h' := expr_preservation hm hcond hsub
          exact ⟨Γ, hm, by unfold check; simp [h']⟩
  | assume e =>
      unfold check at ht
      split at ht <;> try cases ht
      rename_i hcond
      cases e with
      | val v =>
          simp [infer] at hcond
          cases v with
          | scalar d n =>
              cases d with
              | bool =>
                  have hstep :
                      step cfg env (.assume (.val (.scalar .bool n))) = some (env, .skip) := by
                    unfold step; unfold step.stepAssert; rfl
                  rw [hstep] at hs
                  cases hs
                  exact ⟨Γ, hm, by unfold check; rfl⟩
              | _ => simp [valTy] at hcond
          | _ => simp [valTy] at hcond
      | _ =>
          dsimp [step] at hs
          obtain ⟨e0, hsub, rfl, rfl⟩ := assert_child hs (by intro v h; cases h)
          have h' := expr_preservation hm hcond hsub
          exact ⟨Γ, hm, by unfold check; simp [h']⟩
  | devicePrint e =>
      unfold check at ht
      split at ht <;> try cases ht
      rename_i _ he
      cases e with
      | val v =>
          have hstep : step cfg env (.devicePrint (.val v)) = some (env, .skip) := by
            unfold step; unfold step.stepPrint; rfl
          rw [hstep] at hs
          cases hs
          exact ⟨Γ, hm, by unfold check; rfl⟩
      | _ =>
          dsimp [step] at hs
          obtain ⟨e0, hsub, rfl, rfl⟩ := print_child hs (by intro v h; cases h)
          have h' := expr_preservation hm he hsub
          exact ⟨Γ, hm, by unfold check; simp [h']⟩
  | staticPrint e =>
      unfold check at ht
      split at ht <;> try cases ht
      rename_i _ he
      cases e with
      | val v =>
          have hstep : step cfg env (.staticPrint (.val v)) = some (env, .skip) := by
            unfold step; unfold step.stepPrint; rfl
          rw [hstep] at hs
          cases hs
          exact ⟨Γ, hm, by unfold check; rfl⟩
      | _ =>
          dsimp [step] at hs
          obtain ⟨e0, hsub, rfl, rfl⟩ := print_child hs (by intro v h; cases h)
          have h' := expr_preservation hm he hsub
          exact ⟨Γ, hm, by unfold check; simp [h']⟩

/-- Every configuration reachable from a typed command is typed at the same result context. -/
theorem type_safety {cfg : Cfg} {env env2 : Env} {c c2 : Cmd} {Γ Γout : Ctx}
    (hm : models env Γ) (ht : check Γ c = some Γout)
    (hr : Steps cfg env c env2 c2) :
    ∃ Γ2, models env2 Γ2 ∧ check Γ2 c2 = some Γout := by
  induction hr generalizing Γ with
  | refl _ _ => exact ⟨Γ, hm, ht⟩
  | tail _ _ _ _ _ _ hs _ ih =>
      obtain ⟨Γ1, hm1, ht1⟩ := preservation hm ht hs
      exact ih hm1 ht1

end Triton
