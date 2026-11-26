import NCConcave16991.DenseWeakAdaptiveBank

/-! # Chronological finite adaptive row experiments -/

noncomputable section

namespace NCConcave16991.DenseWeakHiding.RowExperiment

variable {I D Y A : Type*} {r : ℕ}

def extend : {r : ℕ} → (E : RowExperiment I D Y r) →
    ((Fin r → D → Y) → I) → RowExperiment I D Y (r + 1)
  | 0, .done, nextRow => .query (nextRow Fin.elim0) (fun _ ↦ .done)
  | _ + 1, .query i next, nextRow =>
      .query i (fun y ↦ extend (next y) (fun h ↦ nextRow (Fin.cons y h)))

theorem run_extend (read : A → I → Y) (E : RowExperiment I D Y r)
    (nextRow : (Fin r → D → Y) → I) (bank : D → A) :
    (E.extend nextRow).run read bank =
      Fin.snoc (E.run read bank) (fun d ↦ read (bank d) (nextRow (E.run read bank))) := by
  induction E with
  | done =>
      ext t
      have ht : t = 0 := Fin.ext (by omega)
      subst t
      rfl
  | @query r i next ih =>
      simp only [extend, run, ih, Fin.cons_snoc_eq_snoc_cons]

def policyExperiment (nextRow : ∀ r : ℕ, (Fin r → D → Y) → I) :
    (r : ℕ) → RowExperiment I D Y r
  | 0 => .done
  | r + 1 => (policyExperiment nextRow r).extend (nextRow r)

theorem run_policyExperiment_succ (read : A → I → Y)
    (nextRow : ∀ r : ℕ, (Fin r → D → Y) → I) (r : ℕ) (bank : D → A) :
    (policyExperiment nextRow (r + 1)).run read bank =
      Fin.snoc ((policyExperiment nextRow r).run read bank)
        (fun d ↦ read (bank d) (nextRow r ((policyExperiment nextRow r).run read bank))) :=
  run_extend read _ _ bank

def snocEquiv (r : ℕ) (Z : Type*) : (Fin r → Z) × Z ≃ (Fin (r + 1) → Z) where
  toFun := fun z ↦ Fin.snoc z.1 z.2
  invFun := fun z ↦ (Fin.init z,z (Fin.last r))
  left_inv := fun z ↦ by simp
  right_inv := Fin.snoc_init_self

end NCConcave16991.DenseWeakHiding.RowExperiment
