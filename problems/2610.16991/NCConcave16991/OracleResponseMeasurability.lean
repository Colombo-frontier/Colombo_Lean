import NCConcave16991.Problem

/-! # Measurability of actual value/full-gradient component replies -/

open Set MeasureTheory
open scoped NNReal

namespace NCConcave16991

noncomputable section

variable {p : ProblemParameters} {dx dy : ℕ} {K : KnownDualDomain dy p.diameter}

theorem Problem.componentGradient_continuousOn (P : Problem p dx dy K)
    (h : P.averagedSmooth) (i : Fin p.n) :
    ContinuousOn (P.componentGradient i) (productDomain dx K) := by
  let C : ℝ≥0 := ⟨Real.sqrt (p.n : ℝ) * p.L,
    mul_nonneg (Real.sqrt_nonneg _) p.L_pos.le⟩
  have hl : LipschitzOnWith C (P.componentGradient i) (productDomain dx K) := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    simp only [dist_eq_norm, C]
    exact AveragedSmooth.component_lipschitz p.n_pos p.L_pos.le h i x hx y hy
  exact hl.continuousOn

/-- The reply is Borel measurable even though the selected component index
may be fully adaptive and the query norm is unrestricted. -/
theorem oracleResponse_measurable (P : Problem p dx dy K) (h : P.averagedSmooth) :
    Measurable (oracleResponse P) := by
  apply measurable_from_prod_countable_right
  intro i
  let Q : PrimalSpace dx × K.carrier → JointSpace dx dy :=
    fun z ↦ jointPoint z.1 z.2.val
  have hQ : Continuous Q :=
    (WithLp.prod_continuous_toLp 2 _ _).comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
  have hmem : ∀ z, Q z ∈ productDomain dx K := fun z ↦ z.2.property
  have hv : Continuous (fun z ↦ P.component i (Q z)) := by
    apply continuous_iff_continuousAt.mpr
    intro z
    exact (P.hasGradientAt_on_domain i (Q z) (hmem z)).continuousAt.comp hQ.continuousAt
  have hg : Continuous (fun z ↦ P.componentGradient i (Q z)) :=
    (P.componentGradient_continuousOn h i).comp_continuous hQ hmem
  have hp := (WithLp.prod_continuous_ofLp 2 (PrimalSpace dx) (DualSpace dy)).comp hg
  exact hv.measurable.prodMk (hp.fst.measurable.prodMk hp.snd.measurable)

end

end NCConcave16991
