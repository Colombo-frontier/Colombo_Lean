import LowRank.GaussianFrobeniusHardness

/-! The remaining Wishart spectral probability premise concerns a genuine
measurable event of the input matrix alone, independently of algorithm seeds. -/

namespace LowRank
open Matrix MeasureTheory
open scoped Matrix
noncomputable section

theorem isClosed_setOf_posSemidef (d : ℕ) :
    IsClosed {A : Matrix (Fin d) (Fin d) ℝ | A.PosSemidef} := by
  simp only [Matrix.PosSemidef, Set.setOf_and, Set.setOf_forall]
  apply IsClosed.inter
  · change IsClosed {A : Matrix (Fin d) (Fin d) ℝ | Aᴴ = A}
    exact isClosed_eq (by fun_prop) continuous_id
  · apply isClosed_iInter
    intro x
    apply isClosed_le continuous_const
    simp only [dotProduct, Matrix.mulVec]
    fun_prop

theorem measurableSet_wishartSpectralEvent (d t : ℕ) (L c₀ k : ℝ) :
    MeasurableSet (wishartSpectralEvent d t L c₀ k) := by
  have hW := measurable_wishart d t
  have hK := measurable_leftKernelProjector (m := Fin d) (n := Fin t)
  have hupper : Measurable (fun X : Matrix (Fin d) (Fin t) ℝ => (L / 2) • 1 - wishart X) := by
    apply measurable_pi_lambda
    intro i
    apply measurable_pi_lambda
    intro j
    exact measurable_const.sub ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp hW))
  have hlower : Measurable (fun X : Matrix (Fin d) (Fin t) ℝ =>
      wishart X - (c₀ * (k / d) ^ 2) • (1 - leftKernelProjector X)) := by
    apply measurable_pi_lambda
    intro i
    apply measurable_pi_lambda
    intro j
    exact ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp hW)).sub
      (measurable_const.mul (measurable_const.sub
        ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp hK))))
  exact ((isClosed_setOf_posSemidef d).measurableSet.preimage hupper).inter
    ((isClosed_setOf_posSemidef d).measurableSet.preimage hlower)

theorem wishartSpectralEvent_bad_prod_real (d t : ℕ) (L c₀ k : ℝ)
    {S : Type*} [MeasurableSpace S] (ν : Measure S) [IsProbabilityMeasure ν] :
    (ν.prod (gaussianMatrixLaw d t)).real {z | z.2 ∉ wishartSpectralEvent d t L c₀ k} =
      (gaussianMatrixLaw d t).real (wishartSpectralEvent d t L c₀ k)ᶜ := by
  have heq : {z : S × Matrix (Fin d) (Fin t) ℝ | z.2 ∉ wishartSpectralEvent d t L c₀ k} =
      (Set.univ : Set S) ×ˢ (wishartSpectralEvent d t L c₀ k)ᶜ := by
    ext z
    simp
  rw [heq]
  simp [measureReal_prod_prod, measureReal_def]

end
end LowRank
