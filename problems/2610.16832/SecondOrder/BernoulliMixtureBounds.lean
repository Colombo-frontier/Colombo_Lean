import SecondOrder.BernoulliMixtureCalculus

open scoped BigOperators Classical

namespace SecondOrder
noncomputable section

theorem pmfMean_abs_mul_le_of_bound {α : Type*} [Fintype α] (P : PMF α)
    (X Y : α → ℝ) (M : ℝ) (hX : ∀ w, |X w| ≤ M) :
    pmfMean P (fun w => |X w*Y w|) ≤ M*pmfMean P (fun w => |Y w|) := by
  rw [← pmfMean_mul]
  exact pmfMean_mono P (fun w => by rw [abs_mul]; exact mul_le_mul_of_nonneg_right (hX w) (abs_nonneg _))

theorem abs_pmfMean_le {α : Type*} [Fintype α] (P : PMF α) (X : α → ℝ) :
    |pmfMean P X| ≤ pmfMean P (fun w => |X w|) := by
  simpa only [Real.norm_eq_abs] using norm_pmfMean_le P X

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem bernoulliMixture_fderiv_abs_le (p : ι → E → ℝ) (V : (ι → Bool) → E → ℝ)
    (hp : ∀ i, ContDiff ℝ 2 (p i)) (hV : ∀ w, ContDiff ℝ 2 (V w))
    (x u : E) (hp0 : ∀ i, 0 < p i x) (hp1 : ∀ i, p i x < 1)
    (v₀ A : ℝ) (hv₀ : 0 ≤ v₀) (hval : ∀ w, |V w x| ≤ v₀)
    (hder : ∀ w, |fderiv ℝ (V w) x u| ≤ A) :
    |fderiv ℝ (bernoulliMixture p V) x u| ≤ A +
      v₀ * Real.sqrt (bernoulliFisherEnergy (fun i => p i x) (fun i => fderiv ℝ (p i) x u)) := by
  let P := bernoulliProduct (fun i => p i x) (fun i => (hp0 i).le) (fun i => (hp1 i).le)
  let S := bernoulliScoreSum (fun i => p i x) (fun i => fderiv ℝ (p i) x u)
  have hscore := bernoulliScoreSum_abs_mean_le (fun i => p i x) (fun i => fderiv ℝ (p i) x u) hp0 hp1
  have hprod := pmfMean_abs_mul_le_of_bound P (fun w => V w x) S v₀ hval
  have hfirst := pmfMean_le_const P A hder
  rw [bernoulliMixture_fderiv p V hp hV x u hp0 hp1]
  have ht := (abs_pmfMean_le P (fun w => fderiv ℝ (V w) x u + V w x*S w)).trans
    (pmfMean_mono P (fun w => abs_add (fderiv ℝ (V w) x u) (V w x*S w)))
  simp only [pmfMean_add] at ht ⊢
  exact ht.trans (add_le_add hfirst (hprod.trans (mul_le_mul_of_nonneg_left hscore hv₀)))

theorem bernoulliMixture_second_abs_le (p : ι → E → ℝ) (V : (ι → Bool) → E → ℝ)
    (hp : ∀ i, ContDiff ℝ 2 (p i)) (hV : ∀ w, ContDiff ℝ 2 (V w))
    (x u v : E) (hp0 : ∀ i, 0 < p i x) (hp1 : ∀ i, p i x < 1)
    (v₀ A B C : ℝ) (hv₀ : 0 ≤ v₀) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hval : ∀ w, |V w x| ≤ v₀) (hdu : ∀ w, |fderiv ℝ (V w) x u| ≤ A)
    (hdv : ∀ w, |fderiv ℝ (V w) x v| ≤ B)
    (hd2 : ∀ w, |secondBilinear (V w) x u v| ≤ C) :
    |secondBilinear (bernoulliMixture p V) x u v| ≤
      C + A*Real.sqrt (bernoulliFisherEnergy (fun i => p i x) (fun i => fderiv ℝ (p i) x v)) +
      B*Real.sqrt (bernoulliFisherEnergy (fun i => p i x) (fun i => fderiv ℝ (p i) x u)) +
      v₀*(2*∑ i, |secondBilinear (p i) x u v| +
        2*Real.sqrt (bernoulliFisherEnergy (fun i => p i x) (fun i => fderiv ℝ (p i) x u))*
          Real.sqrt (bernoulliFisherEnergy (fun i => p i x) (fun i => fderiv ℝ (p i) x v))) := by
  let P := bernoulliProduct (fun i => p i x) (fun i => (hp0 i).le) (fun i => (hp1 i).le)
  let S (t : E) := bernoulliScoreSum (fun i => p i x) (fun i => fderiv ℝ (p i) x t)
  let K := bernoulliSecondScore (fun i => p i x) (fun i => fderiv ℝ (p i) x u)
    (fun i => fderiv ℝ (p i) x v) (fun i => secondBilinear (p i) x u v)
  have hs (t : E) := bernoulliScoreSum_abs_mean_le (fun i => p i x) (fun i => fderiv ℝ (p i) x t) hp0 hp1
  have hk := bernoulliSecondScore_abs_mean_le (fun i => p i x) (fun i => fderiv ℝ (p i) x u)
    (fun i => fderiv ℝ (p i) x v) (fun i => secondBilinear (p i) x u v) hp0 hp1
  have ha := (pmfMean_abs_mul_le_of_bound P (fun w => fderiv ℝ (V w) x u) (S v) A hdu).trans
    (mul_le_mul_of_nonneg_left (hs v) hA)
  have hb := (pmfMean_abs_mul_le_of_bound P (fun w => fderiv ℝ (V w) x v) (S u) B hdv).trans
    (mul_le_mul_of_nonneg_left (hs u) hB)
  have hc := (pmfMean_abs_mul_le_of_bound P (fun w => V w x) K v₀ hval).trans
    (mul_le_mul_of_nonneg_left hk hv₀)
  have hh := pmfMean_le_const P C hd2
  have htri (w : ι → Bool) :
      |secondBilinear (V w) x u v + fderiv ℝ (V w) x u*S v w + fderiv ℝ (V w) x v*S u w + V w x*K w| ≤
        |secondBilinear (V w) x u v| + |fderiv ℝ (V w) x u*S v w| +
          |fderiv ℝ (V w) x v*S u w| + |V w x*K w| :=
    (abs_add _ _).trans (add_le_add_right ((abs_add _ _).trans (add_le_add_right (abs_add _ _) _)) _)
  rw [bernoulliMixture_secondBilinear p V hp hV x u v hp0 hp1]
  have ht := (abs_pmfMean_le P _).trans (pmfMean_mono P htri)
  simp only [pmfMean_add] at ht ⊢
  exact ht.trans (add_le_add (add_le_add (add_le_add hh ha) hb) hc)

end
end SecondOrder
