import GaussianPerturbation254
import NumericalPrimitives254
import GaussianMetric254

noncomputable section
namespace Paper254

theorem approximate_minimizer_transfer {α : Type*} (f g : α→ℝ) (m v : α) (e ξ : ℝ)
    (herr : ∀ w,|f w-g w|≤e) (hmin : g m≤g v+ξ) : f m≤f v+ξ+2*e := by
  have hm := abs_le.mp (herr m)
  have hv := abs_le.mp (herr v)
  linarith

/-- A projection oracle may receive rounded centre and metric inputs.
This transfers its objective guarantee back to the exact metric. -/
theorem rounded_projection_input_gap {d : ℕ} {D : ℝ} (W : Domain d D)
    (A B : Precision d) (hA : A.PosDef) (a b : Space d) (m : W.carrier)
    (M R e t ξ : ℝ) (hM : 0≤M) (hR : 0≤R) (he : 0≤e) (ht : 0≤t)
    (hB : ∀ i j,|B i j|≤M) (hAB : ∀ i j,|A i j-B i j|≤e)
    (hwa : ∀ w : W.carrier,∀ i,|w.val i-a i|≤R)
    (hwb : ∀ w : W.carrier,∀ i,|w.val i-b i|≤R)
    (hab : ∀ i,|a i-b i|≤t)
    (horacle : ∀ v : W.carrier,matrixQuadratic B (m.val-b)≤matrixQuadratic B (v.val-b)+ξ) :
    ‖precisionFactor hA (m.val-(metricProject W (precisionFactor hA) a).val)‖^2≤
      ξ+2*(d:ℝ)^2*(e*R^2+2*M*R*t) := by
  let f : W.carrier→ℝ := fun w=>matrixQuadratic A (w.val-a)
  let g : W.carrier→ℝ := fun w=>matrixQuadratic B (w.val-b)
  have herr : ∀ w,|f w-g w|≤(d:ℝ)^2*(e*R^2+2*M*R*t) := by
    intro w
    apply quadratic_entry_perturbation A B (w.val-a) (w.val-b) M R e t hM hR he ht
      hB hAB (hwa w) (hwb w)
    intro i
    change |(w.val i-a i)-(w.val i-b i)|≤t
    rw [show (w.val i-a i)-(w.val i-b i)=-(a i-b i) by ring,abs_neg]
    exact hab i
  have hg := approximate_minimizer_transfer f g m (metricProject W (precisionFactor hA) a)
    ((d:ℝ)^2*(e*R^2+2*M*R*t)) ξ herr (horacle _)
  apply metricProject_objective_gap W (precisionFactor hA) a m _
  rw [precisionFactor_norm,precisionFactor_norm]
  dsimp [f] at hg
  linarith

theorem projected_mean_coordinate_error {d : ℕ} {D : ℝ} (W : Domain d D)
    (A : Precision d) (hA : A.PosDef) (a : Space d) (m : W.carrier) (l ξ : ℝ)
    (hl : 0<l) (hξ : 0≤ξ)
    (hlower : ∀ x : Space d,l*‖x‖^2≤matrixQuadratic A x)
    (hgap : ‖precisionFactor hA (m.val-(metricProject W (precisionFactor hA) a).val)‖^2≤ξ) :
    ∀ i,|m.val i-(metricProject W (precisionFactor hA) a).val i|≤Real.sqrt (ξ/l) := by
  let x := m.val-(metricProject W (precisionFactor hA) a).val
  have hs : ‖x‖^2≤ξ/l := by
    apply (le_div_iff₀ hl).mpr
    have hh := hlower x
    rw [← precisionFactor_norm hA] at hh
    change ‖precisionFactor hA x‖^2≤ξ at hgap
    nlinarith
  have hn : ‖x‖≤Real.sqrt (ξ/l) := by
    nlinarith [Real.sq_sqrt (div_nonneg hξ hl.le),Real.sqrt_nonneg (ξ/l),norm_nonneg x]
  intro i
  exact (PiLp.norm_apply_le x i).trans hn

end Paper254
#print axioms Paper254.rounded_projection_input_gap
#print axioms Paper254.projected_mean_coordinate_error
