import Bilevel.CachedEstimatorUnion

/-! Accuracy of the actual cached estimator on its four-operation good event,
and a local confidence certificate whenever the stored cache is accurate. -/
noncomputable section
open MeasureTheory ProbabilityTheory
namespace Bilevel.CachedEstimatorProcedure
open Stateful

variable {X Y History : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
  [MeasurableSpace History] {σf σg μ Lf Lg Cf ρ : ℝ}
  (O : HistorySFO (Query := X × Y) (History := History) (X := X) (Y := Y) σf σg)
  (P : Model.Primitive (X := X) (Y := Y) μ Lf Lg Cf ρ)
  [FiniteDimensional ℝ Y]

theorem estimate_good_bound (hgx : ∀ x y, O.lower.truth_x (x,y) = P.gx x y)
    (p : Input X Y) (z : Transcript X Y) {t r δ eC e : ℝ} (ht : 0 < t)
    (hcache : ‖p.2.1 - P.fx p.1 (P.canonicalResponse.y p.1)‖ +
      Lg / μ * ‖p.2.2.1 - P.fy p.1 (P.canonicalResponse.y p.1)‖ ≤ eC)
    (hgood : z ∉ badEvent O p.1 (P.canonicalResponse.y p.1)
      (P.tiltedResponse p.1 t p.2.2.1) r δ)
    (hbudget : eC + t⁻¹ * (2*Lg*r + 2*δ) +
      ((1 + Lg / μ) * ρ * Cf^2 / (2*μ^2)) * t ≤ e) :
    ‖estimate t p z - gradient (P.hyperobjective P.canonicalResponse) p.1‖ ≤ e := by
  simp only [badEvent, firstBad, solveBad, Set.mem_setOf_eq, not_or, not_lt, hgx] at hgood
  have hsolve := add_le_add
    (mul_le_mul_of_nonneg_left hgood.1.1.2 P.Lg_nonneg)
    (mul_le_mul_of_nonneg_left hgood.1.1.1 P.Lg_nonneg)
  have herr : Lg * ‖z.1.2 - P.tiltedResponse p.1 t p.2.2.1‖ +
      Lg * ‖z.1.1 - P.canonicalResponse.y p.1‖ +
      ‖z.2.2 - P.gx p.1 z.1.2‖ + ‖z.2.1 - P.gx p.1 z.1.1‖ ≤ 2*Lg*r+2*δ := by
    linarith [hgood.1.2, hgood.2]
  have hm := mul_le_mul_of_nonneg_left herr (inv_nonneg.mpr ht.le)
  have he := estimate_error P p z ht
  linarith

variable [Nontrivial Y]

theorem estimator_confidence (hgy : ∀ x y, O.lower.truth_y (x,y) = P.gy x y)
    (hgx : ∀ x y, O.lower.truth_x (x,y) = P.gx x y)
    (t D r δ : ℝ) (ht : 0 < t) (hr : 0 < r) (hδ : 0 < δ) (q : ℕ) [NeZero q]
    (p : Input X Y) {eC e : ℝ}
    (h₀ : ‖p.2.2.2 - P.canonicalResponse.y p.1‖ ≤ D)
    (hₜ : ‖p.2.2.2 - P.tiltedResponse p.1 t p.2.2.1‖ ≤ D)
    (hcache : ‖p.2.1 - P.fx p.1 (P.canonicalResponse.y p.1)‖ +
      Lg / μ * ‖p.2.2.1 - P.fy p.1 (P.canonicalResponse.y p.1)‖ ≤ eC)
    (hbudget : eC + t⁻¹ * (2*Lg*r + 2*δ) +
      ((1 + Lg / μ) * ρ * Cf^2 / (2*μ^2)) * t ≤ e) (h : History) :
    ((estimator O μ Lg t D r δ q).law (p,h)).real
      {z | e < ‖z.1 - gradient (P.hyperobjective P.canonicalResponse) p.1‖} ≤
        4 * Real.exp (-(q : ℝ) / 8) := by
  classical
  have hh := Procedure.map_failure_union_bound (transcript O μ Lg t D r δ q)
    (fun z => estimate t z.1 z.2) (by unfold estimate; fun_prop) p h
    {v | e < ‖v - gradient (P.hyperobjective P.canonicalResponse) p.1‖}
    (measurableSet_lt measurable_const (measurable_id.sub_const _).norm)
    (badEvent O p.1 (P.canonicalResponse.y p.1) (P.tiltedResponse p.1 t p.2.2.1) r δ)
    (badEvent_measurable O p.1 _ _ r δ) False (fun z hz => by
      right
      by_contra hgood
      exact (not_lt_of_ge (estimate_good_bound O P hgx p z ht hcache hgood hbudget)) hz)
    (transcript_confidence O P hgy t D r δ hr hδ q p h₀ hₜ h)
  simpa only [ite_false, zero_add] using hh

end Bilevel.CachedEstimatorProcedure
