import SampleReuse.FiniteSignStopping
import SampleReuse.StoppedDriftCharging

open MeasureTheory SecondOrder
open scoped BigOperators InnerProductSpace Classical

namespace SampleReuse
noncomputable section

theorem finiteSign_stopped_orthogonal {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {M : ℕ} (v : Fin M → (Fin M → Bool) → E) (hv : SignPredictable v)
    (s t : (Fin M → Bool) → ℕ) (hs : SignStoppingTime s) (ht : SignStoppingTime t)
    (i j : Fin M) (hne : i ≠ j) :
    uniformMean (fun w => ⟪intervalIncrement s t (predictableSignInnovation v) i w,
      intervalIncrement s t (predictableSignInnovation v) j w⟫_ℝ) = 0 := by
  let v' (i : Fin M) (w : Fin M → Bool) := if s w ≤ i.val ∧ i.val < t w then v i w else 0
  have hv' : SignPredictable v' := hv.stopped_interval s t hs ht
  have he (i : Fin M) (w : Fin M → Bool) :
      intervalIncrement s t (predictableSignInnovation v) i w = predictableSignInnovation v' i w := by
    simp only [intervalIncrement,predictableSignInnovation,v']
    split_ifs <;> simp only [smul_zero]
  simp_rw [he]
  exact predictableSignInnovation_orthogonal v' hv' i j hne

theorem finiteSign_stopped_interval {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {M : ℕ} (x : (Fin M → Bool) → ℕ → E) (a v : Fin M → (Fin M → Bool) → E)
    (hv : SignPredictable v)
    (hx : ∀ w k, x w (k.val+1)-x w k.val = a k w+predictableSignInnovation v k w)
    (s t : (Fin M → Bool) → ℕ) (hs : SignStoppingTime s) (ht : SignStoppingTime t)
    (hst : ∀ w, s w ≤ t w) (hcap : ∀ w, t w ≤ M)
    {σ L : ℝ} (hσ : 0 ≤ σ) (hL : 0 ≤ L) :
    uniformMean (fun w => min (σ^2) (L^2*‖x w (t w)-x w (s w)‖^2)) ≤
      2*σ*L*uniformMean (fun w => ∑ k, ‖intervalIncrement s t a k w‖) +
      2*L^2*uniformMean (fun w => ∑ k, ‖intervalIncrement s t (predictableSignInnovation v) k w‖^2) := by
  have hb := expected_truncated_interval (PMF.uniformOfFintype (Fin M → Bool)) Finset.univ
    (intervalIncrement s t a) (intervalIncrement s t (predictableSignInnovation v)) hσ hL
    (fun i _ j _ hne => finiteSign_stopped_orthogonal v hv s t hs ht i j hne)
  have he := stopped_interval_telescopes s t hst hcap x a (predictableSignInnovation v) hx
  simp_rw [he] at hb
  simpa only [uniformMean,pmfMean_finset_sum] using hb

/-- Finite-sign stopped checkpoint charging with no orthogonality or
conditional-independence hypotheses: these follow from prefix predictability
and first-crossing stopping events. The oracle tape is a fixed parameter. -/
theorem finiteSign_stopped_overlap {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] {M : ℕ}
    (x : (Fin M → Bool) → ℕ → E) (a v : Fin M → (Fin M → Bool) → E)
    (hv : SignPredictable v)
    (hx : ∀ w k, x w (k.val+1)-x w k.val = a k w+predictableSignInnovation v k w)
    (s t : ι → (Fin M → Bool) → ℕ)
    (hs : ∀ i, SignStoppingTime (s i)) (ht : ∀ i, SignStoppingTime (t i))
    (hst : ∀ i w, s i w ≤ t i w) (hcap : ∀ i w, t i w ≤ M)
    (depth : ℕ) (hdepth : ∀ w (k : Fin M),
      (Finset.univ.filter (fun i => s i w ≤ k.val ∧ k.val < t i w)).card ≤ depth)
    {σ L : ℝ} (hσ : 0 ≤ σ) (hL : 0 ≤ L) :
    uniformMean (fun w => ∑ i, min (σ^2) (L^2*‖x w (t i w)-x w (s i w)‖^2)) ≤
      2*(depth:ℝ)*(σ*L*uniformMean (fun w => ∑ k, ‖a k w‖) +
        L^2*uniformMean (fun w => ∑ k, ‖predictableSignInnovation v k w‖^2)) := by
  have hb := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
    finiteSign_stopped_interval x a v hv hx (s i) (t i) (hs i) (ht i) (hst i) (hcap i) hσ hL)
  have hd := uniformMean_mono (fun w : Fin M → Bool =>
    interval_overlap_charge s t depth w (fun k => ‖a k w‖) (fun k => norm_nonneg _) (hdepth w))
  have hz := uniformMean_mono (fun w : Fin M → Bool =>
    interval_overlap_charge s t depth w (fun k => ‖predictableSignInnovation v k w‖^2) (fun k => sq_nonneg _) (hdepth w))
  have hn (i : ι) (k : Fin M) (w : Fin M → Bool) :
      ‖intervalIncrement (s i) (t i) a k w‖ = if s i w ≤ k.val ∧ k.val < t i w then ‖a k w‖ else 0 := by
    unfold intervalIncrement
    split_ifs <;> simp only [norm_zero]
  have hnz (i : ι) (k : Fin M) (w : Fin M → Bool) :
      ‖intervalIncrement (s i) (t i) (predictableSignInnovation v) k w‖^2 =
        if s i w ≤ k.val ∧ k.val < t i w then ‖predictableSignInnovation v k w‖^2 else 0 := by
    unfold intervalIncrement
    split_ifs <;> simp only [norm_zero,zero_pow (by decide : 2 ≠ 0)]
  simp_rw [hn,hnz] at hb
  simp only [uniformMean,pmfMean_finset_sum,pmfMean_mul] at hd hz hb ⊢
  simp only [Finset.sum_add_distrib,← Finset.mul_sum] at hb
  nlinarith [mul_le_mul_of_nonneg_left hd (by positivity : 0 ≤ 2*σ*L),
    mul_le_mul_of_nonneg_left hz (by positivity : 0 ≤ 2*L^2)]

end
end SampleReuse
