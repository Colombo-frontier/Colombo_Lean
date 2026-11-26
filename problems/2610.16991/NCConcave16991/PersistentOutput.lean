import NCConcave16991.PersistentBound
import NCConcave16991.FiniteOutput

/-! # Actual uniform-output stationarity of the persistent trajectory -/

open Set MeasureTheory
open scoped BigOperators

namespace NCConcave16991.PersistentProcess

noncomputable section

variable {n b dx dy : ℕ} [NeZero n] [MeasurableSpace (Fin n)]
  [MeasurableSingletonClass (Fin n)]
  {J : Type*} [Finite J] [MeasurableSpace J] [MeasurableSingletonClass J]

def selectedOutput (G : Fin n → JointSpace dx dy → JointSpace dx dy)
    (y0 : DualSpace dy) (q : ℕ) (solve : State dx dy → J → PrimalSpace dx)
    (c : PrimalSpace dx) {S : ℕ}
    (ω : FiniteProcess.History (J × (Fin b → Fin n)) S × Fin S) : PrimalSpace dx :=
  FiniteProcess.select (fun t h ↦ (process G y0 q solve c t h).center) ω

def outputLaw (σ : Measure J) (S : ℕ) [NeZero S]
    [MeasurableSpace (Fin S)] [MeasurableSingletonClass (Fin S)] :
    Measure (FiniteProcess.History (J × (Fin b → Fin n)) S × Fin S) :=
  (FiniteProcess.law (σ.prod (minibatchLaw n b)) S).prod (uniformIndexLaw S)

instance outputLaw_probability (σ : Measure J) [IsProbabilityMeasure σ]
    (S : ℕ) [NeZero S] [MeasurableSpace (Fin S)] [MeasurableSingletonClass (Fin S)] :
    IsProbabilityMeasure (outputLaw (n := n) (b := b) σ S) := by
  letI : IsProbabilityMeasure (FiniteProcess.law (σ.prod (minibatchLaw n b)) S) :=
    FiniteProcess.law_probability _ _
  unfold outputLaw
  infer_instance

theorem selected_gradient_mean_bound
    {G : Fin n → JointSpace dx dy → JointSpace dx dy} {s : Set (JointSpace dx dy)}
    {f : PrimalSpace dx → ℝ} {L κ noise Δ : ℝ}
    (hL : 0 < L) (hG : AveragedSmooth G s L) (hκ : 1 ≤ κ)
    (hb : 0 < b) (hn : 0 ≤ noise) (hf : BddBelow (range f)) (hw : WeaklyConvex L f)
    (y0 : DualSpace dy) (ha : ∀ x, jointPoint x y0 ∈ s)
    {q : ℕ} (hq : 0 < q) (hbatch : κ * q / b ≤ 1 / 4096)
    (solve : State dx dy → J → PrimalSpace dx)
    (σ : Measure J) [IsProbabilityMeasure σ] (c : PrimalSpace dx)
    (hgap : f c - sInf (range f) ≤ Δ)
    (prox : PrimalSpace dx → PrimalSpace dx)
    (hp : ∀ x, IsProxPoint f L x (prox x))
    (hsolve : ∀ z, (∫ j, ‖solve z j - prox z.center‖ ^ 2 ∂σ) ≤
      (1 / 1024 : ℝ) * ‖prox z.center - z.center‖ ^ 2 +
        3 * weightedErrorSq κ (error G y0 z) / L ^ 2 + noise)
    {S : ℕ} [NeZero S] [MeasurableSpace (Fin S)] [MeasurableSingletonClass (Fin S)] :
    (∫ ω, ‖gradient (moreauEnvelope f L) (selectedOutput G y0 q solve c ω)‖ ^ 2
      ∂outputLaw (n := n) (b := b) σ S) ≤
      4 * L ^ 2 * ((128 / 127 : ℝ) * (Δ / (L * S) + 2 * noise)) := by
  have hmean := mean_displacement_bound hL hG hκ hb hn hf y0 ha hq hbatch solve σ c
    hgap prox hp hsolve (Nat.pos_of_ne_zero (NeZero.ne S))
  have hgrad (x : PrimalSpace dx) :
      ‖gradient (moreauEnvelope f L) x‖ ^ 2 = 4 * L ^ 2 * ‖prox x - x‖ ^ 2 := by
    rw [(moreauEnvelope_hasGradientAt hL hw hp x).gradient]
    simp only [proxResidual, norm_smul, Real.norm_eq_abs,
      abs_of_pos (show 0 < 2 * L by linarith), mul_pow, norm_sub_rev x (prox x)]
    ring
  have hout := FiniteProcess.uniform_prefix_expectation
    (σ.prod (minibatchLaw n b)) (T := S)
    (fun t h ↦ ‖gradient (moreauEnvelope f L) (process G y0 q solve c t h).center‖ ^ 2)
  change (∫ ω, ‖gradient (moreauEnvelope f L) (selectedOutput G y0 q solve c ω)‖ ^ 2
    ∂outputLaw (n := n) (b := b) σ S) = _ at hout
  rw [hout]
  simp_rw [hgrad]
  simp only [integral_const_mul, ← Finset.mul_sum]
  have hh := mul_le_mul_of_nonneg_left hmean (show 0 ≤ 4 * L ^ 2 by positivity)
  dsimp [meanAt] at hh
  convert hh using 1 <;> ring

end

end NCConcave16991.PersistentProcess
