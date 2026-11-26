import Bilevel.PolishedLiteralExpectedFixed

/-! Source hierarchical expected-query consequence for the actual
original SFO and the SAME two-global-frame hard prior. The fixed-horizon
information certificate is instantiated; no bad-event/locality/margin
premise about an algorithm's executed trajectory remains. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace Bilevel.PolishedLiteralActualObserver
open EuclideanGaussian ProjectionPosterior PrimitiveGeometry BorelAdaptive PolishedProjectionDimension
set_option autoImplicit false
set_option maxHeartbeats 1800000
variable {dx du : ℕ}
  [MeasurableSpace (QuerySpace (dx:=dx) (du:=du))] [BorelSpace (QuerySpace (dx:=dx) (du:=du))]
  [MeasurableSpace (Joint (Space dx) (Space du))] [BorelSpace (Joint (Space dx) (Space du))]
  {St Private : Type} [MeasurableSpace St] [MeasurableSpace Private]
  (P : PolishedLiteral.Parameters (X:=Space dx) (U:=Space du))
  (A : Program St (QuerySpace (dx:=dx) (du:=du))
    (QuerySpace (dx:=dx) (du:=du) × QuerySpace (dx:=dx) (du:=du)) (Joint (Space dx) (Space du)))
  (hx : P.macroNode.n+1≤dx) (hu : (P.macroNode.n+1)*(P.n+1)≤du)

/-- An actual fixed pair of mean frames requires expected original calls
at least S*M/(512*p) from every uniformly accurate randomized algorithm.
Nontermination costs infinity; no integrable stopping-time assumption is
imposed. The original source prefix barrier is the sole extra analytic
certificate. One public floor-horizon dimension choice suffices. -/
theorem conditional_expected_calls (initial : Private → St) (hi : Measurable initial)
    (ρ : Measure Private) [IsProbabilityMeasure ρ]
    (κ τ p ε : ℝ) (hp : 0<p) (hp1 : p≤1) (hε : 0<ε)
    (hRx : 0<P.macroNode.radius) (hRu : 0<P.radius)
    (hb : 0<P.macroNode.width) (hβ : 0<P.β) (hτ : 0<τ) (hτβ : τ≤P.β/4)
    (hτb : τ≤P.macroNode.width) (hδsc : ∀ j,j<P.J → τ≤P.δ j)
    (hdx : sourceDimension (⌊(((P.macroNode.n+1)*(P.n+1):ℕ):ℝ)/(16*p)⌋₊+1)
      (P.macroNode.n+1) P.macroNode.radius (P.macroNode.width/4) (1/8)≤dx)
    (hdu : sourceDimension (2*⌊(((P.macroNode.n+1)*(P.n+1):ℕ):ℝ)/(16*p)⌋₊+1)
      ((P.macroNode.n+1)*(P.n+1)) P.radius τ (1/8)≤du)
    (hbarrier : ∀ (U : Frame dx (P.macroNode.n+1)) (hU : Orthonormal ℝ U)
      (V : Frame du ((P.macroNode.n+1)*(P.n+1))) (hV : Orthonormal ℝ V),
      PrefixBarrier (framedParameters P U hU V hV) κ (P.macroNode.width/4) τ ε)
    (haccuracy : ∀ g : HaarPoint (dx:=dx) (du:=du),
      (∫⁻ s,ENNReal.ofReal (haarLoss P hx hu κ (seededStopped A (haarResponse P hx hu τ p) initial (g,s)))
        ∂ρ.prod (IndependentStream.law (BernoulliOracle.law p hp1)))≤ENNReal.ofReal ε) :
    ∃ g : HaarPoint (dx:=dx) (du:=du),
      ENNReal.ofReal ((((P.macroNode.n+1)*(P.n+1):ℕ):ℝ)/(512*p))≤
        ∫⁻ s,seededCalls A (haarResponse P hx hu τ p) initial (g,s)
          ∂ρ.prod (IndependentStream.law (BernoulliOracle.law p hp1)) := by
  let T := (P.macroNode.n+1)*(P.n+1)
  let H := ⌊(T:ℝ)/(16*p)⌋₊
  let ν := (OrthogonalHaar.law dx).prod (OrthogonalHaar.law du)
  let seedLaw := ρ.prod (IndependentStream.law (BernoulliOracle.law p hp1))
  let response := haarResponse P hx hu τ p
  let loss := haarLoss P hx hu κ
  have hr := haarResponse_measurable P hx hu τ p hb hβ hτ hτβ hτb hδsc
  have hl := haarLoss_measurable P hx hu κ
  have hpos : ∀ z,0≤loss z := fun z => norm_nonneg _
  have hacc := ChiExpectedLower.prior_accuracy_of_uniform ν seedLaw (fun _ => True)
    (Filter.Eventually.of_forall (fun _ => True.intro))
    (fun z => loss (seededStopped A response initial z))
    (hl.comp (seededStopped_measurable A response hr initial hi)) ε (fun g _ => haccuracy g)
  have hfixed : ∀ n : ℕ,(n:ℝ)≤(T:ℝ)/(16*p) →
      13/16≤(ν.prod seedLaw).real {z | 8*ε≤loss (seededCapped A response initial n z)} := by
    intro n hn
    have hnH : n≤H := horizon_le_floor n T p hp hn
    have hdxn : sourceDimension (n+1) (P.macroNode.n+1) P.macroNode.radius (P.macroNode.width/4) (1/8)≤dx :=
      (sourceDimension_mono (by omega : 0<n+1) (Nat.succ_pos _) (by omega : n+1≤H+1)
        P.macroNode.radius (P.macroNode.width/4) (1/8) (by norm_num) (by norm_num)).trans hdx
    have hdun : sourceDimension (2*n+1) T P.radius τ (1/8)≤du :=
      (sourceDimension_mono (by omega : 0<2*n+1) (Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _))
        (by omega : 2*n+1≤2*H+1) P.radius τ (1/8) (by norm_num) (by norm_num)).trans hdu
    exact seeded_fixed_probability P A hx hu initial hi ρ κ τ p ε hp hp1 n hn
      hRx hRu hb hβ hτ hτβ hτb hδsc hdxn hdun hbarrier
  have hc := expected_seededCalls_of_fixed_probabilities A response hr initial hi (ν.prod seedLaw)
    loss hl hpos T p ε hp hε hfixed hacc
  have hT : 0<T := Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _)
  have hR : 0<(T:ℝ)/p := div_pos (Nat.cast_pos.mpr hT) hp
  have hc' : ENNReal.ofReal (((T:ℝ)/p)/256)≤
      ∫⁻ z,seededCalls A response initial z ∂ν.prod seedLaw := by
    convert hc using 1
    congr 1
    ring
  obtain ⟨g,_,hg⟩ := fixed_instance_of_extended_expected_cost ν seedLaw (fun _ => True)
    (Filter.Eventually.of_forall (fun _ => True.intro)) (seededCalls A response initial)
    (seededCalls_measurable A response hr initial hi) hR hc'
  refine ⟨g,?_⟩
  convert hg using 1
  congr 1
  ring

/-- Dimension-only source wrapper: even the frame size witnesses are derived
from the manuscript dimension inequalities. -/
theorem conditional_expected_calls_from_dimensions (initial : Private → St) (hi : Measurable initial)
    (ρ : Measure Private) [IsProbabilityMeasure ρ]
    (κ τ p ε : ℝ) (hp : 0<p) (hp1 : p≤1) (hε : 0<ε)
    (hRx : 0<P.macroNode.radius) (hRu : 0<P.radius)
    (hb : 0<P.macroNode.width) (hβ : 0<P.β) (hτ : 0<τ) (hτβ : τ≤P.β/4)
    (hτb : τ≤P.macroNode.width) (hδsc : ∀ j,j<P.J → τ≤P.δ j)
    (hdx : sourceDimension (⌊(((P.macroNode.n+1)*(P.n+1):ℕ):ℝ)/(16*p)⌋₊+1)
      (P.macroNode.n+1) P.macroNode.radius (P.macroNode.width/4) (1/8)≤dx)
    (hdu : sourceDimension (2*⌊(((P.macroNode.n+1)*(P.n+1):ℕ):ℝ)/(16*p)⌋₊+1)
      ((P.macroNode.n+1)*(P.n+1)) P.radius τ (1/8)≤du)
    (hbarrier : ∀ (U : Frame dx (P.macroNode.n+1)) (hU : Orthonormal ℝ U)
      (V : Frame du ((P.macroNode.n+1)*(P.n+1))) (hV : Orthonormal ℝ V),
      PrefixBarrier (framedParameters P U hU V hV) κ (P.macroNode.width/4) τ ε)
    (haccuracy : ∀ (hxx : P.macroNode.n+1≤dx) (huu : (P.macroNode.n+1)*(P.n+1)≤du)
      (g : HaarPoint (dx:=dx) (du:=du)),
      (∫⁻ s,ENNReal.ofReal (haarLoss P hxx huu κ (seededStopped A (haarResponse P hxx huu τ p) initial (g,s)))
        ∂ρ.prod (IndependentStream.law (BernoulliOracle.law p hp1)))≤ENNReal.ofReal ε) :
    ∃ hxx : P.macroNode.n+1≤dx, ∃ huu : (P.macroNode.n+1)*(P.n+1)≤du,
    ∃ g : HaarPoint (dx:=dx) (du:=du),
      ENNReal.ofReal ((((P.macroNode.n+1)*(P.n+1):ℕ):ℝ)/(512*p))≤
        ∫⁻ s,seededCalls A (haarResponse P hxx huu τ p) initial (g,s)
          ∂ρ.prod (IndependentStream.law (BernoulliOracle.law p hp1)) := by
  let H : ℕ := ⌊(((P.macroNode.n+1)*(P.n+1):ℕ):ℝ)/(16*p)⌋₊
  obtain ⟨_,_,hxx,_,_,_,_,_,_,_⟩ := explicit_dimension_sufficient (H+1) (P.macroNode.n+1) dx
    P.macroNode.radius (P.macroNode.width/4) (1/8) (by omega) (Nat.succ_pos _) hRx
    (by positivity) (by norm_num) (by norm_num) hdx
  obtain ⟨_,_,huu,_,_,_,_,_,_,_⟩ := explicit_dimension_sufficient (2*H+1) ((P.macroNode.n+1)*(P.n+1)) du
    P.radius τ (1/8) (by omega) (Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _)) hRu hτ
    (by norm_num) (by norm_num) hdu
  obtain ⟨g,hg⟩ := conditional_expected_calls P A hxx huu initial hi ρ κ τ p ε hp hp1 hε
    hRx hRu hb hβ hτ hτβ hτb hδsc hdx hdu hbarrier (haccuracy hxx huu)
  exact ⟨hxx,huu,g,hg⟩

end Bilevel.PolishedLiteralActualObserver
