import Bilevel.OrdinaryFrameObserver
import Bilevel.GenieDimension

/-! The source-style sufficient dimension condition discharges the raw
genie's residual-rank and all-column revelation-energy budgets for the
actual two-precoin-query plus terminal-output protocol. -/
noncomputable section
open MeasureTheory
open scoped ENNReal
universe u
namespace Bilevel.OrdinaryFrame
open EuclideanGaussian ProjectionPosterior TransportControllerMachine

theorem dimension_observer {d T Q : ℕ} {H : Memory.{u}} {C : Type*} [MeasurableSpace C]
    (hT : T≤d) (hTpos : 0<T) (L : Rules H d T)
    (initial : C → H) (hi : Measurable initial) (ρ : Measure C) [IsProbabilityMeasure ρ]
    (t : ℕ) (δ K θ R τ : ℝ) (hδ : 0<δ) (hδ1 : δ≤1)
    (hK : 1≤K) (hθ : 1≤θ) (hR : 0<R) (hτ : 0<τ)
    (hratio : R^2≤K^2*θ^2*T*τ^2)
    (hD : 128*K^2*(((2*Q+1:ℕ):ℝ)+T)*θ^2*T*
      Real.log (4*((2*Q+1:ℕ):ℝ)*T/δ)≤d) :
    (ρ.prod (HaarFrame.frameLaw d T hT)) {p | ¬Observed L (τ^2/(4*R^2))
      Q T t (initial p.1,(⊥,∅)) p.2}≤ENNReal.ofReal (δ/2) := by
  let M := 2*Q+1
  let ℓ := Real.log (4*(M:ℝ)*T/δ)
  have hm : (1:ℝ)≤M := by dsimp [M];exact_mod_cast (show 1≤2*Q+1 by omega)
  have ht : (1:ℝ)≤T := by exact_mod_cast hTpos
  have hl : 1≤ℓ := GenieDimension.logarithm_one_le M T δ hm ht hδ hδ1
  have hd' : 128*K^2*((M:ℝ)+T)*θ^2*T*ℓ≤d := hD
  have hres := (GenieDimension.dimension_budget d M T K θ ℓ hm ht hK hθ hl hd').1
  have hnat : M+T+2<d := by
    have hh : (M:ℝ)+T+2<d := by linarith
    exact_mod_cast hh
  let r := d-(M+T+2)
  have hr : 0<r := by dsimp [r];omega
  have hrval : (r:ℝ)=(d:ℝ)-M-T-2 := by
    dsimp [r]
    rw [Nat.cast_sub (by omega : M+T+2≤d)]
    push_cast
    ring
  have hgeom := GenieDimension.sufficient_dimension d M T K θ ℓ R τ hm ht hK hθ hl
    hR hτ hratio hd'
  dsimp only at hgeom
  have hb : GenieProtocol.logarithmicIncrement M T r δ=8*ℓ/((d:ℝ)-M-T-2) := by
    simp only [GenieProtocol.logarithmicIncrement,hrval,ℓ]
  have hcap : (T:ℝ)*((M:ℝ)*GenieProtocol.logarithmicIncrement M T r δ)≤1/2 := by
    rw [hb]
    nlinarith only [hgeom.2.1]
  have hsmall : 2*(M:ℝ)*GenieProtocol.logarithmicIncrement M T r δ≤τ^2/(4*R^2) := by
    rw [hb]
    exact hgeom.2.2
  have hdims : M+T+(r+1)≤d := by dsimp [r];omega
  have hp := logarithmic_observer hT hTpos hr L initial hi ρ t δ hδ hδ1 hdims hcap
  refine (measure_mono ?_).trans hp
  intro p hbad hgood
  exact hbad (observed_mono L hsmall Q T t _ _ hgood)

end Bilevel.OrdinaryFrame
