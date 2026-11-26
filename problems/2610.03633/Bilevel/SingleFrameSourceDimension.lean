import Bilevel.SingleFrameSourceProtocol
import Bilevel.ChiSourceHorizonDimension

/-! The ambient dimension is chosen once from public scalar scales and
the finite expected-query horizon. It precedes algorithms and randomness. -/
noncomputable section
set_option autoImplicit false
open scoped ENNReal
namespace Bilevel.SingleFrameSource
open ChiHierarchyIndex ChiHierarchyExecution ChiHierarchyHaar

def energyCap (R τ : ℝ) : ℝ := (τ/(4*R))^2

theorem energyCap_positive {R τ : ℝ} (hR : 0<R) (hτ : 0<τ) : 0<energyCap R τ := by
  unfold energyCap
  positivity

theorem energyCap_small {R τ : ℝ} (hR : 0<R) (hτ : 0<τ) :
    R*Real.sqrt (energyCap R τ)≤τ/2 := by
  rw [energyCap,Real.sqrt_sq (by positivity : 0≤τ/(4*R))]
  have he : R*(τ/(4*R))=τ/4 := by field_simp;ring
  rw [he]
  linarith

theorem exists_dimension (n D₀ : ℕ) (R τ p : ℝ) (hR : 0<R) (hτ : 0<τ) :
    let cap := energyCap R τ
    let N := sourceHorizon (counts n) 0 p
    ∃ D r : ℕ,∃ b : ℝ,D₀≤D ∧
      (∀ i : FrameIndex (counts n) 0,chainSize i+1≤D) ∧
      (2*(N*batchSize (counts n) 0 1)+1)+(N*batchSize (counts n) 0 1)+(r+1)≤D ∧
      0<r ∧ 0<b ∧ b≤2 ∧
      ((N*batchSize (counts n) 0 1:ℕ):ℝ)*(((2*(N*batchSize (counts n) 0 1)+1:ℕ):ℝ)*b)≤1/2 ∧
      2*((2*(N*batchSize (counts n) 0 1)+1:ℕ):ℝ)*b≤cap ∧
      ((2*(N*batchSize (counts n) 0 1)+1:ℕ):ℝ≥0∞)*
        GenieProtocol.failurePerQuery (totalColumns (counts n) 0) r b=1/8 := by
  exact exists_source_observer_dimension (counts n) 0 1 (sourceHorizon (counts n) 0 p) D₀
    (energyCap R τ) (energyCap_positive hR hτ)

end Bilevel.SingleFrameSource
