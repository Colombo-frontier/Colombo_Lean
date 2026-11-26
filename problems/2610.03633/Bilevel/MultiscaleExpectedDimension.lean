import Bilevel.MultiscaleExpectedProperty
import Bilevel.SingleFrameSourceDimension

/-! One public ambient dimension is selected before all algorithms and
frames. The only remaining premise is the actual deterministic barrier. -/
noncomputable section
set_option autoImplicit false
universe u v
namespace Bilevel.MultiscaleMean
open SingleFrameSource ChiHierarchyIndex ChiHierarchyHaar

theorem exists_inner_expected_dimension (n D₀ : ℕ) (R τ p ε : ℝ)
    (hR : 0<R) (hτ : 0<τ) (hp : 0<p) (hp1 : p≤1) (hε : 0<ε) :
    ∃ D : ℕ,∃ hD : ∀ i : FrameIndex (counts n) 0,chainSize i+1≤D,
      D₀≤D ∧ ∀ P : Parameters (E:=EuclideanGaussian.Space D) n,
      P.R=R → P.signalResolution=τ →
      (∀ a x,|WrappedChain.coordinates n P.R (frame hD a (Sum.inl ()))
        ((P.L/P.μ) • x) (Fin.last n)|<P.β → 8*ε≤ innerFrameLoss P hD a x) →
      InnerRateProperty.{u,v} P hD p hp1 ε (((n+1:ℕ):ℝ)/(512*p)) := by
  obtain ⟨D,r,b,hD₀,hD,hdim,_hr,hb,hb2,hproduct,henergy,hbudget⟩ :=
    SingleFrameSource.exists_dimension n D₀ R τ p hR hτ
  refine ⟨D,hD,hD₀,?_⟩
  intro P hPR hPτ hbarrier
  have hsmall : P.R*Real.sqrt (energyCap R τ)≤P.signalResolution/2 := by
    simpa only [hPR,hPτ] using energyCap_small hR hτ
  have hmax : ((n+1:ℕ):ℝ)/(16*p)≤(sourceHorizon (counts n) 0 p:ℝ) := by
    simpa only [Nat.zero_add,SingleFrameSource.capacity_eq] using sourceHorizon_bound (counts n) 0 p
  exact @inner_expected_property.{u,v} n D P p ε (energyCap R τ) hp hp1 hε
    (energyCap_positive hR hτ).le hsmall hD (sourceHorizon (counts n) 0 p) r b hmax
    hb hb2 hdim hproduct henergy (le_of_eq hbudget) hbarrier

end Bilevel.MultiscaleMean
