import Bilevel.EndpointTransportQuadraticRate
import Bilevel.TransportQuadraticExpectedProperty

/-! The actual observer advances after m = layers-1 original calls.
The source arithmetic used layers, so a factor two is explicitly paid. -/
noncomputable section
namespace Bilevel.TransportHierarchy
open ChiHierarchyIndex ChiTreeProgress ChiBoundedChain ChiRecursive ChiExtensionCalibration ChiUpperNoise EndpointTransportNormalization
set_option autoImplicit false

theorem quadratic_expected_count_lower {η η₀ L Δ Cgap Cb ε cn κ : ℝ} {macroN : ℕ}
    (hη : 0<η) (hη₀ : 0<η₀) (hL : 0<L) (hΔ : 0<Δ) (hCg : 0<Cgap) (hCb : 0<Cb)
    (hε : 0<ε) (hcn : 0<cn) (hκ : 3200≤κ) (hlen : 128≤cn/η^2)
    (hn : η₀*L*Δ/(4*Cgap*Cb^2*ε^2)≤(macroN:ℝ))
    (hsize : sourceChainIndex cn 1 (1/max (gain κ) (1/η))+1=microLength cn (max (gain κ) (1/η))) :
    ((cn*η₀/(8*Cgap*Cb^2*192^2*2*Real.sqrt 128))/1024)*L*κ^2*Real.sqrt κ*Δ/ε^2≤
      (((interiors κ+1)*capacity (sourceCounts macroN cn (fun _ => 1) (resolution η (max (gain κ) (1/η)))) 1 0:ℕ):ℝ)/512 := by
  have hcap : capacity (sourceCounts macroN cn (fun _ => 1) (resolution η (max (gain κ) (1/η)))) 1 0=
      (macroN+1)*microLength cn (max (gain κ) (1/η)) := by
    change (macroN+1)*(sourceChainIndex cn 1 (1/max (gain κ) (1/η))+1)=_
    rw [hsize]
  have hlayer : layers κ≤2*(interiors κ+1) := by
    have hh := interiors_add_two hκ
    have h5 := layers_ge_five hκ
    omega
  have hmul := Nat.mul_le_mul_right ((macroN+1)*microLength cn (max (gain κ) (1/η))) hlayer
  have hr := quadratic_transport_count_lower hη hη₀ hL hΔ hCg hCb hε hcn hκ hlen hn
  rw [hcap]
  have hmr : ((layers κ*((macroN+1)*microLength cn (max (gain κ) (1/η))):ℕ):ℝ)≤
      2*(((interiors κ+1)*((macroN+1)*microLength cn (max (gain κ) (1/η))):ℕ):ℝ) := by
    exact_mod_cast (show layers κ*((macroN+1)*microLength cn (max (gain κ) (1/η)))≤
      2*((interiors κ+1)*((macroN+1)*microLength cn (max (gain κ) (1/η)))) by
        simpa only [Nat.mul_assoc] using hmul)
  have hh := div_le_div_of_nonneg_right (hr.trans hmr) (by norm_num : (0:ℝ)≤1024)
  convert hh using 1 <;> ring

end Bilevel.TransportHierarchy
