import Bilevel.EndpointTransportSourceQuadraticCore
import Bilevel.ChiUpperNoiseUniformSource
import Bilevel.EndpointTransportQuadraticSourceProperty

/-! One depth-zero physical source family with paid upper budgets, full
accuracy window, exact original scalar mean geometry, gap and blind barrier.
The transport response and exact quadratic Primitive are assembled separately. -/
noncomputable section
open Filter
open scoped Topology
namespace Bilevel.EndpointTransportResponse
open ChiBoundedChain ChiRecursive ChiCarrier ChiOuter PrimitiveGeometry ChiExtensionCalibration ChiUpperNoise
set_option autoImplicit false

set_option maxHeartbeats 1400000 in
theorem source_quadratic_uniform_certificate : ∃ t η ζ cn CR Km Cgap C η₀ c : ℝ,
    0<t ∧ t<1 ∧ 0<η ∧ η≤1 ∧ 0<ζ ∧ ζ≤2/15 ∧ 0<cn ∧ cn≤1 ∧
    128≤cn/η^2 ∧ 1≤CR ∧ ζ*Real.sqrt cn≤CR ∧ 1≤Km ∧ 1≤Cgap ∧ 1≤C ∧
    0<η₀ ∧ η₀≤1 ∧ 0<c ∧ c≤1 ∧
    ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
      [FiniteDimensional ℝ E] (transport dim : ℕ) (L Δ ε K : ℝ),0<L → 0<Δ → 0<ε → 1/3≤K →
      ε≤c*min L (Real.sqrt (L*Δ)) →
      let ℓ := η₀*L
      let b := baseWidth (96/(t*η)) ε η₀ L
      let initial : Scale := ⟨ℓ,b⟩
      let n := macroIndex Δ Cgap (ℓ*b^2)
      128≤n ∧ η₀*L*Δ/(4*Cgap*(96/(t*η))^2*ε^2)≤(n:ℝ) ∧
      ∀ (U : Space n →ₗᵢ[ℝ] E)
        (V : ∀ j,List ℕ → Space (sourceChainIndex cn 1 (resolution η (max K (1/η)) j)) →ₗᵢ[ℝ] Block dim),
      let M : Node E := sourceMacroNode n initial Km U
      let D : Geometry (Block dim) := sourceGeometry initial (fun _ => 1) (resolution η (max K (1/η))) (fun j => t^(j+1)) 3 1 ζ cn CR V
      let R : ℕ → ℝ := fun j => (D j []).radius
      let ρ : ℕ → ℝ := fun j => t^(j+1)*(D j []).nu
      ∀ Q : Rotations transport dim,QuadraticSourceProperty Q M D ρ R L Δ ε ℓ b K (max K (1/η)) := by
  obtain ⟨t,η,ζ,cn,CR,Km,Cgap,ht,ht1,hη,hη1,hζ,hζsmall,hcn,hcn1,hlen,hCR,hCRcn,hKm,hCgap,hobjective⟩ :=
    source_independent_objective_certificate
  have hζ1 : ζ≤1 := by linarith only [hζsmall]
  obtain ⟨C,hC,hbudgets⟩ := source_quadratic_core_budgets 3 1 ζ cn CR Km (by norm_num) (by norm_num)
    hζ hζ1 hcn hcn1 hCR hCRcn hKm
  have hCg : 0<Cgap := by linarith only [hCgap]
  have hCb : 0<96/(t*η) := by positivity
  obtain ⟨η₀,c,hη₀,hη₀1,hc,hc1,hcal⟩ := direct_upper_calibration hC hCg hCb
  refine ⟨t,η,ζ,cn,CR,Km,Cgap,C,η₀,c,ht,ht1,hη,hη1,hζ,hζsmall,hcn,hcn1,hlen,hCR,hCRcn,hKm,hCgap,hC,
    hη₀,hη₀1,hc,hc1,?_⟩
  intro E _ _ _ _ transport dim L Δ ε K hL hΔ hε hKlow hacc
  dsimp only
  let ℓ := η₀*L
  let b := baseWidth (96/(t*η)) ε η₀ L
  let initial : Scale := ⟨ℓ,b⟩
  let n := macroIndex Δ Cgap (ℓ*b^2)
  have hell : 0<ℓ := mul_pos hη₀ hL
  have hK : 0<K := by linarith only [hKlow]
  have hKg : 0<max K (1/η) := hK.trans_le (le_max_left _ _)
  have hKth : 1/η≤max K (1/η) := le_max_right _ _
  obtain ⟨hb,hforce,hLf,hCf,hn,hgap,hcount⟩ := hcal L Δ ε hL hΔ hε hacc
  refine ⟨hn,hcount,?_⟩
  intro U V
  let M := sourceMacroNode n initial Km U
  let D := sourceGeometry initial (fun _ => 1) (resolution η (max K (1/η))) (fun j => t^(j+1)) 3 1 ζ cn CR V
  let R := fun j => (D j []).radius
  let ρ := fun j => t^(j+1)*(D j []).nu
  intro Q
  have hres := base_resolution_positive hη hKg
  have hresle := base_resolution_le hKg hKth hη
  have hres1 (j : ℕ) : resolution η (max K (1/η)) j≤1 := (hresle j).trans hη1
  have hlen' (j : ℕ) : 128≤cn/(resolution η (max K (1/η)) j)^2 := by
    apply hlen.trans
    exact div_le_div_of_nonneg_left hcn.le (sq_pos_of_pos (hres j))
      (pow_le_pow_left₀ (hres j).le (hresle j) 2)
  have hw (j : ℕ) : 0<t^(j+1) := pow_pos ht _
  have hw1 (j : ℕ) : t^(j+1)≤1 := pow_le_one₀ ht.le ht1.le
  have hbgt := hbudgets E transport dim n Q initial hell hb (fun _ => 1) (resolution η (max K (1/η))) (fun j => t^(j+1))
    (fun _ => le_rfl) rfl hres hres1 hlen' hw hw1 U V
  have he : (D 0 []).ell=ℓ := by change 1*ℓ=ℓ; ring
  have hwidth : (D 0 []).width=b/(max K (1/η)) := by
    change (1/(max K (1/η)))*b/1=b/(max K (1/η))
    ring
  have ho := hobjective E (Block dim) n initial hell hb (fun _ => 1) (fun _ => le_rfl) (max K (1/η)) hKg hKth U V K hK 0
  refine ⟨he,hwidth,?_,ho.1,ho.2.1,ho.2.2.1.trans hgap,?_⟩
  · intro z
    obtain ⟨hf,hg⟩ := hbgt z
    exact ⟨hf.trans hLf,hg.trans hCf⟩
  · intro z hz
    apply le_trans _ (ho.2.2.2 z hz)
    apply le_min
    · change 8*ε≤(ℓ*b)/4
      rw [hforce]
      have hprod : t*η≤1 := by
        have hh := mul_le_mul ht1.le hη1 hη.le (by norm_num : (0:ℝ)≤1)
        simpa only [one_mul] using hh
      have htCb : 32≤96/(t*η) := (le_div_iff₀ (mul_pos ht hη)).mpr (by linarith only [hprod])
      have hh := mul_le_mul_of_nonneg_right htCb hε.le
      linarith only [hh]
    · change 8*ε≤K*(t^(0+1)*(η^0*(ℓ*b))/4/(max K (1/η)))
      rw [hforce]
      have heq : K*(t^(0+1)*(η^0*((96/(t*η))*ε))/4/(max K (1/η)))=
          24*K*ε/(η*max K (1/η)) := by
        norm_num
        field_simp
        ring
      rw [heq]
      apply (le_div_iff₀ (mul_pos hη hKg)).mpr
      have hh := mul_le_mul_of_nonneg_right (ChiUpperNoise.truncated_gain_ratio hη hη1 hKlow) hε.le
      nlinarith only [hh]

end Bilevel.EndpointTransportResponse

