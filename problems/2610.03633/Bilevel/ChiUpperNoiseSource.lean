import Bilevel.ChiUpperNoiseGeometry
import Bilevel.ChiUpperNoiseCalibration
import Bilevel.ChiUniformOuterObjective

/-! One actual direct-upper family: shared source geometry, fixed flattened
inactive scalar, paid primitive budgets, gap and blind-frontier margin.
The conditioning gain exceeds a fixed construction threshold. -/
noncomputable section
open Filter
open scoped Topology
namespace Bilevel.ChiUpperNoise
open ChiBoundedChain ChiRecursive ChiCarrier ChiOuter PrimitiveGeometry ChiExtensionCalibration
universe u

set_option maxHeartbeats 1400000 in
theorem source_direct_upper_certificate : ∃ t η ζ cn CR Km Cgap C η₀ c : ℝ,
    0<t ∧ t<1 ∧ 0<η ∧ η≤1 ∧ 0<ζ ∧ ζ≤2/15 ∧ 0<cn ∧ cn≤1 ∧
    128≤cn/η^2 ∧ 1≤CR ∧ ζ*Real.sqrt cn≤CR ∧ 1≤Km ∧ 1≤Cgap ∧ 1≤C ∧
    0<η₀ ∧ η₀≤1 ∧ 0<c ∧ c≤1 ∧
    ∀ (E F : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
      [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
      [FiniteDimensional ℝ F] (L Δ ε K : ℝ),0<L → 0<Δ → 0<ε → 1/η≤K →
      ε≤c*min L (Real.sqrt (L*Δ)) →
      let ℓ := η₀*L
      let b := baseWidth (32/t) ε η₀ L
      let initial : Scale := ⟨ℓ,b⟩
      let n := macroIndex Δ Cgap (ℓ*b^2)
      128≤n ∧ η₀*L*Δ/(4*Cgap*(32/t)^2*ε^2)≤(n:ℝ) ∧
      ∀ (U : Space n →ₗᵢ[ℝ] E)
        (V : ∀ j,List ℕ → Space (sourceChainIndex cn 1 (resolution η K j)) →ₗᵢ[ℝ] F),
      let M := sourceMacroNode n initial Km U
      let D := sourceGeometry initial (fun _ => 1) (resolution η K) (fun j => t^(j+1)) 3 1 ζ cn CR V
      let R := fun j => (D j []).radius
      let ρ := fun j => t^(j+1)*(D j []).nu
      let f := core 1 M (ℓ/24) D ρ R
      let Ftrue := jointOuter 1 M (ℓ/24) D ρ R 0 K
      (D 0 []).ell=ℓ ∧ (D 0 []).width=b/K ∧
      (∀ z,‖iteratedFDeriv ℝ 2 f z‖≤L/4 ∧
        ‖gradient (fun u => f (pack z.fst u)) z.snd‖≤L/4 ∧
        ‖gradient (signal 1 M D) z‖≤C*(32/t)*ε/K) ∧
      Tendsto Ftrue (cocompact (Joint E (Blocks 1 F))) atTop ∧ Ftrue 0=0 ∧
      Ftrue 0-sInf (Set.range Ftrue)≤Δ ∧
      ∀ z,M.coordinates z.fst (Fin.last n)<b → 8*ε≤‖gradient Ftrue z‖ := by
  obtain ⟨t,η,ζ,cn,CR,Km,Cgap,ht,ht1,hη,hη1,hζ,hζsmall,hcn,hcn1,hlen,hCR,hCRcn,hKm,hCgap,hobjective⟩ :=
    source_independent_objective_certificate.{u}
  have hζ1 : ζ≤1 := by linarith only [hζsmall]
  obtain ⟨C,hC,hbudgets⟩ := source_core_budgets 3 1 ζ cn CR Km (by norm_num) (by norm_num)
    hζ hζ1 hcn hcn1 hCR hCRcn hKm
  have hCg : 0<Cgap := by linarith only [hCgap]
  have hCb : 0<32/t := by positivity
  obtain ⟨η₀,c,hη₀,hη₀1,hc,hc1,hcal⟩ := direct_upper_calibration hC hCg hCb
  refine ⟨t,η,ζ,cn,CR,Km,Cgap,C,η₀,c,ht,ht1,hη,hη1,hζ,hζsmall,hcn,hcn1,hlen,hCR,hCRcn,hKm,hCgap,hC,
    hη₀,hη₀1,hc,hc1,?_⟩
  intro E F _ _ _ _ _ _ _ _ L Δ ε K hL hΔ hε hKth hacc
  dsimp only
  let ℓ := η₀*L
  let b := baseWidth (32/t) ε η₀ L
  let initial : Scale := ⟨ℓ,b⟩
  let n := macroIndex Δ Cgap (ℓ*b^2)
  have hell : 0<ℓ := mul_pos hη₀ hL
  have hK : 0<K := (div_pos zero_lt_one hη).trans_le hKth
  obtain ⟨hb,hforce,hLf,hCf,hn,hgap,hcount⟩ := hcal L Δ ε hL hΔ hε hacc
  refine ⟨hn,hcount,?_⟩
  intro U V
  let M := sourceMacroNode n initial Km U
  let D := sourceGeometry initial (fun _ => 1) (resolution η K) (fun j => t^(j+1)) 3 1 ζ cn CR V
  let R := fun j => (D j []).radius
  let ρ := fun j => t^(j+1)*(D j []).nu
  have hres := base_resolution_positive hη hK
  have hresle := base_resolution_le hK hKth hη
  have hres1 (j : ℕ) : resolution η K j≤1 := (hresle j).trans hη1
  have hlen' (j : ℕ) : 128≤cn/(resolution η K j)^2 := by
    apply hlen.trans
    exact div_le_div_of_nonneg_left hcn.le (sq_pos_of_pos (hres j))
      (pow_le_pow_left₀ (hres j).le (hresle j) 2)
  have hw (j : ℕ) : 0<t^(j+1) := pow_pos ht _
  have hw1 (j : ℕ) : t^(j+1)≤1 := pow_le_one₀ ht.le ht1.le
  have hbgt := hbudgets E F n initial hell hb (fun _ => 1) (resolution η K) (fun j => t^(j+1))
    (fun _ => le_rfl) rfl hres hres1 hlen' hw hw1 U V 1
  have he : (D 0 []).ell=ℓ := by change 1*ℓ=ℓ; ring
  have hwidth : (D 0 []).width=b/K := by
    change (1/K)*b/1=b/K
    ring
  have ho := hobjective E F n initial hell hb (fun _ => 1) (fun _ => le_rfl) K hK hKth U V K hK 0
  refine ⟨he,hwidth,?_,ho.1,ho.2.1,ho.2.2.1.trans hgap,?_⟩
  · intro z
    obtain ⟨hf,hg,hs⟩ := hbgt z
    refine ⟨hf.trans hLf,hg.trans hCf,?_⟩
    rw [he,hwidth] at hs
    apply hs.trans_eq
    change C*(ℓ*(b/K))=C*(32/t)*ε/K
    rw [← mul_div_assoc,hforce]
    ring
  · intro z hz
    apply le_trans _ (ho.2.2.2 z hz)
    apply le_min
    · change 8*ε≤(ℓ*b)/4
      rw [hforce]
      have htCb : 32≤32/t := (le_div_iff₀ ht).mpr (by linarith only [ht1])
      have hh := mul_le_mul_of_nonneg_right htCb hε.le
      linarith only [hh]
    · change 8*ε≤K*(t^(0+1)*(η^0*(ℓ*b))/4/K)
      rw [hforce]
      apply le_of_eq
      norm_num
      field_simp
      ring

end Bilevel.ChiUpperNoise
