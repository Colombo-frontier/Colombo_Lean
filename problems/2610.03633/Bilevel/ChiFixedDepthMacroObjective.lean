import Bilevel.ChiFixedDepthWidth
import Bilevel.ChiUniformMacroObjective
import Bilevel.ChiUniformOuterObjective
import Bilevel.ChiSourcePhysicalScales

/-! Actual independent-width recursive objective on the manuscript's full
accuracy window. This is a deterministic objective certificate, not a
primitive or stochastic information lower bound. -/
noncomputable section
open Filter
open scoped Topology
namespace Bilevel.ChiIndependentWidths
open ChiBoundedChain ChiRecursive ChiCarrier ChiOuter PrimitiveGeometry ChiExtensionCalibration
universe u

set_option maxHeartbeats 1000000 in
theorem fixed_macro_objective_certificate : ∃ t η ζ cn CR Km Cgap : ℝ,
    0<t ∧ t<1 ∧ 0<η ∧ η≤1 ∧ 0<ζ ∧ ζ≤2/15 ∧ 0<cn ∧ cn≤1 ∧
    128≤cn/η^2 ∧ 1≤CR ∧ ζ*Real.sqrt cn≤CR ∧ 1≤Km ∧ 1≤Cgap ∧
    ∀ η₀ bStar cold : ℝ,0<η₀ → η₀≤1 → 0<bStar → bStar^2≤1/(256*Cgap) → 0<cold →
    ∃ c : ℝ,0<c ∧ c≤1 ∧ c≤cold ∧
    ∀ (E F : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
      [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
      [FiniteDimensional ℝ F] (L Δ κ ε : ℝ),
      0<L → 0<Δ → 2≤κ → 0<ε →
      ε≤c*min L (Real.sqrt (L*Δ)) →
      let J := (1:ℕ)
      let b := macroWidth bStar Δ (η₀*L)
      let h := middleWidth (32/t) ε (κ/6) (η₀*L) (t*η) J
      let S := macroLength (1/(2*Cgap)) Δ (η₀*L) b
      let n := S-1
      let Kg := b/h
      let initial : Scale := ⟨η₀*L,b⟩
      64≤S ∧ n+1=S ∧ 64≤middleLength cn b h ∧ 0<h/b ∧ h/b≤η ∧
      cn*Δ/(8*Cgap*(η₀*L)*h^2)≤((S*middleLength cn b h:ℕ):ℝ) ∧
      ∀ (U : Space n →ₗᵢ[ℝ] E)
        (V : ∀ j,List ℕ → Space (sourceChainIndex cn (sourceRatio 1 j) (resolution η Kg j)) →ₗᵢ[ℝ] F),
      let M := sourceMacroNode n initial Km U
      let weight := fun j => t^(j+1)
      let D := sourceGeometry initial (sourceRatio 1) (resolution η Kg) weight 3 1 ζ cn CR V
      let R := fun j => (D j []).radius
      let ρ := fun j => weight j*(ζ*(parentScale initial (sourceRatio 1) (resolution η Kg) j).curvature)
      let f := jointOuter (J+1) M (initial.curvature/24) D ρ R J (κ/6)
      Tendsto f (cocompact (Joint E (Blocks (J+1) F))) atTop ∧ f 0=0 ∧
      f 0-sInf (Set.range f)≤Δ ∧
      ∀ z,M.coordinates z.fst (Fin.last n)<b → 8*ε≤‖gradient f z‖ := by
  obtain ⟨t,η,ζ,cn,CR,Km,Cgap,ht,ht1,hη,hη1,hζ,hζ1,hcn,hcn1,hlen,hCR,hCRcn,hKm,hCgap,hshared⟩ :=
    source_independent_objective_certificate.{u}
  refine ⟨t,η,ζ,cn,CR,Km,Cgap,ht,ht1,hη,hη1,hζ,hζ1,hcn,hcn1,hlen,hCR,hCRcn,hKm,hCgap,?_⟩
  intro η₀ bStar cold hη₀ hη₀1 hbStar hbsmall hcold
  have hCg : 0<Cgap := by linarith
  have hCb : 0<32/t := by positivity
  have hmacro : bStar^2≤(1/(2*Cgap))/128 := by convert hbsmall using 1; ring
  obtain ⟨c,hc,hc1,hccold,hcal⟩ := exists_fixed_width_calibration hη₀ hη₀1 hbStar hcn hCb ht hη hη
    (by norm_num : (0:ℝ)<1/32) hcold hmacro
  refine ⟨c,hc,hc1,hccold,?_⟩
  intro E F _ _ _ _ _ _ _ _ L Δ κ ε hL hΔ hκ hε hacc
  dsimp only
  let J := (1:ℕ)
  let b := macroWidth bStar Δ (η₀*L)
  let h := middleWidth (32/t) ε (κ/6) (η₀*L) (t*η) J
  let S := macroLength (1/(2*Cgap)) Δ (η₀*L) b
  let n := S-1
  let Kg := b/h
  let initial : Scale := ⟨η₀*L,b⟩
  have hK : 0<κ/6 := by linarith
  have hbp : 0<b := macroWidth_pos hbStar hΔ (mul_pos hη₀ hL)
  have hhp : 0<h := by dsimp [h,middleWidth]; positivity
  have hw := hcal L Δ κ ε hL hΔ hκ hε hacc
  change 0<h/b ∧ h/b≤η ∧ ε≤(1/32)*(η₀*L)*b ∧ 64≤S ∧
    64≤middleLength cn b h ∧ _ at hw
  obtain ⟨hrpos,hr,hεmacro,hS,hn,hcount⟩ := hw
  have hSn : n+1=S := by dsimp [n]; omega
  refine ⟨hS,hSn,hn,hrpos,hr,?_,?_⟩
  · convert hcount using 1
    ring
  intro U V
  have hKg : 0<Kg := div_pos hbp hhp
  have hKgη : 1/η≤Kg := by
    apply (div_le_iff₀ hη).mpr
    have hh := (div_le_iff₀ hbp).mp hr
    dsimp [Kg]
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hhp).mpr
    nlinarith only [hh]
  have ho := hshared E F n initial (mul_pos hη₀ hL) hbp (sourceRatio 1)
    (sourceRatio_ge_one le_rfl) Kg hKg hKgη U V (κ/6) hK J
  have hgap : Cgap*((n:ℝ)+1)*initial.energy≤Δ := by
    have harg : 0≤(1/(2*Cgap))*Δ/((η₀*L)*b^2) := by positivity
    have hf : (S:ℝ)≤(1/(2*Cgap))*Δ/((η₀*L)*b^2) := Nat.floor_le harg
    have hm := mul_le_mul_of_nonneg_right hf (show 0≤Cgap*((η₀*L)*b^2) by positivity)
    have he : ((1/(2*Cgap))*Δ/((η₀*L)*b^2))*(Cgap*((η₀*L)*b^2))=Δ/2 := by
      field_simp
      ring
    rw [he] at hm
    have hncast : (n:ℝ)+1=(S:ℝ) := by exact_mod_cast hSn
    change Cgap*((n:ℝ)+1)*((η₀*L)*b^2)≤Δ
    rw [hncast]
    nlinarith only [hm,hΔ]
  refine ⟨ho.1,ho.2.1,ho.2.2.1.trans hgap,?_⟩
  intro z hlast
  apply le_trans _ (ho.2.2.2 z hlast)
  apply le_min
  · change 8*ε≤((η₀*L)*b)/4
    linarith only [hεmacro]
  · change 8*ε≤(κ/6)*(t^(J+1)*(η^J*((η₀*L)*b))/4/(b/h))
    rw [independent_margin_exact J hK (mul_pos hη₀ hL) ht hη hbp]
    have he : t*(32/t)*ε/4=8*ε := by field_simp; ring
    rw [he]

end Bilevel.ChiIndependentWidths

