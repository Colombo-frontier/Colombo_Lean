import Bilevel.EndpointTransportSourceUpperBase
import Bilevel.ChiIndependentWidths

/-! Physical upper-base normalization is chosen before the extension
constants, uniformly over transport length, ambient dimension and accuracy. -/
noncomputable section
namespace Bilevel.EndpointTransportResponse
open ChiBoundedChain ChiRecursive ChiCarrier ChiOuter PrimitiveGeometry ChiIndependentWidths

theorem uniform_physical_upper_base_certificate (A K ζ cn CR Km Cgap : ℝ)
    (hA : 0≤A) (hK : 1≤K) (hζ : 0<ζ) (hζ1 : ζ≤1) (hcn : 0<cn) (hcn1 : cn≤1)
    (hCR : 1≤CR) (hCRcn : ζ*Real.sqrt cn≤CR) (hKm : 1≤Km) (hCgap : 1≤Cgap) :
    ∃ η₀ bStar : ℝ,0<η₀ ∧ η₀≤1 ∧ 0<bStar ∧ bStar≤1 ∧ bStar^2≤1/(256*Cgap) ∧
    ∀ (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
      (n dim nM : ℕ) (Q : Rotations n dim) (L Δ : ℝ),0<L → 0<Δ →
      ∀ (r η weight : ℕ → ℝ),(∀ j,1≤r j) → r 0=1 →
      (∀ j,0<η j) → (∀ j,η j≤1) → (∀ j,128≤cn/(η j)^2) →
      (∀ j,0<weight j) → (∀ j,weight j≤1) →
      ∀ (U : Space nM →ₗᵢ[ℝ] E)
        (V : ∀ j,List ℕ → Space (sourceChainIndex cn (r j) (η j)) →ₗᵢ[ℝ] Block dim),
      let initial : Scale := ⟨η₀*L,macroWidth bStar Δ (η₀*L)⟩
      let M := sourceMacroNode nM initial Km U
      let D := sourceGeometry initial r η weight A K ζ cn CR V
      let ρ := weight 0*(ζ*initial.curvature)
      let R := (D 0 []).radius
      ∀ (J m : ℕ) (z : PhysicalBase E m n dim),
      ‖iteratedFDeriv ℝ 2 (physicalUpperBase m Q M (initial.curvature/24) D J ρ R) z‖≤L/4 ∧
      ‖gradient (fun v => physicalUpperBase m Q M (initial.curvature/24) D J ρ R (pack z.fst v)) z.snd‖≤L/4 := by
  obtain ⟨C,hC,hbase⟩ := source_upper_physical_base_budgets A K ζ cn CR Km hA hK hζ hζ1 hcn hcn1 hCR hCRcn hKm
  let η₀ := 1/(4*C)
  let bStar := 1/(256*Cgap+1)
  have hCp : 0<C := by linarith
  have hCg : 0<Cgap := by linarith
  have hη₀ : 0<η₀ := by dsimp [η₀]; positivity
  have hη₀1 : η₀≤1 := by
    apply (div_le_one (by positivity : 0<4*C)).mpr
    linarith
  have hb : 0<bStar := by dsimp [bStar]; positivity
  have hb1 : bStar≤1 := by
    apply (div_le_one (by positivity : 0<256*Cgap+1)).mpr
    linarith
  have hbs : bStar^2≤1/(256*Cgap) := by
    have hbsq : bStar^2≤bStar := by nlinarith only [hb,hb1]
    apply hbsq.trans
    exact one_div_le_one_div_of_le (by positivity) (by linarith : 256*Cgap≤256*Cgap+1)
  refine ⟨η₀,bStar,hη₀,hη₀1,hb,hb1,hbs,?_⟩
  intro E _ _ _ n dim nM Q L Δ hL hΔ r η weight hr hr0 hη hη1 hlen hw hw1 U V
  dsimp only
  let initial : Scale := ⟨η₀*L,macroWidth bStar Δ (η₀*L)⟩
  have hinit := macroWidth_pos hb hΔ (mul_pos hη₀ hL)
  have hbnd : initial.width≤1 := (macroWidth_le hb.le).trans hb1
  have hh := hbase E n dim nM Q initial (mul_pos hη₀ hL) hinit r η weight hr hr0 hη hη1 hlen hw hw1 U V
  have he : C*initial.curvature=L/4 := by dsimp [initial,η₀]; field_simp; ring
  intro J m z
  have hu := hh J m z
  refine ⟨hu.1.trans_eq he,hu.2.trans ?_⟩
  unfold Scale.force
  have hm := mul_le_mul_of_nonneg_left hbnd (show 0≤C*initial.curvature by positivity)
  rw [he] at hm
  rw [← mul_assoc,he]
  simpa only [mul_one] using hm

end Bilevel.EndpointTransportResponse
