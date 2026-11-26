import Bilevel.ChiSourceFineExtension
import Bilevel.ChiSourcePhysicalScales
import Bilevel.ChiUniformPhysicalBudgets

/-! Actual fine extension on the full accuracy range. The base width
ratio and response gain are independent; the exact fine parameter pays
the third derivative and the squared depth cancellation pays the Hessian. -/
noncomputable section
namespace Bilevel.ChiExtensionCalibration
open ChiBoundedChain ChiRecursive ChiCarrier ChiOuter PrimitiveGeometry ChiExtension ChiCurvatureSchedule ChiIndependentWidths

theorem wide_fine_extension_jets : ∃ B : ℝ,1≤B ∧
    ∀ (E F : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
      [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
      (n J : ℕ) (L μ θ κ η₀ b η t Cb ε Kg T A Kminus ζ cn CR Km : ℝ) (weight : ℕ → ℝ),
      0<L → 0<μ → 0≤θ → θ≤κ^2 → 0<κ → 0<η₀ → 0<b → 0<η → η≤1 →
      0<t → t≤1 → 0≤Cb → 0≤ε → 0<Kg → 1/η≤Kg → 1≤T → 1≤J →
      b/Kg=middleWidth Cb ε (κ/6) (η₀*L) (t*η) J →
      (∀ j,0<weight j) → (∀ j,weight j≤1) → 1≤Kminus → 0<ζ → ζ≤1 → 1≤CR → 1≤Km →
      ∀ (U : Space n →ₗᵢ[ℝ] E)
        (V : ∀ j,List ℕ → Space (sourceChainIndex cn (sourceRatio T j) (resolution η Kg j)) →ₗᵢ[ℝ] F),
      let initial : Scale := ⟨η₀*L,b⟩
      let M := sourceMacroNode n initial Km U
      let D := sourceGeometry initial (sourceRatio T) (resolution η Kg) weight A Kminus ζ cn CR V
      ∀ (blocks normals : ℕ) (index : Fin normals) (cms Cf Mpay : ℝ),
      0<cms → cms≤1/128 → 1≤Mpay →
      Mpay*(max 1 (24*SmallGapLiftSupport.C/cms^2)*B^2)≤Cf → 4*(B^2/t)^2≤Cf →
      let v := fineParameter (θ*μ) (3*μ/2) ((D J []).ell) (normalCoefficient L J) Cf J
      ∀ hv : 1≤v, ∀ hc : 0<cms, ∀ hh : 0<(D J []).width,
      let data := outerFineData blocks M D J cms v hc hh hv
      ∀ z : Full (Joint E (Blocks blocks F)) normals,
      ‖iteratedFDeriv ℝ 2 (fun y => fineTerm normals index data y/normalCoefficient L J) z‖≤
        (576*SmallGapLiftSupport.C*Cb/(cms*Real.sqrt (6*η₀)))*(ε/L) ∧
      ‖iteratedFDeriv ℝ 3 (fun y => fineTerm normals index data y/normalCoefficient L J) z‖≤
        2*θ/(3*Mpay) := by
  obtain ⟨B,hB,hjet⟩ := source_fine_extension_budget
  refine ⟨B,hB,?_⟩
  intro E F _ _ _ _ _ _ n J L μ θ κ η₀ b η t Cb ε Kg T A Kminus ζ cn CR Km weight
    hL hμ hθ hθκ hκ hη₀ hb hη hη1 ht ht1 hCb hε hK hthreshold hT hJ hwidthGain
    hw hw1 hKminus hζ hζ1 hCR hKm U V
  dsimp only
  let initial : Scale := ⟨η₀*L,b⟩
  let D := sourceGeometry initial (sourceRatio T) (resolution η Kg) weight A Kminus ζ cn CR V
  have hr := sourceRatio_ge_one hT
  have hres := base_resolution_positive hη hK
  have hres1 (j : ℕ) : resolution η Kg j≤1 := (base_resolution_le hK hthreshold hη j).trans hη1
  intro blocks normals index cms Cf Mpay hc hcs hMpay hCf hCfWide hv hc' hh z
  have hell : (D J []).ell=η₀*L*curvature T J := by
    obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show J≠0 by omega)
    exact source_high_node_curvature initial (by linarith) η Kg j
  have hwidth0 : (D J []).width=η^J*b/(Kg*curvature T J) := by
    obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show J≠0 by omega)
    exact source_parent_width initial hT (mul_pos hη₀ hL) η Kg (j+1)
  have hwidth : (D J []).width=
      η^J*middleWidth Cb ε (κ/6) (η₀*L) (t*η) J/curvature T J := by
    rw [hwidth0,← hwidthGain]
    ring
  have hraw := hjet E F n initial (mul_pos hη₀ hL) hb (sourceRatio T) (resolution η Kg) weight
    A Kminus ζ cn CR Km hr hres hres1 hw hw1 hKminus hζ hζ1 hCR hKm U V
    J blocks normals index cms (θ*μ) (3*μ/2) (normalCoefficient L J) Cf Mpay hc hcs
    (mul_nonneg hθ hμ.le) (by positivity) (normalCoefficient_pos hL hJ) hMpay hCf hv hc' hh z
  have hbase : 1≤max 1 (24*SmallGapLiftSupport.C/cms^2)*B^2 :=
    one_le_mul_of_one_le_of_one_le (le_max_left _ _) (one_le_pow₀ hB)
  have hCfpos : 0<Cf := lt_of_lt_of_le zero_lt_one
    ((one_le_mul_of_one_le_of_one_le hMpay hbase).trans hCf)
  have hs := wide_fine_hessian_factor hL hμ hη₀ hCb hε hκ hθ hθκ
    (curvature_bounds hT J).1 hB ht ht1 hη hCfpos hCfWide J hJ
  refine ⟨hraw.2.1.trans ?_,hraw.2.2.trans_eq ?_⟩
  · change 12*SmallGapLiftSupport.C*B^(J+2)*(D J []).ell*(D J []).width*
      Real.sqrt (fineParameter (θ*μ) (3*μ/2) ((D J []).ell) (normalCoefficient L J) Cf J)/cms/
      normalCoefficient L J≤_
    rw [hell,hwidth]
    have hCP := SmallGapLiftSupport.C_pos
    have hm := mul_le_mul_of_nonneg_left hs (show 0≤12*SmallGapLiftSupport.C/cms by positivity)
    convert hm using 1 <;> ring
  · field_simp
    ring

end Bilevel.ChiExtensionCalibration
