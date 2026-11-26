import Bilevel.EndpointTransportSourceFineBudget
import Bilevel.ChiUniformFineExtension

/-! Actual physical fine extension at the independent source scales.
The full theta <= kappa^2 range is preserved in the numerical cancellation. -/
noncomputable section
namespace Bilevel.EndpointTransportResponse
open ChiBoundedChain ChiRecursive ChiCarrier ChiOuter PrimitiveGeometry ChiExtension ChiExtensionCalibration ChiCurvatureSchedule ChiIndependentWidths

theorem wide_physical_fine_extension_jets : ∃ B : ℝ,1≤B ∧
    ∀ (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
      (n J transport dim : ℕ) (Q : Rotations transport dim)
      (L μ θ κ η₀ b η t Cb ε Kg T Ar Kminus ζ cn CR Km : ℝ) (weight : ℕ → ℝ),
      0<L → 0<μ → 0≤θ → θ≤κ^2 → 0<κ → 0<η₀ → 0<b → 0<η → η≤1 →
      0<t → t≤1 → 0≤Cb → 0≤ε → 0<Kg → 1/η≤Kg → 1≤T → 1≤J →
      b/Kg=middleWidth Cb ε (κ/6) (η₀*L) (t*η) J →
      (∀ j,0<weight j) → (∀ j,weight j≤1) → 1≤Kminus → 0<ζ → ζ≤1 → 1≤CR → 1≤Km →
      ∀ (U : Space n →ₗᵢ[ℝ] E)
        (V : ∀ j,List ℕ → Space (sourceChainIndex cn (sourceRatio T j) (resolution η Kg j)) →ₗᵢ[ℝ] Block dim),
      let initial : Scale := ⟨η₀*L,b⟩
      let M := sourceMacroNode n initial Km U
      let G := sourceGeometry initial (sourceRatio T) (resolution η Kg) weight Ar Kminus ζ cn CR V
      ∀ (normals : ℕ) (P : ChiFine.Parameters),P.ℓ=(G J []).ell → P.β=(G J []).width →
      ∀ (index : Fin normals) (Cf Mpay : ℝ),1≤Mpay →
      Mpay*(max 1 (24*SmallGapLiftSupport.C/P.c^2)*B^2)≤Cf → 4*(B^2/t)^2≤Cf →
      P.θ=fineParameter (θ*μ) (3*μ/2) P.ℓ (normalCoefficient L J) Cf J →
      ∀ z : Full (PhysicalBase E J transport dim) normals,
      let data := physicalHierarchyFine Q M G P J
      ‖iteratedFDeriv ℝ 2 (fun y => fineTerm normals index data y/normalCoefficient L J) z‖≤
        (576*SmallGapLiftSupport.C*Cb/(P.c*Real.sqrt (6*η₀)))*(ε/L) ∧
      ‖iteratedFDeriv ℝ 3 (fun y => fineTerm normals index data y/normalCoefficient L J) z‖≤2*θ/(3*Mpay) := by
  obtain ⟨B,hB,hjet⟩ := source_physical_fine_extension_budget
  refine ⟨B,hB,?_⟩
  intro E _ _ _ n J transport dim Q L μ θ κ η₀ b η t Cb ε Kg T Ar Kminus ζ cn CR Km weight
    hL hμ hθ hθκ hκ hη₀ hb hη hη1 ht ht1 hCb hε hK hthreshold hT hJ hwidthGain
    hw hw1 hKminus hζ hζ1 hCR hKm U V
  dsimp only
  let initial : Scale := ⟨η₀*L,b⟩
  let G := sourceGeometry initial (sourceRatio T) (resolution η Kg) weight Ar Kminus ζ cn CR V
  have hr := sourceRatio_ge_one hT
  have hres := base_resolution_positive hη hK
  have hres1 (j : ℕ) : resolution η Kg j≤1 := (base_resolution_le hK hthreshold hη j).trans hη1
  intro normals P hℓP hβP index Cf Mpay hMpay hCf hCfWide hv z
  have hell : (G J []).ell=η₀*L*curvature T J := by
    obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show J≠0 by omega)
    exact source_high_node_curvature initial (by linarith) η Kg j
  have hwidth0 : (G J []).width=η^J*b/(Kg*curvature T J) := by
    obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show J≠0 by omega)
    exact source_parent_width initial hT (mul_pos hη₀ hL) η Kg (j+1)
  have hwidth : (G J []).width=η^J*middleWidth Cb ε (κ/6) (η₀*L) (t*η) J/curvature T J := by
    rw [hwidth0,← hwidthGain]
    ring
  have hraw := hjet E n transport dim Q initial (mul_pos hη₀ hL) hb (sourceRatio T) (resolution η Kg) weight
    Ar Kminus ζ cn CR Km hr hres hres1 hw hw1 hKminus hζ hζ1 hCR hKm U V
    J normals P hℓP hβP index (θ*μ) (3*μ/2) (normalCoefficient L J) Cf Mpay
    (mul_nonneg hθ hμ.le) (by positivity) (normalCoefficient_pos hL hJ) hMpay hCf hv z
  have hbase : 1≤max 1 (24*SmallGapLiftSupport.C/P.c^2)*B^2 :=
    one_le_mul_of_one_le_of_one_le (le_max_left _ _) (one_le_pow₀ hB)
  have hCfpos : 0<Cf := lt_of_lt_of_le zero_lt_one
    ((one_le_mul_of_one_le_of_one_le hMpay hbase).trans hCf)
  have hs := wide_fine_hessian_factor hL hμ hη₀ hCb hε hκ hθ hθκ
    (curvature_bounds hT J).1 hB ht ht1 hη hCfpos hCfWide J hJ
  refine ⟨hraw.2.1.trans ?_,hraw.2.2.trans_eq ?_⟩
  · rw [hv,hℓP,hβP,hell,hwidth]
    have hCP := SmallGapLiftSupport.C_pos
    have hc := P.c_pos
    have hm := mul_le_mul_of_nonneg_left hs (show 0≤12*SmallGapLiftSupport.C/P.c by positivity)
    convert hm using 1 <;> ring
  · field_simp
    ring

end Bilevel.EndpointTransportResponse
