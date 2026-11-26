import Bilevel.ChiSourceFineExtension
import Bilevel.ChiFineSourceScales
import Bilevel.ChiSourcePhysicalScales

/-! Actual fine extension with the physical source scales. In the source
branch θ ≤ κ, the conservative square-root estimate already gives a
dimension-independent second-jet coefficient times the initial width. -/
noncomputable section
namespace Bilevel.ChiExtensionCalibration
open ChiBoundedChain ChiRecursive ChiCarrier ChiOuter PrimitiveGeometry ChiExtension ChiCurvatureSchedule

theorem scheduled_fine_extension_jets : ∃ B : ℝ,1 ≤ B ∧
    ∀ (E F : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
      [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
      (n : ℕ) (L μ θ η₀ b η κ T A Kminus ζ cn CR Km : ℝ) (weight : ℕ → ℝ),
      0 < L → 0 < μ → 0 ≤ θ → θ ≤ κ → 0 < η₀ → 0 < b → 0 < η → η ≤ 1 → 1 ≤ κ →
      1/η ≤ κ/6 → 1 ≤ T →
      (∀ j,0 < weight j) → (∀ j,weight j ≤ 1) → 1 ≤ Kminus → 0 < ζ → ζ ≤ 1 → 1 ≤ CR → 1 ≤ Km →
      ∀ (U : Space n →ₗᵢ[ℝ] E)
        (V : ∀ j,List ℕ → Space (sourceChainIndex cn (sourceRatio T j)
          (resolution η (κ/6) j)) →ₗᵢ[ℝ] F),
      let initial : Scale := ⟨η₀*L,b⟩
      let M := sourceMacroNode n initial Km U
      let D := sourceGeometry initial (sourceRatio T) (resolution η (κ/6)) weight A Kminus ζ cn CR V
      ∀ (J blocks normals : ℕ),1 ≤ J → ∀ (index : Fin normals) (c Cf Mpay : ℝ),
      0 < c → c ≤ 1/128 → 1 ≤ Mpay →
      Mpay*(max 1 (24*SmallGapLiftSupport.C/c^2)*B^2) ≤ Cf →
      let v := fineParameter (θ*μ) (3*μ/2) ((D J []).ell) (normalCoefficient L J) Cf J
      ∀ hv : 1 ≤ v, ∀ hc : 0 < c, ∀ hh : 0 < (D J []).width,
      let data := outerFineData blocks M D J c v hc hh hv
      ∀ z : Full (Joint E (Blocks blocks F)) normals,
      ‖iteratedFDeriv ℝ 1 (fun y => fineTerm normals index data y/normalCoefficient L J) z‖ ≤
        24*SmallGapLiftSupport.C*B^(J+2)*η₀*Real.sqrt (2*(J:ℝ))*b^2/(κ/6)^2 ∧
      ‖iteratedFDeriv ℝ 2 (fun y => fineTerm normals index data y/normalCoefficient L J) z‖ ≤
        48*SmallGapLiftSupport.C*B^(J+2)*b/c ∧
      ‖iteratedFDeriv ℝ 3 (fun y => fineTerm normals index data y/normalCoefficient L J) z‖ ≤
        2*θ/(3*Mpay) := by
  obtain ⟨B,hB,hjet⟩ := source_fine_extension_budget
  refine ⟨B,hB,?_⟩
  intro E F _ _ _ _ _ _ n L μ θ η₀ b η κ T A Kminus ζ cn CR Km weight
    hL hμ hθ hθκ hη₀ hb hη hη1 hκ hthreshold hT hw hw1 hKminus hζ hζ1 hCR hKm U V
  dsimp only
  let initial : Scale := ⟨η₀*L,b⟩
  let M := sourceMacroNode n initial Km U
  let D := sourceGeometry initial (sourceRatio T) (resolution η (κ/6)) weight A Kminus ζ cn CR V
  have hκp : 0 < κ := by linarith
  have hK : 0 < κ/6 := by positivity
  have hr := sourceRatio_ge_one hT
  have hres := base_resolution_positive hη hK
  have hres1 (j : ℕ) : resolution η (κ/6) j ≤ 1 := (base_resolution_le hK hthreshold hη j).trans hη1
  intro J blocks normals hJ index c Cf Mpay hc hcs hMpay hCf hv hc' hh z
  have hell : (D J []).ell = η₀*L*curvature T J := by
    obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show J ≠ 0 by omega)
    exact source_high_node_curvature initial (by linarith) η (κ/6) j
  have hwidth : (D J []).width = η^J*b/((κ/6)*curvature T J) := by
    obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show J ≠ 0 by omega)
    exact source_parent_width initial hT (mul_pos hη₀ hL) η (κ/6) (j+1)
  have hraw := hjet E F n initial (mul_pos hη₀ hL) hb (sourceRatio T) (resolution η (κ/6)) weight
    A Kminus ζ cn CR Km hr hres hres1 hw hw1 hKminus hζ hζ1 hCR hKm U V
    J blocks normals index c (θ*μ) (3*μ/2) (normalCoefficient L J) Cf Mpay hc hcs
    (mul_nonneg hθ hμ.le) (by positivity) (normalCoefficient_pos hL hJ) hMpay hCf hv hc' hh z
  have hB0 : 0 ≤ B := by linarith
  have hC := SmallGapLiftSupport.C_pos
  have hbase : 1 ≤ max 1 (24*SmallGapLiftSupport.C/c^2)*B^2 :=
    one_le_mul_of_one_le_of_one_le (le_max_left _ _) (one_le_pow₀ hB)
  have hCf1 : 1 ≤ Cf := (one_le_mul_of_one_le_of_one_le hMpay hbase).trans hCf
  have ha : 1 ≤ curvature T J := (curvature_bounds hT J).1
  have hv' : 1 ≤ fineParameter (θ*μ) (3*μ/2) (η₀*L*curvature T J) (normalCoefficient L J) Cf J := by
    have hh' : 1 ≤ fineParameter (θ*μ) (3*μ/2) ((D J []).ell) (normalCoefficient L J) Cf J := hv
    rwa [hell] at hh'
  refine ⟨hraw.1.trans ?_,hraw.2.1.trans ?_,hraw.2.2.trans_eq ?_⟩
  · change 6*SmallGapLiftSupport.C*B^(J+2)*(D J []).ell*((D J []).width)^2/normalCoefficient L J ≤ _
    rw [hell,hwidth]
    have he := mul_le_mul_of_nonneg_left (fine_source_energy_scale (b:=b) hL hη₀.le hη.le hη1 hK ha J)
      (show 0 ≤ 6*SmallGapLiftSupport.C*B^(J+2) by positivity)
    convert he using 1 <;> ring
  · change 12*SmallGapLiftSupport.C*B^(J+2)*(D J []).ell*(D J []).width*
      Real.sqrt (fineParameter (θ*μ) (3*μ/2) ((D J []).ell) (normalCoefficient L J) Cf J)/c/normalCoefficient L J ≤ _
    rw [hell,hwidth]
    have hs := fine_source_second_scale hθ hμ hL hη₀ hη.le hη1 hb.le hK ha hCf1 J hJ hv'
    have hscale : 2*θ*b/(3*(κ/6)) ≤ 4*b := by
      apply (div_le_iff₀ (show 0 < 3*(κ/6) by positivity)).mpr
      have hm := mul_le_mul_of_nonneg_right hθκ hb.le
      nlinarith only [hm]
    have he := mul_le_mul_of_nonneg_left (hs.trans hscale)
      (show 0 ≤ 12*SmallGapLiftSupport.C*B^(J+2)/c by positivity)
    convert he using 1 <;> ring
  · field_simp
    ring

end Bilevel.ChiExtensionCalibration
