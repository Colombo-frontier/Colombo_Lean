import Bilevel.ChiSourceCoarseExtension
import Bilevel.ChiScheduledNodeScales
import Bilevel.ChiScheduledCoarseSums

/-! Actual coarse normal extension with the source curvature schedule.
The carrier ledger and every node scale are discharged in the conclusions. -/
noncomputable section
namespace Bilevel.ChiExtensionCalibration
open ChiBoundedChain ChiRecursive ChiCarrier ChiOuter PrimitiveGeometry ChiExtension

theorem scheduled_coarse_extension_jets (A Kminus ζ cn : ℝ)
    (hA : 0 ≤ A) (hKm : 1 ≤ Kminus) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1)
    (hcn : 0 < cn) (hcn1 : cn ≤ 1) :
    ∃ C : ℝ,1 ≤ C ∧
    ∀ (E F : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
      [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
      (n : ℕ) (L η₀ b η κ T CR Km : ℝ) (weight : ℕ → ℝ),
      0 < L → 0 < η₀ → 0 < b → 0 < η → η ≤ 1 → η^2 ≤ 1/2 → 1 ≤ κ →
      1/η ≤ κ/6 → 1 ≤ T → T ≤ κ → 128 ≤ cn/η^2 →
      (∀ j,0 < weight j) → (∀ j,weight j ≤ 1) → 1 ≤ CR → ζ*Real.sqrt cn ≤ CR → 1 ≤ Km →
      ∀ (U : Space n →ₗᵢ[ℝ] E)
        (V : ∀ j,List ℕ → Space (sourceChainIndex cn (sourceRatio T j)
          (resolution η (κ/6) j)) →ₗᵢ[ℝ] F),
      let initial : Scale := ⟨η₀*L,b⟩
      let M := sourceMacroNode n initial Km U
      let D := sourceGeometry initial (sourceRatio T) (resolution η (κ/6)) weight A Kminus ζ cn CR V
      ∀ (J blocks normals : ℕ),1 ≤ J → ∀ (index : Fin J → Fin normals)
        (z : Full (Joint E (Blocks blocks F)) normals),
      ‖iteratedFDeriv ℝ 1 (sourceCoarseExtension blocks normals M D J index (normalCoefficient L J)) z‖ ≤
        16*SmallGapLiftSupport.C*C^(J+2)*cn*η₀*Real.sqrt (2*(J:ℝ))*b^2/(κ/6)^2 ∧
      ‖iteratedFDeriv ℝ 2 (sourceCoarseExtension blocks normals M D J index (normalCoefficient L J)) z‖ ≤
        192*SmallGapLiftSupport.C*C^(J+2)*η₀*b*(cn/η^2)*((J:ℝ)+1)^2 ∧
      ‖iteratedFDeriv ℝ 3 (sourceCoarseExtension blocks normals M D J index (normalCoefficient L J)) z‖ ≤
        64*SmallGapLiftSupport.C*C^(J+2)*η₀*(cn/η^2)^(1/3:ℝ)*((J:ℝ)+1)^2*T := by
  obtain ⟨C,hC,hjet⟩ := source_coarse_extension_jets A Kminus ζ cn hA hKm hζ hζ1 hcn hcn1
  refine ⟨C,hC,?_⟩
  intro E F _ _ _ _ _ _ n L η₀ b η κ T CR Km weight hL hη₀ hb hη hη1 hηsq hκ hthreshold
    hT hTκ hlen hw hw1 hCR hCRcn hKm' U V
  dsimp only
  let initial : Scale := ⟨η₀*L,b⟩
  let D := sourceGeometry initial (sourceRatio T) (resolution η (κ/6)) weight A Kminus ζ cn CR V
  have hκp : 0 < κ := by linarith
  have hK : 0 < κ/6 := by positivity
  have hr := sourceRatio_ge_one hT
  have hres := base_resolution_positive hη hK
  have hresle := base_resolution_le hK hthreshold hη
  have hres1 (j : ℕ) : resolution η (κ/6) j ≤ 1 := (hresle j).trans hη1
  have hreslen (j : ℕ) : 128 ≤ cn/(resolution η (κ/6) j)^2 := by
    apply hlen.trans
    apply div_le_div_of_nonneg_left hcn.le (sq_pos_of_pos (hres j))
    nlinarith [hresle j,hres j]
  intro J blocks normals hJ index z
  have hj := hjet E F n initial (mul_pos hη₀ hL) hb (sourceRatio T) (resolution η (κ/6)) weight
    CR Km hr hres hres1 hreslen hw hw1 hCR hCRcn hKm' U V J blocks normals index
    (normalCoefficient L J) (normalCoefficient_pos hL hJ) z
  have hsc (i : Fin J) := source_high_node_scales initial T η (κ/6) weight A Kminus ζ cn CR V
    (mul_pos hη₀ hL) hT hη hcn hlen i.val []
  have hN (i : Fin J) : ((D (i.val+1) []).n:ℝ)+1 = (ChiCurvatureSchedule.length cn η T i.val:ℝ) := by
    exact_mod_cast (hsc i).1
  have hell (i : Fin J) : (D (i.val+1) []).ell = η₀*L*ChiCurvatureSchedule.curvature T (i.val+1) :=
    (hsc i).2.1
  have hwidth (i : Fin J) : (D (i.val+1) []).width =
      η^(i.val+1)*b/((κ/6)*ChiCurvatureSchedule.curvature T (i.val+1)) := (hsc i).2.2
  change _ ≤ _ ∧ _ ≤ _ ∧ _ ≤ _ at hj
  change ‖iteratedFDeriv ℝ 1 _ z‖ ≤ ∑ i : Fin J,2*SmallGapLiftSupport.C*C^(J+2)*
      (((D (i.val+1) []).n:ℝ)+1)*(D (i.val+1) []).ell*((D (i.val+1) []).width)^2/normalCoefficient L J ∧
    ‖iteratedFDeriv ℝ 2 _ z‖ ≤ ∑ i : Fin J,4*SmallGapLiftSupport.C*C^(J+2)*
      (D (i.val+1) []).ell*(D (i.val+1) []).width*((((D (i.val+1) []).n:ℝ)+1)^(1/3:ℝ))^2/normalCoefficient L J ∧
    ‖iteratedFDeriv ℝ 3 _ z‖ ≤ ∑ i : Fin J,8*SmallGapLiftSupport.C*C^(J+2)*
      (D (i.val+1) []).ell*((((D (i.val+1) []).n:ℝ)+1)^(1/3:ℝ))/normalCoefficient L J at hj
  simp_rw [hN,hell,hwidth] at hj
  have hP : 0 ≤ SmallGapLiftSupport.C*C^(J+2) := mul_nonneg SmallGapLiftSupport.C_pos.le
    (pow_nonneg (by linarith) _)
  have hs := coarse_scheduled_sums hcn.le hη hη1 hηsq hT hTκ hL hη₀.le hb.le hκ hP hlen J
  refine ⟨hj.1.trans ?_,hj.2.1.trans ?_,hj.2.2.trans ?_⟩
  · simpa only [mul_assoc] using hs.1
  · simpa only [mul_assoc] using hs.2.1
  · simpa only [mul_assoc] using hs.2.2

end Bilevel.ChiExtensionCalibration
