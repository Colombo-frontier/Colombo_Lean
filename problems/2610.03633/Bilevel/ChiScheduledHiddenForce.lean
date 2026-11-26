import Bilevel.ChiScheduledExtensionAssembly
import Bilevel.ChiExtensionLedgerAbsorption

/-! The full actual hidden extension has a bounded gradient independent
of the fine parameter. The unbounded public radial field is excluded. -/
noncomputable section
namespace Bilevel.ChiExtensionCalibration
open ChiBoundedChain ChiRecursive ChiCarrier ChiOuter PrimitiveGeometry ChiExtension ChiCurvatureSchedule

theorem scheduled_hidden_force (A Kminus ζ cn : ℝ)
    (hA : 0 ≤ A) (hKm : 1 ≤ Kminus) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1)
    (hcn : 0 < cn) (hcn1 : cn ≤ 1) :
    ∃ Cforce : ℝ,1 ≤ Cforce ∧
    ∀ (E F : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
      [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
      (n : ℕ) (L η₀ b η κ T CR Km : ℝ) (weight : ℕ → ℝ),
      0 < L → 0 < η₀ → 0 < b → 0 < η → η ≤ 1 → η^2 ≤ 1/2 → 1 ≤ κ →
      1/η ≤ κ/6 → 1 ≤ T → T ≤ κ → 128 ≤ cn/η^2 →
      (∀ j,0 < weight j) → (∀ j,weight j ≤ 1) → 1 ≤ CR → ζ*Real.sqrt cn ≤ CR → 1 ≤ Km →
      ∀ (U : Space n →ₗᵢ[ℝ] E)
        (V : ∀ j,List ℕ → Space (sourceChainIndex cn (sourceRatio T j) (resolution η (κ/6) j)) →ₗᵢ[ℝ] F),
      let initial : Scale := ⟨η₀*L,b⟩
      let M := sourceMacroNode n initial Km U
      let D := sourceGeometry initial (sourceRatio T) (resolution η (κ/6)) weight A Kminus ζ cn CR V
      ∀ (J blocks normals : ℕ),1 ≤ J → ∀ (index : Fin J → Fin normals) (fineIndex : Fin normals)
        (c v : ℝ),∀ hc : 0 < c,c ≤ 1/128 → ∀ hv : 1 ≤ v, ∀ hβ : 0 < (D J []).width,
      ∀ z : Full (Joint E (Blocks blocks F)) normals,
      ‖iteratedFDeriv ℝ 1 (hidden index (coarseFamily blocks M D J) (coarseWidths D J) fineIndex
        (outerFineData blocks M D J c v hc hβ hv) (1/normalCoefficient L J)) z‖ ≤
        Cforce^(J+1)*η₀*Real.sqrt (2*(J:ℝ))*b^2/(κ/6)^2 := by
  obtain ⟨C,hC,hcoarse⟩ := scheduled_coarse_extension_jets A Kminus ζ cn hA hKm hζ hζ1 hcn hcn1
  obtain ⟨B,hB,hfine⟩ := source_outer_coupling_jets
  let P := 16*SmallGapLiftSupport.C*cn
  let Q := 24*SmallGapLiftSupport.C
  let Cforce := max 1 (P+Q)*(C+B)^2
  have hCforce : 1 ≤ Cforce := by
    simpa only [add_zero] using (three_coefficients_constant_ge_one (P:=P) (Q:=Q) (R:=0) hC hB)
  refine ⟨Cforce,hCforce,?_⟩
  intro E F _ _ _ _ _ _ n L η₀ b η κ T CR Km weight hL hη₀ hb hη hη1 hηsq hκ hthreshold
    hT hTκ hlen hw hw1 hCR hCRcn hKm' U V
  dsimp only
  let initial : Scale := ⟨η₀*L,b⟩
  let M := sourceMacroNode n initial Km U
  let D := sourceGeometry initial (sourceRatio T) (resolution η (κ/6)) weight A Kminus ζ cn CR V
  intro J blocks normals hJ index fineIndex c v hc hcs hv hβ z
  let data := outerFineData blocks M D J c v hc hβ hv
  have hκp : 0 < κ := by linarith
  have hK : 0 < κ/6 := by positivity
  have hr := sourceRatio_ge_one hT
  have hres := base_resolution_positive hη hK
  have hres1 (j : ℕ) : resolution η (κ/6) j ≤ 1 := (base_resolution_le hK hthreshold hη j).trans hη1
  have hp := parentScale_positive initial (sourceRatio T) (resolution η (κ/6)) (mul_pos hη₀ hL) hb hr hres
  have hW (i : Fin J) : 0 < coarseWidths D J i := by
    unfold coarseWidths
    have hi : 0 < (D (i.val+1) []).width := (hp (i.val+2)).2
    exact mul_pos hi (Real.rpow_pos_of_pos (by positivity) _)
  have hell : (D J []).ell = η₀*L*curvature T J := by
    obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show J ≠ 0 by omega)
    exact source_high_node_curvature initial (by linarith) η (κ/6) j
  have hwidth : (D J []).width = η^J*b/((κ/6)*curvature T J) := by
    obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show J ≠ 0 by omega)
    exact source_parent_width initial hT (mul_pos hη₀ hL) η (κ/6) (j+1)
  have hco := hcoarse E F n L η₀ b η κ T CR Km weight hL hη₀ hb hη hη1 hηsq hκ hthreshold hT hTκ hlen
    hw hw1 hCR hCRcn hKm' U V J blocks normals hJ index z
  have hfi := hfine E F n initial (mul_pos hη₀ hL) hb (sourceRatio T) (resolution η (κ/6)) weight
    A Kminus ζ cn CR Km hr hres hres1 hw hw1 hKm hζ hζ1 hCR hKm' U V J blocks c v hc hcs hv
    (normalSlice normals fineIndex z)
  have hfi' := fineTerm_normalized_jet fineIndex data (normalCoefficient_pos hL hJ) z 1 (by norm_num) hfi.1
  have hnorm := SmallGapLiftSupport.C_pos
  have hscale := mul_le_mul_of_nonneg_left
    (fine_source_energy_scale (b:=b) hL hη₀.le hη.le hη1 hK (curvature_bounds hT J).1 J)
    (show 0 ≤ 6*SmallGapLiftSupport.C*B^(J+2) by positivity)
  have hfi'' : ‖iteratedFDeriv ℝ 1 (fun y => fineTerm normals fineIndex data y/normalCoefficient L J) z‖ ≤
      24*SmallGapLiftSupport.C*B^(J+2)*η₀*Real.sqrt (2*(J:ℝ))*b^2/(κ/6)^2 := by
    apply hfi'.trans
    change 6*SmallGapLiftSupport.C*B^(J+2)*(D J []).ell*((D J []).width)^2/normalCoefficient L J ≤ _
    rw [hell,hwidth]
    convert hscale using 1 <;> ring
  have hh := source_hidden_add_jet_bound blocks normals M D J index fineIndex data (normalCoefficient L J) hW
    z 1 (by norm_num) _ _ hco.1 hfi''
  have hcoeff := three_coefficients_absorption (show 0 ≤ P by dsimp [P]; positivity)
    (show 0 ≤ Q by dsimp [Q]; positivity) (show (0:ℝ) ≤ 0 by norm_num) hC hB J
  simp only [zero_mul,add_zero] at hcoeff
  have hm := mul_le_mul_of_nonneg_right hcoeff
    (show 0 ≤ η₀*Real.sqrt (2*(J:ℝ))*b^2/(κ/6)^2 by positivity)
  apply hh.trans
  convert hm using 1 <;> dsimp only [P,Q,Cforce] <;> ring

end Bilevel.ChiExtensionCalibration
