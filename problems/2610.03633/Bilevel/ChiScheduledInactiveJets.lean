import Bilevel.ChiHierarchyInactive
import Bilevel.ChiScheduledCoarseExtension
import Bilevel.ChiFineSourceScales
import Bilevel.ChiScheduledRadialBudget

/-! Actual globally fixed inactive hierarchy: physical source gradient
and Hessian ledgers without increasing Cf or CT. Only Cf≥1 and the
already constructed v≥1 are needed; an inactive third-jet budget is not
required by the mean Primitive model. -/
noncomputable section
namespace Bilevel.ChiExtensionCalibration
open ChiBoundedChain ChiRecursive ChiCarrier ChiOuter PrimitiveGeometry ChiExtension ChiCurvatureSchedule

theorem inactive_radial_add_jet_bound
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (m : ℕ) (M : Node E) (D : Geometry F) (J : ℕ)
    (c v : ℝ) (hc : 0 < c) (hβ : 0 < (D J []).width) (hv : 1 ≤ v)
    (s : ℕ) (index radialIndex : Fin J → Fin s) (fineIndex : Fin s) (rad R : ℕ → ℝ) (dn : ℝ)
    (hw : ∀ i : Fin J,0 < (D (i.val+1) []).width)
    (z : Full (Joint E (Blocks m F)) s) (k : ℕ) (hk : k ≤ 3) (Bh Br : ℝ)
    (hh : ‖iteratedFDeriv ℝ k (hierarchyInactiveHidden m M D J c v hc hβ hv s index fineIndex dn) z‖ ≤ Bh)
    (hr : ‖iteratedFDeriv ℝ k (radialSum radialIndex
      (fun i => hierarchyBlock (E:=E) (F:=F) m (i.val+1)) (fun i => hierarchyBlock_norm_le m (i.val+1))
      (fun i => rad (i.val+1)) (fun i => R (i.val+1)) dn) z‖ ≤ Br) :
    ‖iteratedFDeriv ℝ k (hierarchyInactiveExtension m M D J c v hc hβ hv s index radialIndex fineIndex rad R dn) z‖ ≤ Bh+Br := by
  have hhcont := hierarchyInactiveHidden_contDiff m M D J c v hc hβ hv s index fineIndex dn hw
  have hrcont := radialSum_contDiff radialIndex (fun i => hierarchyBlock (E:=E) (F:=F) m (i.val+1))
    (fun i => hierarchyBlock_norm_le m (i.val+1)) (fun i => rad (i.val+1)) (fun i => R (i.val+1)) dn
  have hk' : (k:WithTop ℕ∞) ≤ 3 := by exact_mod_cast hk
  unfold hierarchyInactiveExtension
  rw [iteratedFDeriv_add_apply' ((hhcont.of_le hk').contDiffAt) ((hrcont.of_le hk').contDiffAt)]
  exact (norm_add_le _ _).trans (add_le_add hh hr)

set_option maxHeartbeats 1200000 in
theorem scheduled_inactive_jets (A Kminus ζ cn : ℝ)
    (hA : 0 ≤ A) (hKm : 1 ≤ Kminus) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1)
    (hcn : 0 < cn) (hcn1 : cn ≤ 1) :
    ∃ C B : ℝ,1 ≤ C ∧ 1 ≤ B ∧
    ∀ (E F : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
      [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
      (n : ℕ) (L μ θ η₀ b η κ T CR Km : ℝ) (weight : ℕ → ℝ),
      0 < L → 0 < μ → 0 ≤ θ → θ ≤ κ → 0 < η₀ → 0 < b → 0 < η → η ≤ 1 → η^2 ≤ 1/2 → 1 ≤ κ →
      1/η ≤ κ/6 → 1 ≤ T → T ≤ κ → 128 ≤ cn/η^2 →
      (∀ j,0 < weight j) → (∀ j,weight j ≤ 1) → 1 ≤ CR → ζ*Real.sqrt cn ≤ CR → 1 ≤ Km →
      ∀ (U : Space n →ₗᵢ[ℝ] E)
        (V : ∀ j,List ℕ → Space (sourceChainIndex cn (sourceRatio T j) (resolution η (κ/6) j)) →ₗᵢ[ℝ] F),
      let initial : Scale := ⟨η₀*L,b⟩
      let M := sourceMacroNode n initial Km U
      let D := sourceGeometry initial (sourceRatio T) (resolution η (κ/6)) weight A Kminus ζ cn CR V
      ∀ (J blocks normals : ℕ),1 ≤ J → ∀ (index radialIndex : Fin J → Fin normals) (fineIndex : Fin normals)
        (c Cf : ℝ),0 < c → c ≤ 1/128 → 1 ≤ Cf →
      let v := fineParameter (θ*μ) (3*μ/2) ((D J []).ell) (normalCoefficient L J) Cf J
      ∀ hv : 1 ≤ v, ∀ hc : 0 < c, ∀ hβ : 0 < (D J []).width,
      let rad := fun j => weight j*(D j []).nu
      let R := fun j => (D j []).radius
      ∀ z : Full (Joint E (Blocks blocks F)) normals,
      ‖iteratedFDeriv ℝ 1 (hierarchyInactiveHidden blocks M D J c v hc hβ hv normals index fineIndex
        (normalCoefficient L J)) z‖ ≤
        (16*SmallGapLiftSupport.C*C^(J+2)*cn+32*SmallGapLiftSupport.C*B^(J+2))*
          η₀*Real.sqrt (2*(J:ℝ))*b^2/(κ/6)^2 ∧
      ‖iteratedFDeriv ℝ 2 (hierarchyInactiveExtension blocks M D J c v hc hβ hv normals index radialIndex fineIndex
        rad R (normalCoefficient L J)) z‖ ≤
        192*SmallGapLiftSupport.C*C^(J+2)*η₀*b*(cn/η^2)*((J:ℝ)+1)^2+
          92*SmallGapLiftSupport.C*B^(J+2)*b/c+144*CR*η₀*b*((J:ℝ)+1)^2 := by
  obtain ⟨C,hC,hcoarse⟩ := scheduled_coarse_extension_jets A Kminus ζ cn hA hKm hζ hζ1 hcn hcn1
  obtain ⟨B,hB,hfine⟩ := source_outer_inactive_normal_jets
  refine ⟨C,B,hC,hB,?_⟩
  intro E F _ _ _ _ _ _ n L μ θ η₀ b η κ T CR Km weight hL hμ hθ hθκ hη₀ hb hη hη1 hηsq hκ hthreshold
    hT hTκ hlen hw hw1 hCR hCRcn hKm' U V
  dsimp only
  let initial : Scale := ⟨η₀*L,b⟩
  let M := sourceMacroNode n initial Km U
  let D := sourceGeometry initial (sourceRatio T) (resolution η (κ/6)) weight A Kminus ζ cn CR V
  intro J blocks normals hJ index radialIndex fineIndex c Cf hc hcs hCf hv hc' hβ z
  let v := fineParameter (θ*μ) (3*μ/2) ((D J []).ell) (normalCoefficient L J) Cf J
  let rad := fun j => weight j*(D j []).nu
  let R := fun j => (D j []).radius
  have hκp : 0 < κ := by linarith
  have hK : 0 < κ/6 := by positivity
  have hr := sourceRatio_ge_one hT
  have hres := base_resolution_positive hη hK
  have hres1 (j : ℕ) : resolution η (κ/6) j ≤ 1 := (base_resolution_le hK hthreshold hη j).trans hη1
  have hp := parentScale_positive initial (sourceRatio T) (resolution η (κ/6)) (mul_pos hη₀ hL) hb hr hres
  have hwidth (i : Fin J) : 0 < (D (i.val+1) []).width := (hp (i.val+2)).2
  have hell : (D J []).ell = η₀*L*curvature T J := by
    obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show J ≠ 0 by omega)
    exact source_high_node_curvature initial (by linarith) η (κ/6) j
  have hβeq : (D J []).width = η^J*b/((κ/6)*curvature T J) := by
    obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show J ≠ 0 by omega)
    exact source_parent_width initial hT (mul_pos hη₀ hL) η (κ/6) (j+1)
  have hco := hcoarse E F n L η₀ b η κ T CR Km weight hL hη₀ hb hη hη1 hηsq hκ hthreshold hT hTκ hlen
    hw hw1 hCR hCRcn hKm' U V J blocks normals hJ index z
  have hfi := hfine E F n initial (mul_pos hη₀ hL) hb (sourceRatio T) (resolution η (κ/6)) weight
    A Kminus ζ cn CR Km hr hres hres1 hw hw1 hKm hζ hζ1 hCR hKm' U V J blocks c v hc' hcs hv hβ normals fineIndex z
  have hnorm := SmallGapLiftSupport.C_pos
  have hcont := outerInactiveNormal_contDiff blocks M D J c v hc' hβ hv normals fineIndex
  have hfi1 : ‖iteratedFDeriv ℝ 1 (fun y => outerInactiveNormal blocks M D J c v hc' hβ hv normals fineIndex y/
      normalCoefficient L J) z‖ ≤ 8*SmallGapLiftSupport.C*B^(J+2)*(D J []).ell*((D J []).width)^2/normalCoefficient L J := by
    rw [normalized_jet_norm hcont (normalCoefficient_pos hL hJ) 1 (by norm_num)]
    exact div_le_div_of_nonneg_right hfi.1 (normalCoefficient_pos hL hJ).le
  have hfi2 : ‖iteratedFDeriv ℝ 2 (fun y => outerInactiveNormal blocks M D J c v hc' hβ hv normals fineIndex y/
      normalCoefficient L J) z‖ ≤ 23*SmallGapLiftSupport.C*B^(J+2)*(D J []).ell*(D J []).width*
        Real.sqrt v/c/normalCoefficient L J := by
    rw [normalized_jet_norm hcont (normalCoefficient_pos hL hJ) 2 (by norm_num)]
    exact div_le_div_of_nonneg_right hfi.2.1 (normalCoefficient_pos hL hJ).le
  have hpay1 : 8*SmallGapLiftSupport.C*B^(J+2)*(D J []).ell*((D J []).width)^2/normalCoefficient L J ≤
      32*SmallGapLiftSupport.C*B^(J+2)*η₀*Real.sqrt (2*(J:ℝ))*b^2/(κ/6)^2 := by
    rw [hell,hβeq]
    have he := mul_le_mul_of_nonneg_left (fine_source_energy_scale (b:=b) hL hη₀.le hη.le hη1 hK (curvature_bounds hT J).1 J)
      (show 0 ≤ 8*SmallGapLiftSupport.C*B^(J+2) by positivity)
    convert he using 1 <;> ring
  have hv' : 1 ≤ fineParameter (θ*μ) (3*μ/2) (η₀*L*curvature T J) (normalCoefficient L J) Cf J := by
    have hh : 1 ≤ v := hv
    dsimp only [v] at hh
    rwa [hell] at hh
  have hpay2 : 23*SmallGapLiftSupport.C*B^(J+2)*(D J []).ell*(D J []).width*Real.sqrt v/c/normalCoefficient L J ≤
      92*SmallGapLiftSupport.C*B^(J+2)*b/c := by
    dsimp only [v]
    rw [hell,hβeq]
    have hs := fine_source_second_scale hθ hμ hL hη₀ hη.le hη1 hb.le hK (curvature_bounds hT J).1 hCf J hJ hv'
    have hscale : 2*θ*b/(3*(κ/6)) ≤ 4*b := by
      apply (div_le_iff₀ (show 0 < 3*(κ/6) by positivity)).mpr
      have hm := mul_le_mul_of_nonneg_right hθκ hb.le
      nlinarith only [hm]
    have he := mul_le_mul_of_nonneg_left (hs.trans hscale)
      (show 0 ≤ 23*SmallGapLiftSupport.C*B^(J+2)/c by positivity)
    convert he using 1 <;> ring
  have hH1 := hierarchyInactiveHidden_jet_bound blocks M D J c v hc' hβ hv normals index fineIndex
    (normalCoefficient L J) hwidth z 1 (by norm_num) _ _ hco.1 (hfi1.trans hpay1)
  have hH2 := hierarchyInactiveHidden_jet_bound blocks M D J c v hc' hβ hv normals index fineIndex
    (normalCoefficient L J) hwidth z 2 (by norm_num) _ _ hco.2.1 (hfi2.trans hpay2)
  have hra := scheduled_radial_jets hJ radialIndex
    (fun i => hierarchyBlock (E:=E) (F:=F) blocks (i.val+1)) (fun i => hierarchyBlock_norm_le blocks (i.val+1))
    L η₀ b η (κ/6) κ T ζ CR (fun i => weight (i.val+1)) hL hη₀ hb hη hη1 hκ rfl hT hTκ hζ (by linarith)
    (fun i => hw (i.val+1)) (fun i => hw1 (i.val+1)) z
  refine ⟨hH1.trans_eq (by ring),?_⟩
  exact inactive_radial_add_jet_bound blocks M D J c v hc' hβ hv normals index radialIndex fineIndex rad R
    (normalCoefficient L J) hwidth z 2 (by norm_num) _ _ hH2 hra.1

end Bilevel.ChiExtensionCalibration
