import Bilevel.PolishedLiteralScalarWindows
import Bilevel.PolishedLiteralAllJets

/-! The source's annular localization is a full zero-jet assertion, not
only an estimate through order three. Here all orders concern the actual
literal smooth flattening and globally centered one-sided residual. -/
noncomputable section
open Set
open scoped BigOperators ContDiff
namespace Bilevel.PolishedAnnularAllJets
open ChiBoundedChain ZeroChainPotential PolishedLiteralFlattenCutoff
  PolishedLiteralFlattenMap PolishedLiteralScalarWindows
open PolishedLiteral.AllJets (scalar_plateau_flat scalar_linear_flat
  product_flat_left product_flat_right composition_flat)

theorem flatten_contDiff_all (δ : ℝ) (k : ℕ) : ContDiff ℝ k (flatten δ) :=
  contDiff_id.mul (omega_contDiff_all.comp (contDiff_id.div_const δ))

theorem resolutionDifference_contDiff_all (s δ' δ : ℝ) (k : ℕ) :
    ContDiff ℝ k (resolutionDifference s δ' δ) :=
  ((phi_contDiff k).comp (contDiff_const.mul (flatten_contDiff_all δ' k))).sub
    ((phi_contDiff k).comp (contDiff_const.mul (flatten_contDiff_all δ k)))

theorem resolutionDifference_flat_all (s : ℝ) {δ' δ : ℝ} (hδ' : 0 < δ') (hδ : δ' ≤ δ)
    (k : ℕ) (t : ℝ) (ht : ¬(δ' < |t| ∧ |t| < 2*δ)) :
    iteratedDeriv k (resolutionDifference s δ' δ) t=0 := by
  have he (u : ℝ) (hu : |u| ≤ δ') := resolutionDifference_zero_inner s hδ' hδ hu
  have ho (u : ℝ) (hu : 2*δ ≤ |u|) := resolutionDifference_zero_outer s hδ' hδ hu
  cases k with
  | zero =>
    simp only [iteratedDeriv_zero]
    by_cases hsmall : |t| ≤ δ'
    · exact he t hsmall
    · exact ho t (by by_contra! hh; exact ht ⟨lt_of_not_ge hsmall,hh⟩)
  | succ k =>
    by_cases hsmall : |t| ≤ δ'
    · exact scalar_plateau_flat (resolutionDifference_contDiff_all s δ' δ)
        (uniqueDiffOn_Icc (show -δ' < δ' by linarith)) (fun u hu => he u (abs_le.mpr hu))
        (k+1) (by omega) t (abs_le.mp hsmall)
    · have hout : 2*δ ≤ |t| := by by_contra! hh; exact ht ⟨lt_of_not_ge hsmall,hh⟩
      rcases le_total 0 t with hp | hn
      · apply scalar_plateau_flat (resolutionDifference_contDiff_all s δ' δ)
          (uniqueDiffOn_Ici (2*δ)) (fun u hu => ho u (by
            change 2*δ ≤ u at hu
            rw [abs_of_nonneg (by linarith : 0 ≤ u)]
            exact hu)) (k+1) (by omega) t
        simpa only [abs_of_nonneg hp] using hout
      · apply scalar_plateau_flat (resolutionDifference_contDiff_all s δ' δ)
          (uniqueDiffOn_Iic (-(2*δ))) (fun u hu => ho u (by
            change u ≤ -(2*δ) at hu
            rw [abs_of_nonpos (by linarith : u ≤ 0)]
            linarith)) (k+1) (by omega) t
        change t ≤ -(2*δ)
        rw [abs_of_nonpos hn] at hout
        linarith

theorem remainderProfile_contDiff_all (s δ : ℝ) (k : ℕ) :
    ContDiff ℝ k (remainderProfile s δ) :=
  ((phi_contDiff k).comp (contDiff_const.mul contDiff_id)).sub
    ((phi_contDiff k).comp (contDiff_const.mul (flatten_contDiff_all δ k)))

theorem remainderProfile_flat_outer_all (s : ℝ) {δ : ℝ} (hδ : 0 < δ)
    (k : ℕ) (t : ℝ) (ht : 2*δ ≤ |t|) : iteratedDeriv k (remainderProfile s δ) t=0 := by
  cases k with
  | zero => simpa only [iteratedDeriv_zero] using remainderProfile_zero_outer s hδ ht
  | succ k =>
    rcases le_total 0 t with hp | hn
    · apply scalar_plateau_flat (remainderProfile_contDiff_all s δ) (uniqueDiffOn_Ici (2*δ))
        (fun u hu => remainderProfile_zero_outer s hδ (by
          change 2*δ ≤ u at hu
          simpa only [abs_of_nonneg (by linarith : 0 ≤ u)] using hu)) (k+1) (by omega) t
      simpa only [abs_of_nonneg hp] using ht
    · apply scalar_plateau_flat (remainderProfile_contDiff_all s δ) (uniqueDiffOn_Iic (-(2*δ)))
        (fun u hu => remainderProfile_zero_outer s hδ (by
          change u ≤ -(2*δ) at hu
          rw [abs_of_nonpos (by linarith : u ≤ 0)]
          linarith)) (k+1) (by omega) t
      change t ≤ -(2*δ)
      rw [abs_of_nonpos hn] at ht
      linarith

theorem pieceProfile_flat_outside_window_all (s : ℝ) (J : ℕ) (δ : ℕ → ℝ)
    (hpos : ∀ j,j < J → 0 < δ j) (hmono : ∀ i j,i ≤ j → j < J → δ j ≤ δ i)
    (i : ℕ) (hi0 : 1 ≤ i) (hiJ : i ≤ J) (t : ℝ)
    (ht : ¬pieceWindow J δ i |t|) (k : ℕ) : iteratedDeriv k (pieceProfile s J δ i) t=0 := by
  have hprev : i-1 < J := by omega
  by_cases hi : i < J
  · rw [pieceProfile,if_pos hi]
    apply resolutionDifference_flat_all s (hpos i hi) (hmono (i-1) i (Nat.sub_le _ _) hi) k t
    intro hh
    exact ht ⟨hh.2,fun _ => hh.1⟩
  · rw [pieceProfile,if_neg hi]
    apply remainderProfile_flat_outer_all s (hpos (i-1) hprev) k t
    by_contra! hn
    exact ht ⟨hn,fun hh => (hi hh).elim⟩

theorem latentTerm_contDiff_all (n : ℕ) {f : ℝ → ℝ} (hf : ∀ k : ℕ,ContDiff ℝ k f)
    (i : Fin (n+1)) (k : ℕ) : ContDiff ℝ k (PolishedLiteral.latentTerm n f i) :=
  (PolishedLiteral.selector_contDiff n k i).mul (hf k |>.comp (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff)

theorem latentSelected_jet_sum_all (n : ℕ) {f : ℝ → ℝ} (hf : ∀ k : ℕ,ContDiff ℝ k f)
    (z : Space n) (k : ℕ) : iteratedFDeriv ℝ k (PolishedLiteral.latentSelected n f) z=
      ∑ i : Fin (n+1),iteratedFDeriv ℝ k (PolishedLiteral.latentTerm n f i) z := by
  have hh := congrFun (iteratedFDeriv_sum (u := Finset.univ)
    (fun i _ => latentTerm_contDiff_all n hf i k)) z
  simpa only [Finset.sum_apply] using hh

theorem latentTerm_flat_profile_all (n : ℕ) {f : ℝ → ℝ} (hf : ∀ k : ℕ,ContDiff ℝ k f)
    (i : Fin (n+1)) (z : Space n) (k : ℕ) (hz : ∀ j,j ≤ k → iteratedDeriv j f (z i)=0) :
    iteratedFDeriv ℝ k (PolishedLiteral.latentTerm n f i) z=0 :=
  product_flat_right k (PolishedLiteral.selector_contDiff n k i)
    ((hf k).comp (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff) z
    (fun j hj => scalar_linear_flat j (hf j) (EuclideanSpace.proj (𝕜 := ℝ) i) z (hz j hj))

theorem normalizedFlat_contDiff_all {δ : ℝ} (hδ : 0 < δ) (hs : δ ≤ 1/16) (n k : ℕ) :
    ContDiff ℝ k (PolishedLiteral.normalizedFlat n δ) := by
  have he : PolishedLiteral.normalizedFlat n δ=
      fun z => PolishedLiteral.latentSelected n (fun t => -phi (flatten δ t)) z+phi 0 :=
    funext (PolishedLiteral.normalizedFlat_selected hδ hs n)
  rw [he]
  exact (ContDiff.sum (fun i _ => latentTerm_contDiff_all n
    (fun s => ((phi_contDiff s).comp (flatten_contDiff_all δ s)).neg) i k)).add contDiff_const

theorem normalized_difference_annulus_all {δ' δ : ℝ} (hδ' : 0 < δ') (hδ : δ' ≤ δ)
    (hs : δ ≤ 1/16) (n : ℕ) (z : Space n) (k : ℕ)
    (hn : iteratedFDeriv ℝ k (fun w => PolishedLiteral.normalizedFlat n δ' w-
      PolishedLiteral.normalizedFlat n δ w) z ≠ 0) :
    ∃ i : Fin (n+1),δ' < |z i| ∧ |z i| < 2*δ ∧
      ∃ j ≤ k,iteratedFDeriv ℝ j (PolishedLiteral.selector n i) z ≠ 0 := by
  let f := fun t => -resolutionDifference 1 δ' δ t
  have hf (s : ℕ) : ContDiff ℝ s f := (resolutionDifference_contDiff_all 1 δ' δ s).neg
  have he : (fun w => PolishedLiteral.normalizedFlat n δ' w-PolishedLiteral.normalizedFlat n δ w)=
      PolishedLiteral.latentSelected n f := by
    funext w
    rw [PolishedLiteral.normalizedFlat_selected hδ' (hδ.trans hs),
      PolishedLiteral.normalizedFlat_selected (hδ'.trans_le hδ) hs,
      add_sub_add_right_eq_sub,PolishedLiteral.latentSelected_sub]
    congr 1
    funext t
    simp only [f,resolutionDifference,one_mul]
    ring
  rw [he,latentSelected_jet_sum_all n hf z k] at hn
  have hex : ∃ i : Fin (n+1),iteratedFDeriv ℝ k (PolishedLiteral.latentTerm n f i) z ≠ 0 := by
    by_contra! hz
    exact hn (Finset.sum_eq_zero (fun i _ => hz i))
  obtain ⟨i,hi⟩ := hex
  have hann : δ' < |z i| ∧ |z i| < 2*δ := by
    by_contra h
    apply hi
    apply latentTerm_flat_profile_all n hf i z k
    intro j _
    rw [iteratedDeriv_neg,resolutionDifference_flat_all 1 hδ' hδ j _ h,neg_zero]
  have hsel : ∃ j ≤ k,iteratedFDeriv ℝ j (PolishedLiteral.selector n i) z ≠ 0 := by
    by_contra! hz
    exact hi (product_flat_left k (PolishedLiteral.selector_contDiff n k i)
      ((hf k).comp (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff) z hz)
  exact ⟨i,hann.1,hann.2,hsel⟩

/-- The full source-scale assertion in fb's annular paragraph. The
centering constant cancels in the actual difference; the active selector
is evaluated at the unchanged normalized input. -/
theorem source_flatResidual_difference_annulus_all (n : ℕ) (L β δ' δ : ℝ)
    (hβ : 0 < β) (hδ' : 0 < δ') (hδ : δ' ≤ δ) (hs : δ ≤ β/16)
    (z : Space n) (k : ℕ)
    (hn : iteratedFDeriv ℝ k (fun w => PolishedLiteral.flatResidual n L β δ' w-
      PolishedLiteral.flatResidual n L β δ w) z ≠ 0) :
    ∃ i : Fin (n+1),δ' < |z i| ∧ |z i| < 2*δ ∧
      ∃ j ≤ k,iteratedFDeriv ℝ j (PolishedLiteral.selector n i) (β⁻¹ • z) ≠ 0 := by
  have hδp : 0 < δ := hδ'.trans_le hδ
  have hnδ : 0 < δ/β := div_pos hδp hβ
  have hnδ' : 0 < δ'/β := div_pos hδ' hβ
  have hnle : δ'/β ≤ δ/β := div_le_div_of_nonneg_right hδ hβ.le
  have hns : δ/β ≤ 1/16 := (div_le_iff₀ hβ).mpr (by linarith)
  let F := fun w => PolishedLiteral.normalizedFlat n (δ'/β) w-PolishedLiteral.normalizedFlat n (δ/β) w
  let f := fun w : Space n => β⁻¹ • w
  have hF (s : ℕ) : ContDiff ℝ s F :=
    (normalizedFlat_contDiff_all hnδ' (hnle.trans hns) n s).sub (normalizedFlat_contDiff_all hnδ hns n s)
  have hf (s : ℕ) : ContDiff ℝ s f := contDiff_id.const_smul β⁻¹
  have he : (fun w => PolishedLiteral.flatResidual n L β δ' w-PolishedLiteral.flatResidual n L β δ w)=
      fun w => (L*β^2) • (F ∘ f) w := by
    funext w
    rw [PolishedLiteral.flatResidual_scaled n L β δ' hβ.ne' hδ'.ne',
      PolishedLiteral.flatResidual_scaled n L β δ hβ.ne' hδp.ne']
    dsimp [ZeroChainResidualScaled.scaled,F,f]
    ring
  have hcomp : iteratedFDeriv ℝ k (F ∘ f) z ≠ 0 := by
    intro hz
    apply hn
    rw [he,iteratedFDeriv_const_smul_apply' ((hF k).comp (hf k)).contDiffAt,hz,smul_zero]
  have hex : ∃ j ≤ k,iteratedFDeriv ℝ j F (f z) ≠ 0 := by
    by_contra! hz
    exact hcomp (composition_flat k (hf k) (hF k) z hz)
  obtain ⟨j,hjk,hj⟩ := hex
  obtain ⟨i,hi1,hi2,a,haj,ha⟩ := normalized_difference_annulus_all hnδ' hnle hns n (f z) j hj
  have habs : |f z i|=|z i|/β := by
    simp only [f,PiLp.smul_apply,smul_eq_mul,abs_mul,abs_inv,abs_of_pos hβ,div_eq_mul_inv]
    ring
  rw [habs] at hi1 hi2
  have hb1 : δ' < |z i| := (div_lt_div_iff_of_pos_right hβ).mp hi1
  have hb2 : |z i| < 2*δ := (div_lt_div_iff_of_pos_right hβ).mp (by
    convert hi2 using 1
    ring)
  exact ⟨i,hb1,hb2,a,haj.trans hjk,ha⟩

end Bilevel.PolishedAnnularAllJets
