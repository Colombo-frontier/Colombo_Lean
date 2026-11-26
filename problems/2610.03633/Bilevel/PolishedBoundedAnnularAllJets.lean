import Bilevel.PolishedSmoothProfiles
import Bilevel.PolishedAnnularAllJets
import Bilevel.PolishedSplitAllJets
import Bilevel.ChiFineScaled

/-! Arbitrary-order annular localization for the canonical bounded-chain
frontier, instantiated with the migrated genuine smooth cutoff. This
module must be rebuilt with the complete smooth-profile dependency closure.
-/
noncomputable section
open scoped BigOperators ContDiff
namespace Bilevel.PolishedBoundedAnnularAllJets
open ChiBoundedChain ZeroChainPotential
open PolishedLiteral.AllJets (scalar_linear_flat product_flat_left product_flat_right composition_flat)

theorem canonical_flatten_eq_literal (δ : ℝ) :
    ZeroChainFlatteningCutoff.flatten δ=PolishedLiteralFlattenCutoff.flatten δ := by
  funext t
  simp only [ZeroChainFlatteningCutoff.flatten,PolishedLiteralFlattenCutoff.flatten,
    PolishedSmoothProfiles.omega_eq_literal]

theorem canonical_resolutionDifference_eq_literal (s δ' δ : ℝ) :
    ZeroChainFlatteningAnnulus.resolutionDifference s δ' δ=
      PolishedLiteralScalarWindows.resolutionDifference s δ' δ := by
  funext t
  simp only [ZeroChainFlatteningAnnulus.resolutionDifference,
    PolishedLiteralScalarWindows.resolutionDifference,canonical_flatten_eq_literal]

theorem term_contDiff_all (n : ℕ) {f : ℝ → ℝ} (hf : ∀ k : ℕ,ContDiff ℝ k f)
    (i : Fin (n+1)) (k : ℕ) : ContDiff ℝ k (ChiFine.term n f i) :=
  (selector_contDiff n k i).mul ((hf k).comp (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff)

theorem selected_jet_sum_all (n : ℕ) {f : ℝ → ℝ} (hf : ∀ k : ℕ,ContDiff ℝ k f)
    (z : Space n) (k : ℕ) : iteratedFDeriv ℝ k (ChiFine.selected n f) z=
      ∑ i : Fin (n+1),iteratedFDeriv ℝ k (ChiFine.term n f i) z := by
  have hh := congrFun (iteratedFDeriv_sum (u := Finset.univ) (fun i _ => term_contDiff_all n hf i k)) z
  simpa only [Finset.sum_apply] using hh

theorem term_flat_profile_all (n : ℕ) {f : ℝ → ℝ} (hf : ∀ k : ℕ,ContDiff ℝ k f)
    (i : Fin (n+1)) (z : Space n) (k : ℕ) (hz : ∀ j,j ≤ k → iteratedDeriv j f (z i)=0) :
    iteratedFDeriv ℝ k (ChiFine.term n f i) z=0 :=
  product_flat_right k (selector_contDiff n k i)
    ((hf k).comp (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff) z
    (fun j hj => scalar_linear_flat j (hf j) (EuclideanSpace.proj (𝕜 := ℝ) i) z (hz j hj))

theorem flattened_contDiff_all (n : ℕ) (δ : ℝ) (k : ℕ) : ContDiff ℝ k (ChiFine.flattened n δ) := by
  have hf (s : ℕ) : ContDiff ℝ s (ChiFine.flatProfile δ) := by
    unfold ChiFine.flatProfile
    rw [canonical_flatten_eq_literal]
    exact (((phi_contDiff s).comp (PolishedAnnularAllJets.flatten_contDiff_all δ s)).sub contDiff_const).neg
  unfold ChiFine.flattened ChiFine.selected
  exact ContDiff.sum (fun i _ => term_contDiff_all n hf i k)

theorem flattened_difference_annulus_all {δ' δ : ℝ} (hδ' : 0 < δ') (hδ : δ' ≤ δ)
    (n : ℕ) (z : Space n) (k : ℕ)
    (hn : iteratedFDeriv ℝ k (fun w => ChiFine.flattened n δ' w-ChiFine.flattened n δ w) z ≠ 0) :
    ∃ i : Fin (n+1),δ' < |z i| ∧ |z i| < 2*δ ∧
      ∃ j ≤ k,iteratedFDeriv ℝ j (selector n i) z ≠ 0 := by
  let f := fun t => -PolishedLiteralScalarWindows.resolutionDifference 1 δ' δ t
  have hf (s : ℕ) : ContDiff ℝ s f :=
    (PolishedAnnularAllJets.resolutionDifference_contDiff_all 1 δ' δ s).neg
  have he : (fun w => ChiFine.flattened n δ' w-ChiFine.flattened n δ w)=ChiFine.selected n f := by
    rw [ChiFine.flattened_difference,canonical_resolutionDifference_eq_literal]
  rw [he,selected_jet_sum_all n hf z k] at hn
  have hex : ∃ i : Fin (n+1),iteratedFDeriv ℝ k (ChiFine.term n f i) z ≠ 0 := by
    by_contra! hz
    exact hn (Finset.sum_eq_zero (fun i _ => hz i))
  obtain ⟨i,hi⟩ := hex
  have hann : δ' < |z i| ∧ |z i| < 2*δ := by
    by_contra h
    apply hi
    apply term_flat_profile_all n hf i z k
    intro j _
    rw [iteratedDeriv_neg,PolishedAnnularAllJets.resolutionDifference_flat_all 1 hδ' hδ j _ h,neg_zero]
  have hsel := PolishedSplitAllJets.selected_atom_jet_has_selector
    (fun w : Space n => w) (fun _ => contDiff_id) (fun w : Space n => f (w i))
    (fun s => (hf s).comp (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff) i z k hi
  exact ⟨i,hann.1,hann.2,hsel⟩

theorem source_flatFrontier_difference_annulus_all (n : ℕ) (ℓ β δ' δ : ℝ)
    (hβ : 0 < β) (hδ' : 0 < δ') (hδ : δ' ≤ δ) (z : Space n) (k : ℕ)
    (hn : iteratedFDeriv ℝ k (fun w => ChiFine.flatFrontier n ℓ β δ' w-
      ChiFine.flatFrontier n ℓ β δ w) z ≠ 0) :
    ∃ i : Fin (n+1),δ' < |z i| ∧ |z i| < 2*δ ∧
      ∃ j ≤ k,iteratedFDeriv ℝ j (selector n i) (β⁻¹ • z) ≠ 0 := by
  have hnδ' : 0 < δ'/β := div_pos hδ' hβ
  have hnle : δ'/β ≤ δ/β := div_le_div_of_nonneg_right hδ hβ.le
  let F := fun w => ChiFine.flattened n (δ'/β) w-ChiFine.flattened n (δ/β) w
  let f := fun w : Space n => β⁻¹ • w
  have hF (s : ℕ) : ContDiff ℝ s F :=
    (flattened_contDiff_all n (δ'/β) s).sub (flattened_contDiff_all n (δ/β) s)
  have hf (s : ℕ) : ContDiff ℝ s f := contDiff_id.const_smul β⁻¹
  have he : (fun w => ChiFine.flatFrontier n ℓ β δ' w-ChiFine.flatFrontier n ℓ β δ w)=
      fun w => (ℓ*β^2) • (F ∘ f) w := by
    funext w
    dsimp [ChiFine.flatFrontier,ZeroChainResidualScaled.scaled,F,f]
    ring
  have hcomp : iteratedFDeriv ℝ k (F ∘ f) z ≠ 0 := by
    intro hz
    apply hn
    rw [he,iteratedFDeriv_const_smul_apply' ((hF k).comp (hf k)).contDiffAt,hz,smul_zero]
  have hex : ∃ j ≤ k,iteratedFDeriv ℝ j F (f z) ≠ 0 := by
    by_contra! hz
    exact hcomp (composition_flat k (hf k) (hF k) z hz)
  obtain ⟨j,hjk,hj⟩ := hex
  obtain ⟨i,hi1,hi2,a,haj,ha⟩ := flattened_difference_annulus_all hnδ' hnle n (f z) j hj
  have habs : |f z i|=|z i|/β := by
    simp only [f,PiLp.smul_apply,smul_eq_mul,abs_mul,abs_inv,abs_of_pos hβ,div_eq_mul_inv]
    ring
  rw [habs] at hi1 hi2
  have hb1 : δ' < |z i| := (div_lt_div_iff_of_pos_right hβ).mp hi1
  have hb2 : |z i| < 2*δ := (div_lt_div_iff_of_pos_right hβ).mp (by
    convert hi2 using 1
    ring)
  exact ⟨i,hb1,hb2,a,haj.trans hjk,ha⟩

end Bilevel.PolishedBoundedAnnularAllJets
