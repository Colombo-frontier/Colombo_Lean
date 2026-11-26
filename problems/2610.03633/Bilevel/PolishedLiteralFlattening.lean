import Bilevel.PolishedLiteralResidualBounds
import Bilevel.PolishedLiteralFlatteningTools
import Bilevel.ZeroChainFlatteningError

/-! One-sided latent flattening for the literal exponential-profile additive family, including the single global
centering constant. Coarse values and all derivative budgets retain that
constant; it cancels only in differences between resolutions. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
open scoped BigOperators
namespace Bilevel.PolishedLiteral
open ChiBoundedChain ZeroChainPotential PolishedLiteralFlattenCutoff PolishedLiteralFlattenMap
open PolishedLiteralFlatteningTools

theorem phi_lip (s t : ℝ) : |phi s-phi t|≤Real.sqrt (Real.exp 1)*|s-t| :=
  ZeroChainFlatteningError.phi_lip s t

theorem child_error_bound {δ : ℝ} (hδ : 0<δ) (t : ℝ) :
    |phi t-phi (flatten δ t)|≤2*Real.sqrt (Real.exp 1)*δ :=
  (phi_lip t (flatten δ t)).trans (by
    nlinarith [mul_le_mul_of_nonneg_left (flatten_error_le hδ t) (Real.sqrt_nonneg (Real.exp 1))])

theorem coordinateCutoff_flatten {δ : ℝ} (hδ : 0<δ) (hs : δ≤1/16) (t : ℝ) :
    ChiBoundedChain.coordinateCutoff (flatten δ t)=ChiBoundedChain.coordinateCutoff t := by
  by_cases ht : 2*δ≤|t|
  · rw [flatten_identity hδ ht]
  · have hh : |t|≤1/4 := by linarith [lt_of_not_ge ht]
    rw [ChiBoundedChain.coordinateCutoff_zero hh,
      ChiBoundedChain.coordinateCutoff_zero ((flatten_abs_le δ t).trans hh)]

theorem tailMask_flatten {δ : ℝ} (hδ : 0<δ) (hs : δ≤1/16)
    {n : ℕ} (i : Fin (n+1)) (z : Space n) :
    tailMask i (flattenMap n δ z)=tailMask i z := by
  simp only [tailMask,tailEnergy,flattenMap,coordinateMap_apply,coordinateCutoff_flatten hδ hs]

theorem flattenMap_scale_commute (n : ℕ) (β δ : ℝ) (hβ : β≠0) (hδ : δ≠0) (z : Space n) :
    β⁻¹ • flattenMap n δ z=flattenMap n (δ/β) (β⁻¹ • z) := by
  ext j
  simp only [PiLp.smul_apply,smul_eq_mul,flattenMap,coordinateMap_apply,flatten]
  have he : (β⁻¹*z j)/(δ/β)=z j/δ := by field_simp
  rw [he]
  ring

def latentTerm (n : ℕ) (f : ℝ → ℝ) (i : Fin (n+1)) (z : Space n) : ℝ :=
  PolishedLiteral.selector n i z*f (z i)

def latentSelected (n : ℕ) (f : ℝ → ℝ) (z : Space n) : ℝ :=
  ∑ i : Fin (n+1),latentTerm n f i z

def normalizedFlat (n : ℕ) (δ : ℝ) (z : Space n) : ℝ :=
  normalizedResidual n (flattenMap n δ z)

theorem psi_flatten {δ : ℝ} (hδ : 0<δ) (hs : δ≤1/16) (t : ℝ) :
    psi (flatten δ t)=psi t := by
  by_cases ht : 2*δ≤|t|
  · rw [flatten_identity hδ ht]
  · have hh : |t|≤1/2 := by linarith [lt_of_not_ge ht]
    rw [psi_zero ((le_abs_self t).trans hh),
      psi_zero ((le_abs_self _).trans ((flatten_abs_le δ t).trans hh))]

theorem selector_flatten {δ : ℝ} (hδ : 0<δ) (hs : δ≤1/16)
    {n : ℕ} (i : Fin (n+1)) (z : Space n) :
    PolishedLiteral.selector n i (flattenMap n δ z)=PolishedLiteral.selector n i z := by
  refine Fin.cases (tailMask_flatten hδ hs 0 z) (fun j => ?_) i
  simp only [PolishedLiteral.selector,Fin.cases_succ,flattenMap,coordinateMap_apply]
  rw [psi_flatten hδ hs]
  congr 1
  exact tailMask_flatten hδ hs j.succ z

theorem normalizedResidual_selected (n : ℕ) (z : Space n) :
    normalizedResidual n z=latentSelected n (fun t => -phi t) z+phi 0 := by
  unfold normalizedResidual latentSelected latentTerm PolishedLiteral.residualTerm
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem normalizedFlat_selected {δ : ℝ} (hδ : 0<δ) (hs : δ≤1/16)
    (n : ℕ) (z : Space n) :
    normalizedFlat n δ z=latentSelected n (fun t => -phi (flatten δ t)) z+phi 0 := by
  rw [normalizedFlat,normalizedResidual_selected]
  unfold latentSelected latentTerm
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [selector_flatten hδ hs]
  rfl

theorem latentSelected_sub (n : ℕ) (f g : ℝ → ℝ) (z : Space n) :
    latentSelected n f z-latentSelected n g z=latentSelected n (fun t => f t-g t) z := by
  simp only [latentSelected,latentTerm,mul_sub,Finset.sum_sub_distrib]

theorem latentSelected_abs_bound (n : ℕ) (f : ℝ → ℝ) (B : ℝ) (hB : 0≤B)
    (hf : ∀ t,|f t|≤B) (z : Space n) : |latentSelected n f z|≤Real.exp 1*B := by
  calc
    _ ≤ ∑ i : Fin (n+1),|latentTerm n f i z| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin (n+1),PolishedLiteral.selector n i z*B := by
      apply Finset.sum_le_sum
      intro i _
      rw [latentTerm,abs_mul,abs_of_nonneg (PolishedLiteral.selector_nonneg n i z)]
      exact mul_le_mul_of_nonneg_left (hf _) (PolishedLiteral.selector_nonneg n i z)
    _ = (∑ i : Fin (n+1),PolishedLiteral.selector n i z)*B := (Finset.sum_mul ..).symm
    _ ≤ Real.exp 1*B := mul_le_mul_of_nonneg_right (PolishedLiteral.selector_sum_le_exp_one n z) hB

theorem normalized_flattening_error {δ : ℝ} (hδ : 0<δ) (hs : δ≤1/16)
    (n : ℕ) (z : Space n) :
    |normalizedResidual n z-normalizedFlat n δ z|≤Real.exp 1*(2*Real.sqrt (Real.exp 1)*δ) := by
  rw [normalizedResidual_selected,normalizedFlat_selected hδ hs]
  rw [add_sub_add_right_eq_sub,latentSelected_sub]
  apply latentSelected_abs_bound n _ _ (by positivity)
  intro t
  have hh := child_error_bound hδ t
  simpa only [neg_sub_neg,abs_sub_comm] using hh

theorem normalizedFlat_contDiff (n : ℕ) (δ : ℝ) : ContDiff ℝ 3 (normalizedFlat n δ) :=
  (normalizedResidual_contDiff n 3).comp (flattenMap_contDiff n δ)

theorem normalizedFlat_positive_jets : ∃ C : ℝ,1≤C ∧
    ∀ (n : ℕ) (δ : ℝ),0<δ → δ≤1 → ∀ (j : Fin 3) (z : Space n),
      ‖iteratedFDeriv ℝ (j.val+1) (normalizedFlat n δ) z‖≤C/δ^j.val := by
  obtain ⟨M,hM,hm⟩ := normalizedResidual_jet_bounds
  obtain ⟨K,hK,hcore⟩ := coreMap_common_jet_bound
  let d : Fin 3 → ℝ := fun j => ((j.val+1).factorial:ℝ)*M*K^(j.val+1)
  have hd (j : Fin 3) : 0≤d j := by dsimp [d];positivity
  let C := 1+∑ j,d j
  have hC : 1≤C := le_add_of_nonneg_right (Finset.sum_nonneg (fun j _ => hd j))
  have hdC (j : Fin 3) : d j≤C := by
    have hh := Finset.single_le_sum (fun l (_ : l∈Finset.univ) => hd l) (Finset.mem_univ j)
    dsimp only [C]
    linarith
  refine ⟨C,hC,fun n δ hδ hs j z => ?_⟩
  have ho (k : ℕ) (hk0 : 1≤k) (hk : k≤3) (w : Space n) :
      ‖iteratedFDeriv ℝ k (normalizedResidual n) w‖≤M*δ/δ^k := by
    apply (hm n k hk w).trans
    have hp : δ^k≤δ := by simpa only [pow_one] using pow_le_pow_of_le_one hδ.le hs hk0
    exact (le_div_iff₀ (pow_pos hδ k)).mpr (mul_le_mul_of_nonneg_left hp (by linarith))
  have hh := flatten_positive_jet_bound (normalizedResidual_contDiff n 3) K M δ hK
    (by linarith) hδ (hcore n) ho z (j.val+1) (by omega) (by omega)
  change ‖iteratedFDeriv ℝ (j.val+1) (normalizedFlat n δ) z‖≤_ at hh
  have he : ((j.val+1).factorial:ℝ)*M*K^(j.val+1)*δ/δ^(j.val+1)=d j/δ^j.val := by
    dsimp only [d]
    rw [pow_succ]
    field_simp
    ring
  rw [he] at hh
  exact hh.trans (div_le_div_of_nonneg_right (hdC j) (pow_nonneg hδ.le _))

theorem flatResidual_scaled (n : ℕ) (L β δ : ℝ) (hβ : β≠0) (hδ : δ≠0) :
    flatResidual n L β δ=ZeroChainResidualScaled.scaled (normalizedFlat n (δ/β)) (L*β^2) β := by
  funext z
  unfold flatResidual residual ZeroChainResidualScaled.scaled normalizedFlat
  rw [flattenMap_scale_commute n β δ hβ hδ]

theorem source_flattening_error (n : ℕ) (L β δ : ℝ) (hL : 0≤L) (hβ : 0<β)
    (hδ : 0<δ) (hs : δ≤β/16) (z : Space n) :
    |residual n L β z-flatResidual n L β δ z|≤(Real.exp 1*(2*Real.sqrt (Real.exp 1)))*L*β*δ := by
  rw [flatResidual_scaled n L β δ hβ.ne' hδ.ne']
  change |(L*β^2)*normalizedResidual n (β⁻¹ • z)-(L*β^2)*normalizedFlat n (δ/β) (β⁻¹ • z)|≤_
  rw [← mul_sub,abs_mul,abs_of_nonneg (mul_nonneg hL (sq_nonneg _))]
  have hh := mul_le_mul_of_nonneg_left
    (normalized_flattening_error (div_pos hδ hβ) ((div_le_iff₀ hβ).mpr (by linarith)) n (β⁻¹ • z))
    (mul_nonneg hL (sq_nonneg β))
  exact hh.trans_eq (by field_simp;ring)

end Bilevel.PolishedLiteral
