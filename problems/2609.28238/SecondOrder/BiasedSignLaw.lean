import SecondOrder.FiniteLawTransport
import SecondOrder.Entropy
import SecondOrder.RademacherMoments

open MeasureTheory InformationTheory
open scoped BigOperators Classical ENNReal

namespace SecondOrder
noncomputable section

def biasedSignMass (R c : ℝ) (b : Bool) : ℝ := (1+(c/R)*signValue b)/2

theorem biasedSignMass_pos {R c : ℝ} (hR : 2 ≤ R) (hc : c^2 = 1) (b : Bool) :
    0 < biasedSignMass R c b := by
  have hp := biased_sign_probability_and_mean hR hc
  cases b <;> dsimp [biasedSignMass, signValue] <;> linarith

theorem biasedSignMass_sum (R c : ℝ) : ∑ b, biasedSignMass R c b = 1 := by
  rw [Fintype.sum_bool]
  unfold biasedSignMass signValue
  norm_num
  ring

/-- A single coefficient sign is sampled with the bias needed for mean c. -/
def biasedSignPMF (R c : ℝ) (hR : 2 ≤ R) (hc : c^2 = 1) : PMF Bool :=
  PMF.ofFintype (fun b => ENNReal.ofReal (biasedSignMass R c b)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun b _ => (biasedSignMass_pos hR hc b).le), biasedSignMass_sum]
    simp)

@[simp] theorem biasedSignPMF_toReal (R c : ℝ) (hR : 2 ≤ R) (hc : c^2 = 1) (b : Bool) :
    (biasedSignPMF R c hR hc b).toReal = biasedSignMass R c b :=
  ENNReal.toReal_ofReal (biasedSignMass_pos hR hc b).le

theorem biasedSignPMF_ne_zero (R c : ℝ) (hR : 2 ≤ R) (hc : c^2 = 1) (b : Bool) :
    biasedSignPMF R c hR hc b ≠ 0 :=
  (ENNReal.ofReal_pos.mpr (biasedSignMass_pos hR hc b)).ne'

theorem biasedSignPMF_mean (R c : ℝ) (hR : 2 ≤ R) (hc : c^2 = 1) :
    pmfMean (biasedSignPMF R c hR hc) (fun b => R*signValue b) = c := by
  simp only [pmfMean, smul_eq_mul, Fintype.sum_bool, biasedSignPMF_toReal,
    biasedSignMass, signValue]
  have hR0 : R ≠ 0 := by linarith
  field_simp
  ring

theorem uniformBool_ne_zero (b : Bool) : PMF.uniformOfFintype Bool b ≠ 0 := by
  simp [PMF.uniformOfFintype_apply]

theorem pmfKL_biasedSign (R c : ℝ) (hR : 2 ≤ R) (hc : c^2 = 1) :
    pmfKL (biasedSignPMF R c hR hc) (PMF.uniformOfFintype Bool) = signKL (c/R) := by
  simp only [pmfKL, Fintype.sum_bool, biasedSignPMF_toReal,
    PMF.uniformOfFintype_apply, Fintype.card_bool, ENNReal.toReal_inv, ENNReal.toReal_ofNat,
    biasedSignMass, signValue]
  norm_num
  simp only [show ∀ x : ℝ, x/2/(1/2) = x by intro x; ring, ← sub_eq_add_neg]
  unfold signKL
  ring

theorem klDiv_biasedSign (R c : ℝ) (hR : 2 ≤ R) (hc : c^2 = 1) :
    klDiv (biasedSignPMF R c hR hc).toMeasure (PMF.uniformOfFintype Bool).toMeasure ≤
      ENNReal.ofReal (1/R^2) := by
  rw [klDiv_pmf _ _ uniformBool_ne_zero, pmfKL_biasedSign]
  exact ENNReal.ofReal_le_ofReal (biased_sign_entropy hR hc)

theorem klDiv_biasedSignProduct {ι : Type*} [Fintype ι]
    (R : ℝ) (c : ι → ℝ) (hR : 2 ≤ R) (hc : ∀ i, c i^2 = 1) :
    klDiv (finitePiPMF (fun i => biasedSignPMF R (c i) hR (hc i))).toMeasure
      (finitePiPMF (fun _ : ι => PMF.uniformOfFintype Bool)).toMeasure ≤
      ENNReal.ofReal ((Fintype.card ι:ℝ)/R^2) := by
  rw [klDiv_finitePi _ _ (fun i => biasedSignPMF_ne_zero R (c i) hR (hc i))
    (fun _ => uniformBool_ne_zero)]
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ ∑ _i : ι, 1/R^2 := Finset.sum_le_sum (fun i _ => by
      rw [pmfKL_biasedSign]
      exact biased_sign_entropy hR (hc i))
    _ = _ := by simp [div_eq_mul_inv]

end
end SecondOrder
