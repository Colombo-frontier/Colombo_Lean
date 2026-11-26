import Bilevel.TransportRoundRunProbability

/-! Explicit finite scalar calibration of the conservative observer bound.
The full actual-run failure budget is C/r with C independent of ambient
dimension. A positive integer residual rank can therefore attain any given
positive failure tolerance. -/
noncomputable section
open scoped ENNReal
namespace Bilevel.TransportRound
open TransportControllerMachine TransportControllerEdge
set_option maxHeartbeats 800000

def forwardNumerator (n p t : ℕ) : ℝ :=
  ((1+historyProbes n p 1 1 t : ℕ):ℝ)*(64*((size n p 1 1 t+p+1:ℕ):ℝ)^2)

def reverseNumerator (n p t : ℕ) : ℝ :=
  ((1+((size n p 1 1 t+p)+historyProbes n p 1 1 t) : ℕ):ℝ)*
    (64*(reverseDimension n (size n p 1 1 t+p):ℝ)^2)

def batchNumerator (n p t : ℕ) : ℝ := (n:ℝ)*(forwardNumerator n p t+reverseNumerator n p t)

def queryNumerator (n p T M : ℕ) (a : ℝ) : ℝ := ((M*((n+1)*p):ℕ):ℝ)*((T:ℝ)/a)

def runNumerator (n p T M : ℕ) (a : ℝ) : ℝ := queryNumerator n p T M a+∑ t : Fin M,batchNumerator n p t

theorem forwardNumerator_nonneg (n p t : ℕ) : 0≤forwardNumerator n p t := by unfold forwardNumerator; positivity
theorem reverseNumerator_nonneg (n p t : ℕ) : 0≤reverseNumerator n p t := by unfold reverseNumerator; positivity
theorem batchNumerator_nonneg (n p t : ℕ) : 0≤batchNumerator n p t :=
  mul_nonneg (Nat.cast_nonneg _) (add_nonneg (forwardNumerator_nonneg _ _ _) (reverseNumerator_nonneg _ _ _))
theorem queryNumerator_nonneg (n p T M : ℕ) {a : ℝ} (ha : 0<a) : 0≤queryNumerator n p T M a := by
  unfold queryNumerator
  positivity
theorem runNumerator_nonneg (n p T M : ℕ) {a : ℝ} (ha : 0<a) : 0≤runNumerator n p T M a :=
  add_nonneg (queryNumerator_nonneg _ _ _ _ ha) (Finset.sum_nonneg (fun _ _ => batchNumerator_nonneg _ _ _))

theorem nat_mul_ofReal_div (m r : ℕ) (x : ℝ) :
    (m:ℝ≥0∞)*ENNReal.ofReal (x/(r:ℝ))=ENNReal.ofReal (((m:ℝ)*x)/(r:ℝ)) := by
  rw [← ENNReal.ofReal_natCast m,← ENNReal.ofReal_mul (Nat.cast_nonneg m)]
  congr 1
  ring

theorem forwardBudget_eq (n p t r : ℕ) : forwardBudget n p t r=ENNReal.ofReal (forwardNumerator n p t/(r:ℝ)) :=
  nat_mul_ofReal_div _ _ _

theorem reverseBudget_eq (n p t r : ℕ) : reverseBudget n p t r=ENNReal.ofReal (reverseNumerator n p t/(r:ℝ)) :=
  nat_mul_ofReal_div _ _ _

theorem batchBudget_eq (n p t r : ℕ) : batchBudget n p t r=ENNReal.ofReal (batchNumerator n p t/(r:ℝ)) := by
  rw [batchBudget,forwardBudget_eq,reverseBudget_eq]
  rw [← ENNReal.ofReal_add (div_nonneg (forwardNumerator_nonneg n p t) (Nat.cast_nonneg r))
    (div_nonneg (reverseNumerator_nonneg n p t) (Nat.cast_nonneg r)),← add_div,nat_mul_ofReal_div]
  rfl

theorem queryBudget_eq (n p T M r : ℕ) (a : ℝ) :
    (M:ℝ≥0∞)*((n+1)*p:ℕ)*ENNReal.ofReal ((T:ℝ)/((r:ℝ)*a))=
      ENNReal.ofReal (queryNumerator n p T M a/(r:ℝ)) := by
  rw [show (T:ℝ)/((r:ℝ)*a)=((T:ℝ)/a)/(r:ℝ) by rw [div_div,mul_comm a]]
  rw [← Nat.cast_mul,nat_mul_ofReal_div]
  rfl

theorem runBudget_eq (n p T M r : ℕ) {a : ℝ} (ha : 0<a) :
    runBudget n p T M r a=ENNReal.ofReal (runNumerator n p T M a/(r:ℝ)) := by
  rw [runBudget,queryBudget_eq]
  simp_rw [batchBudget_eq]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun (t : Fin M) (_ : t∈Finset.univ) =>
    div_nonneg (batchNumerator_nonneg n p t) (Nat.cast_nonneg r))]
  rw [← Finset.sum_div]
  rw [← ENNReal.ofReal_add (div_nonneg (queryNumerator_nonneg n p T M ha) (Nat.cast_nonneg r))
    (div_nonneg (Finset.sum_nonneg (fun (t : Fin M) (_ : t∈Finset.univ) => batchNumerator_nonneg n p t)) (Nat.cast_nonneg r))]
  congr 1
  exact (add_div _ _ _).symm

def residualRank (n p T M : ℕ) (a δ : ℝ) : ℕ := max 1 (⌈runNumerator n p T M a/δ⌉₊)

theorem residualRank_pos (n p T M : ℕ) (a δ : ℝ) : 0<residualRank n p T M a δ := by
  unfold residualRank
  omega

theorem calibrated_runBudget (n p T M : ℕ) {a δ : ℝ} (ha : 0<a) (hδ : 0<δ) :
    runBudget n p T M (residualRank n p T M a δ) a≤ENNReal.ofReal δ := by
  rw [runBudget_eq n p T M _ ha]
  apply ENNReal.ofReal_le_ofReal
  have hr : (0:ℝ)<residualRank n p T M a δ := by exact_mod_cast residualRank_pos n p T M a δ
  apply (div_le_iff₀ hr).mpr
  have hceil : runNumerator n p T M a/δ≤(residualRank n p T M a δ:ℝ) := by
    apply (Nat.le_ceil _).trans
    exact_mod_cast (le_max_right 1 (⌈runNumerator n p T M a/δ⌉₊))
  simpa only [mul_comm] using (div_le_iff₀ hδ).mp hceil

end Bilevel.TransportRound
