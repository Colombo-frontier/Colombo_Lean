import SampleReuse.PersistentStageEntry
import SecondOrder.FiniteCoordinateResampling
import SecondOrder.FirstOrderReferenceActivation

/-! A finite product source groups each hidden sign block together with
all handles' biased arrays for that block. Different blocks are independent;
arrays of one block remain coupled to their common hidden sign. -/

open SecondOrder
open scoped Classical ENNReal BigOperators
namespace SampleReuse
noncomputable section
variable {d T : ℕ} {Handle S : Type}

abbrev PersistentBlock (d : ℕ) (Handle : Type) (R : ℝ) :=
  (Fin d → Bool) × (Handle → Fin d → SignedCoefficient R)

def persistentSourceHidden {R : ℝ} (w : Fin (T + 1) → PersistentBlock d Handle R) :
    Fin (T + 1) → Fin d → Bool := fun i => (w i).1

def persistentSourceTable {R : ℝ} (w : Fin (T + 1) → PersistentBlock d Handle R) :
    Handle → FirstOrderCoefficients d T R := fun r i => (w i).2 r

def persistentSourceRun (P : PersistentFirstOrderPolicy d T Handle S) (A β : ℝ) {R : ℝ}
    (w : Fin (T + 1) → PersistentBlock d Handle R) (n : ℕ) :=
  persistentComparisonRun P (persistentSourceHidden w) A β (persistentSourceTable w) n

def persistentSourceQuery (P : PersistentFirstOrderPolicy d T Handle S) (A β : ℝ) {R : ℝ}
    (w : Fin (T + 1) → PersistentBlock d Handle R) (n : ℕ) := P.query n (persistentSourceRun P A β w n).2

theorem persistentSourceRun_prefix (P : PersistentFirstOrderPolicy d T Handle S) (A β : ℝ) {R : ℝ}
    (w w' : Fin (T + 1) → PersistentBlock d Handle R) (n k : ℕ)
    (hw : ∀ i, i.val < k → w i = w' i) (hu : (persistentSourceRun P A β w n).1 + 1 ≤ k) :
    persistentSourceRun P A β w n = persistentSourceRun P A β w' n := by
  unfold persistentSourceRun at hu
  apply persistentComparison_prefix
  · intro i hi
    exact congrArg Prod.fst (hw i (by omega))
  · intro r i hi
    exact congrArg (fun b : PersistentBlock d Handle R => b.2 r) (hw i (by omega))

theorem persistentSource_unrevealed_iff (P : PersistentFirstOrderPolicy d T Handle S) (A β : ℝ) {R : ℝ}
    (w w' : Fin (T + 1) → PersistentBlock d Handle R) (n k : ℕ)
    (hw : ∀ i, i.val < k → w i = w' i) :
    (persistentSourceRun P A β w n).1 + 1 ≤ k ↔ (persistentSourceRun P A β w' n).1 + 1 ≤ k := by
  constructor
  · intro hu
    rw [← persistentSourceRun_prefix P A β w w' n k hw hu]
    exact hu
  · intro hu
    rw [persistentSourceRun_prefix P A β w' w n k (fun i hi => (hw i hi).symm) hu] at hu
    exact hu

theorem persistentSource_update_prefix {R : ℝ} (w : Fin (T + 1) → PersistentBlock d Handle R)
    (j : Fin (T + 1)) (b : PersistentBlock d Handle R) :
    ∀ i, i.val < j.val → w i = Function.update w j b i := by
  intro i hi
  exact (Function.update_of_ne (by intro he; subst i; omega) _ _).symm

variable [Fintype Handle]

def persistentBlockLaw (d : ℕ) (Handle : Type) [Fintype Handle] (R : ℝ) (hR : 2 ≤ R) :
    PMF (PersistentBlock d Handle R) :=
  finiteConditionalPMF (PMF.uniformOfFintype (Fin d → Bool))
    (fun θ => finitePiPMF (fun _ : Handle => firstOrderCoefficientLaw θ R hR))

def persistentSourceLaw (d T : ℕ) (Handle : Type) [Fintype Handle] (R : ℝ) (hR : 2 ≤ R) :
    PMF (Fin (T + 1) → PersistentBlock d Handle R) :=
  finitePiPMF (fun _ => persistentBlockLaw d Handle R hR)

theorem persistentBlockLaw_hidden_mean (R : ℝ) (hR : 2 ≤ R) (F : (Fin d → Bool) → ℝ) :
    pmfMean (persistentBlockLaw d Handle R hR) (fun b => F b.1) =
      pmfMean (PMF.uniformOfFintype (Fin d → Bool)) F :=
  finiteConditionalPMF_mean_fst _ _ F

def persistentFarCoordinate (P : PersistentFirstOrderPolicy d T Handle S) (A β : ℝ) {R : ℝ}
    (j : Fin (T + 1)) (n : ℕ) (w : Fin (T + 1) → PersistentBlock d Handle R) : Prop :=
  (persistentSourceRun P A β w n).1 + 1 ≤ j.val ∧
    0 < firstOrderBlockCompletion (w j).1 (firstOrderDilation d T β (persistentSourceQuery P A β w n).1 j)

/-- Far activation under the actual joint hidden/table product law. The
proof resamples the hidden vector together with all its reusable arrays,
so it never asserts independence between a sign and its biased arrays. -/
theorem persistent_far_coordinate_bound (P : PersistentFirstOrderPolicy d T Handle S)
    (A β R : ℝ) (hR : 2 ≤ R) (j : Fin (T + 1)) (n : ℕ) :
    pmfEventProbability (persistentSourceLaw d T Handle R hR)
      (fun w => decide (persistentFarCoordinate P A β j n w)) ≤ 2 * Real.exp (-(d : ℝ) / 128) := by
  rw [pmfEventProbability_mean]
  simp only [decide_eq_true_eq]
  unfold persistentSourceLaw
  rw [← finitePiPMF_resample_mean _ j]
  apply pmfMean_le_const
  intro w
  have hu (b : PersistentBlock d Handle R) := persistentSource_unrevealed_iff P A β w
    (Function.update w j b) n j.val (persistentSource_update_prefix w j b)
  by_cases hh : (persistentSourceRun P A β w n).1 + 1 ≤ j.val
  · have hq (b : PersistentBlock d Handle R) :
        persistentSourceQuery P A β (Function.update w j b) n = persistentSourceQuery P A β w n := by
      unfold persistentSourceQuery
      rw [← persistentSourceRun_prefix P A β w (Function.update w j b) n j.val
        (persistentSource_update_prefix w j b) hh]
    have he : (fun b : PersistentBlock d Handle R =>
        if persistentFarCoordinate P A β j n (Function.update w j b) then (1 : ℝ) else 0) =
        (fun b => if 0 < firstOrderBlockCompletion b.1
          (firstOrderDilation d T β (persistentSourceQuery P A β w n).1 j) then 1 else 0) := by
      funext b
      simp only [persistentFarCoordinate, (hu b).mp hh, true_and, Function.update_self, hq b]
    rw [he, persistentBlockLaw_hidden_mean (Handle := Handle) R hR
      (fun θ => if 0 < firstOrderBlockCompletion θ
        (firstOrderDilation d T β (persistentSourceQuery P A β w n).1 j) then 1 else 0)]
    simpa only [pmfEventProbability_mean, decide_eq_true_eq] using
      firstOrderBlockCompletion_activation_pmf
        (firstOrderDilation d T β (persistentSourceQuery P A β w n).1 j)
  · have he : (fun b : PersistentBlock d Handle R =>
        if persistentFarCoordinate P A β j n (Function.update w j b) then (1 : ℝ) else 0) = fun _ => 0 := by
      funext b
      simp only [persistentFarCoordinate, (hu b).not.mp hh, false_and, if_false]
    rw [he, pmfMean_const]
    positivity

end
end SampleReuse
