import NCConcave16991.ConeAdmissibility
import NCConcave16991.ConditionalHaarProduct

/-! # The static Haar-distributed family of actual admissible cone Problems

The domain, dimensions, public parameters and initial point are fixed before
the rotations. Only the literal source rows depend on the sampled matrices.
-/

noncomputable section

namespace NCConcave16991.ConeLower

open ConeProblem ConeSmooth Haar
open scoped InnerProductSpace

set_option backward.isDefEq.respectTransparency false

abbrev Ambient (k : ℕ) := EuclideanSpace ℝ (Fin k)
abbrev Rotations (k M : ℕ) := Fin (M + 1) → OrthogonalGroup k

def rowEmbedding {n k : ℕ} (h : n ≤ k) : Fin n ↪ Fin k where
  toFun := fun i ↦ ⟨i.val, i.isLt.trans_le h⟩
  inj' := fun _ _ hij ↦ Fin.ext (congrArg (fun v : Fin k ↦ v.val) hij)

abbrev normalizedParameters (n : ℕ) (hn : 0 < n) (M : ℕ)
    (R : ℝ) (hR : 0 < R) (q : ℝ) (hq : 1 ≤ q) : ProblemParameters :=
  ConeProblem.parameters n hn M individualConstant individualConstant_pos R hR q hq

def model {n k M : ℕ} (hn : 0 < n) (R : ℝ) (hR : 0 < R) (q : ℝ) (hq : 1 ≤ q)
    (e : Fin n ↪ Fin k) (Q : Rotations k M) :
    Problem (normalizedParameters n hn M R hR q hq)
      (primalDimension (Ambient k) M) (dualDimension (Ambient k) M)
      (dualDomain (Ambient k) M R hR) :=
  ConeProblem.problem hn individualConstant individualConstant_pos R hR q hq (rotatedRows e Q)
    (rotatedRows_orthonormal e Q)

theorem model_initialPoint {n k M : ℕ} (hn : 0 < n) (R : ℝ) (hR : 0 < R)
    (q : ℝ) (hq : 1 ≤ q) (e : Fin n ↪ Fin k) (Q : Rotations k M) :
    (model hn R hR q hq e Q).initialPoint = 0 := rfl

theorem model_individualSmooth {n k M : ℕ} (hn : 0 < n) {R q : ℝ}
    (hR : 1 ≤ R) (hq : 16 ≤ q) (hrel : Real.sqrt (n : ℝ) = q * R)
    (hq2 : Real.sqrt (n : ℝ) ≤ q ^ 2) (e : Fin n ↪ Fin k) (Q : Rotations k M) :
    (model hn R (by linarith) q (by linarith) e Q).individualSmooth :=
  ConeSmooth.problem_individualSmooth hn hR hq hrel hq2 (rotatedRows e Q) (rotatedRows_orthonormal e Q)

theorem model_averagedSmooth {n k M : ℕ} (hn : 0 < n) {R q : ℝ}
    (hR : 1 ≤ R) (hq : 16 ≤ q) (hrel : Real.sqrt (n : ℝ) = q * R)
    (hq2 : Real.sqrt (n : ℝ) ≤ q ^ 2) (e : Fin n ↪ Fin k) (Q : Rotations k M) :
    (model hn R (by linarith) q (by linarith) e Q).averagedSmooth :=
  (model hn R (by linarith) q (by linarith) e Q).individual_implies_averaged
    (model_individualSmooth hn hR hq hrel hq2 e Q)

end NCConcave16991.ConeLower
