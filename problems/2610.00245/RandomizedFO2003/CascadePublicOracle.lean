import RandomizedFO2003.CascadeReconstruction
import RandomizedFO2003.CascadeFamily

namespace RandomizedFO2003.Cascade

open Primitives MeasureTheory

variable {N : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- All three coefficients of the chosen block are removed from the public
data. They can subsequently enter only through the permitted answers. -/
noncomputable def Data.publicData (d : Data N E) (i : Fin (N + 1)) : Data N E :=
  ((d.censorGate i).replaceForce i 0).eraseOperator i

theorem Data.publicData_updated (d : Data N E) (i : Fin (N + 1))
    (A : E →L[ℝ] E) (a b : E) :
    ({ d with
      A := Function.update d.A i A
      a := Function.update d.a i a
      b := Function.update d.b i b } : Data N E).publicData i = d.publicData i := by
  simp [publicData, censorGate, replaceForce, eraseOperator, Function.update_idem]

theorem Data.oracleAuthorized_publicData (d : Data N E) (i : Fin (N + 1))
    (z : BlockProduct (N + 1) E) : (d.publicData i).oracleAuthorized i z = d.oracleAuthorized i z := by
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · have hne : j.castSucc ≠ j.succ := by intro h; have := congrArg Fin.val h; simp at this
    simp only [Data.oracleAuthorized, Fin.cases_succ, publicData, censorGate, replaceForce,
      eraseOperator, Function.update_of_ne hne]

variable [CompleteSpace E]

/-- The reconstruction formula factors through genuinely public data;
in particular it has no access to the current hidden readout direction. -/
theorem Data.reconstruct_publicData (d : Data N E) (i : Fin (N + 1))
    (b v : E) (z : BlockProduct (N + 1) E) :
    (d.publicData i).reconstruct i b v z = d.reconstruct i b v z := by
  simp [reconstruct, publicData, censorGate, replaceForce, eraseOperator, Function.update_idem]

/-- A public decoder reconstructs the fixed censored oracle on every query. -/
theorem Data.public_reconstruction (d : Data N E) (i : Fin (N + 1))
    (hA : IsSelfAdjoint (d.A i)) (z : BlockProduct (N + 1) E) :
    (d.publicData i).reconstruct i
      (if (d.publicData i).oracleAuthorized i z = true then d.b i else 0)
      (d.A i (z i)) z = (d.censorGate i).blockOracle z := by
  rw [d.reconstruct_publicData, d.oracleAuthorized_publicData, d.reconstruct_authorized_or_zero i hA z]

end RandomizedFO2003.Cascade
