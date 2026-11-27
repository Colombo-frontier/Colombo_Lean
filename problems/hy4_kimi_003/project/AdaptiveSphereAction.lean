import AdaptiveSphereState
import AdaptiveSphereEmbedding
import AdaptiveSphereOrbit

/-! The actual stopped residual action on the genuine Haar prior. Every object
is constructed from the canonical policy and its real scalar transcript. -/

open MeasureTheory Set ProbabilityTheory
open scoped Matrix

namespace Task006.AdaptiveSphereAction

open Task006.Full Task006.Full.OracleAlgorithm
open Task006.HaarRebalancing Task006.AdaptiveSphereBlock
open Task006.AdaptiveSphereFrame Task006.AdaptiveSphereResidualFrame
open Task006.AdaptiveSphereTranscript Task006.AdaptiveSphereMeasurable
open Task006.AdaptiveSphereState

noncomputable section

/-- A single fixed control space handles every possible residual rank. -/
abbrev ResidualControls (d : ℕ) := (r : Fin (d+1)) → OrthogonalGroup (d-r.val)

instance realMatrix_metrizable (d : ℕ) :
    TopologicalSpace.MetrizableSpace (Matrix (Fin d) (Fin d) ℝ) := by
  change TopologicalSpace.MetrizableSpace (Fin d → Fin d → ℝ)
  infer_instance

instance orthogonalGroup_metrizable (d : ℕ) :
    TopologicalSpace.MetrizableSpace (OrthogonalGroup d) := by
  change TopologicalSpace.MetrizableSpace
    (↥(unitary (Matrix (Fin d) (Fin d) ℝ) : Set (Matrix (Fin d) (Fin d) ℝ)))
  infer_instance

variable {d N : ℕ} {S Ω : Type*} [MeasurableSpace S]

def zeroRank (d : ℕ) : Fin (d+1) := ⟨0, by omega⟩

def rotateAtState (state : FrameState d) (control : ResidualControls d) : OrthogonalGroup d :=
  state.2 * blockOrthogonal d state.1.val (by omega) (control state.1) * state.2⁻¹

theorem rotateAtRank_continuous (r : Fin (d+1)) :
    Continuous (fun p : OrthogonalGroup d × ResidualControls d => rotateAtState (r,p.1) p.2) := by
  have hb : Continuous (Prod.fst : OrthogonalGroup d × ResidualControls d → OrthogonalGroup d) :=
    continuous_fst
  have hc : Continuous (fun p : OrthogonalGroup d × ResidualControls d => p.2 r) :=
    (continuous_apply r).comp continuous_snd
  have hblock := (blockOrthogonal_continuous d r.val (by omega)).comp hc
  have hresult := (hb.mul hblock).mul hb.inv
  change Continuous (fun p : OrthogonalGroup d × ResidualControls d =>
    p.1 * blockOrthogonal d r.val (by omega) (p.2 r) * p.1⁻¹) at hresult
  simpa only [rotateAtState] using hresult

theorem rotateAtState_joint_measurable :
    Measurable (fun p : FrameState d × ResidualControls d => rotateAtState p.1 p.2) := by
  have hfixed (r : Fin (d+1)) : Measurable
      (fun p : OrthogonalGroup d × ResidualControls d => rotateAtState (r,p.1) p.2) :=
    (rotateAtRank_continuous r).measurable
  have hall : Measurable (fun p : Fin (d+1) × (OrthogonalGroup d × ResidualControls d) =>
      rotateAtState (p.1,p.2.1) p.2.2) := measurable_from_prod_countable_right hfixed
  have hinput : Measurable (fun p : FrameState d × ResidualControls d =>
      (p.1.1,(p.1.2,p.2))) :=
    (measurable_fst.comp measurable_fst).prodMk
      ((measurable_snd.comp measurable_fst).prodMk measurable_snd)
  have hresult := hall.comp hinput
  simpa only [Function.comp_def] using hresult

theorem rotateAtState_control_continuous (state : FrameState d) :
    Continuous (rotateAtState state) := by
  have hresult := (rotateAtRank_continuous state.1).comp
    (continuous_const.prodMk continuous_id : Continuous
      (fun control : ResidualControls d => (state.2,control)))
  simpa only [Function.comp_def] using hresult

theorem blockOrthogonal_zero (g : OrthogonalGroup d) :
    blockOrthogonal d 0 (Nat.zero_le d) g = g := by
  apply Subtype.ext
  ext i j
  rw [blockOrthogonal_apply]
  simp only [not_lt_zero, dite_false, Nat.sub_zero]

theorem rotateAtState_initial (control : ResidualControls d) :
    rotateAtState (initialState d) control = control (zeroRank d) := by
  simp [rotateAtState, initialState, zeroRank, blockOrthogonal_zero]

def history (A : OracleAlgorithm d N S) (weight : Ω → ℝ) (tape : ℕ → Ω)
    (seed : S) (t : ℕ) (j : Fin d) (Q : OrthogonalGroup d) : Transcript N :=
  A.runPrefix (linearSample weight (column Q j)) tape seed t

def actualState (A : OracleAlgorithm d N S) (weight : Ω → ℝ) (tape : ℕ → Ω)
    (seed : S) (k : ℕ) (hkd : k ≤ d) (t : ℕ) (j : Fin d)
    (Q : OrthogonalGroup d) : FrameState d :=
  frameFromTranscript A weight tape seed k hkd t (history A weight tape seed t j Q)

def orbitTransform (A : OracleAlgorithm d N S) (weight : Ω → ℝ) (tape : ℕ → Ω)
    (seed : S) (k : ℕ) (hkd : k ≤ d) (t : ℕ) (j : Fin d)
    (control : ResidualControls d) (Q : OrthogonalGroup d) : OrthogonalGroup d :=
  rotateAtState (actualState A weight tape seed k hkd t j Q) control * Q

theorem measurable_history (A : OracleAlgorithm d N S) (weight : Ω → ℝ)
    (tape : ℕ → Ω) (seed : S) (t : ℕ) (j : Fin d) :
    Measurable (history A weight tape seed t j) := by
  have hresult := (measurable_linear_runPrefix A weight tape seed t).comp (measurable_column j)
  change Measurable (fun Q : OrthogonalGroup d =>
    A.runPrefix (linearSample weight (column Q j)) tape seed t)
  simpa only [Function.comp_def] using hresult

theorem measurable_actualState (A : OracleAlgorithm d N S) (weight : Ω → ℝ)
    (tape : ℕ → Ω) (seed : S) (k : ℕ) (hkd : k ≤ d) (t : ℕ) (j : Fin d) :
    Measurable (actualState A weight tape seed k hkd t j) := by
  have hresult := (measurable_frameFromTranscript A weight tape seed k hkd t).comp
    (measurable_history A weight tape seed t j)
  change Measurable (fun Q : OrthogonalGroup d =>
    frameFromTranscript A weight tape seed k hkd t (history A weight tape seed t j Q))
  simpa only [Function.comp_def] using hresult

theorem orbitTransform_joint_measurable (A : OracleAlgorithm d N S) (weight : Ω → ℝ)
    (tape : ℕ → Ω) (seed : S) (k : ℕ) (hkd : k ≤ d) (t : ℕ) (j : Fin d) :
    Measurable (fun p : ResidualControls d × OrthogonalGroup d =>
      orbitTransform A weight tape seed k hkd t j p.1 p.2) := by
  have hs := (measurable_actualState A weight tape seed k hkd t j).comp
    (measurable_snd : Measurable (Prod.snd : ResidualControls d × OrthogonalGroup d → OrthogonalGroup d))
  have hin := hs.prodMk
    (measurable_fst : Measurable (Prod.fst : ResidualControls d × OrthogonalGroup d → ResidualControls d))
  have hrot := (rotateAtState_joint_measurable (d := d)).comp hin
  simp only [Function.comp_def] at hrot
  have hmul : Measurable (fun p : OrthogonalGroup d × OrthogonalGroup d => p.1 * p.2) := measurable_mul
  have hresult := hmul.comp (hrot.prodMk measurable_snd)
  simpa only [orbitTransform, Function.comp_def] using hresult

theorem orbitTransform_control_continuous (A : OracleAlgorithm d N S) (weight : Ω → ℝ)
    (tape : ℕ → Ω) (seed : S) (k : ℕ) (hkd : k ≤ d) (t : ℕ) (j : Fin d)
    (Q : OrthogonalGroup d) :
    Continuous (fun control => orbitTransform A weight tape seed k hkd t j control Q) := by
  have hresult := (rotateAtState_control_continuous
    (actualState A weight tape seed k hkd t j Q)).mul_const Q
  simpa only [orbitTransform] using hresult

theorem orbitTransform_zero_measurePreserving (A : OracleAlgorithm d N S) (weight : Ω → ℝ)
    (tape : ℕ → Ω) (seed : S) (k : ℕ) (hkd : k ≤ d) (j : Fin d)
    (control : ResidualControls d) :
    MeasurePreserving (orbitTransform A weight tape seed k hkd 0 j control)
      (orthogonalHaarProbability d) (orthogonalHaarProbability d) := by
  let gzero : OrthogonalGroup d := control (zeroRank d)
  have heq : orbitTransform A weight tape seed k hkd 0 j control =
      (fun Q : OrthogonalGroup d => gzero * Q) := by
    funext Q
    simp only [orbitTransform, actualState, frameFromTranscript, rotateAtState_initial, gzero]
  rw [heq]
  exact measurePreserving_mul_left (orthogonalHaarProbability d) gzero

theorem orbitTransform_zero_fixes_history (A : OracleAlgorithm d N S) (weight : Ω → ℝ)
    (tape : ℕ → Ω) (seed : S) (k : ℕ) (hkd : k ≤ d) (j : Fin d)
    (control : ResidualControls d) (Q : OrthogonalGroup d) :
    history A weight tape seed 0 j (orbitTransform A weight tape seed k hkd 0 j control Q) =
      history A weight tape seed 0 j Q := rfl

#print axioms rotateAtState_joint_measurable
#print axioms measurable_actualState
#print axioms orbitTransform_joint_measurable
#print axioms orbitTransform_control_continuous
#print axioms orbitTransform_zero_measurePreserving
end
end Task006.AdaptiveSphereAction
