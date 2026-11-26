import MatchingBounds1005.ReferenceState
import MatchingBounds1005.ResponseHistory

/-! Assembling physical first-order responses in the accessible reference state. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory

namespace MatchingBounds1005.ReferenceState
open GaussianVector TensorChannelRows GaussianNoiseStream FiniteGaussianSampler
open TensorGeometry hiding Vec

variable {Seed : Type} [MeasurableSpace Seed] {d H N : ℕ}

def cubicResponse (j : ℕ) (y : Fin (H * (d + d)) → ℝ) : Vec d :=
  (EuclideanSpace.measurableEquiv (Fin d)).symm
    (fun i => ResponseHistory.currentBlock j y (Fin.castAdd d i))

def quarticResponse (j : ℕ) (y : Fin (H * (d + d)) → ℝ) : Vec d :=
  (EuclideanSpace.measurableEquiv (Fin d)).symm
    (fun i => ResponseHistory.currentBlock j y (Fin.natAdd d i))

theorem cubicResponse_measurable (j : ℕ) : Measurable (cubicResponse (d := d) (H := H) j) := by
  apply (EuclideanSpace.measurableEquiv (Fin d)).symm.measurable.comp
  apply measurable_pi_lambda
  intro i
  exact (measurable_pi_apply (Fin.castAdd d i)).comp (ResponseHistory.currentBlock_measurable j)

theorem quarticResponse_measurable (j : ℕ) : Measurable (quarticResponse (d := d) (H := H) j) := by
  apply (EuclideanSpace.measurableEquiv (Fin d)).symm.measurable.comp
  apply measurable_pi_lambda
  intro i
  exact (measurable_pi_apply (Fin.natAdd d i)).comp (ResponseHistory.currentBlock_measurable j)

abbrev Result (Seed : Type) (d H N : ℕ) := State Seed d H N ×
  (Vec d × (Fin (H * (d + d)) → ℝ))

def assembled (A : Model.Algorithm d Seed) (constant R η : ℝ)
    (correction : (Fin N → Vec d) × Vec d → Model.Response d)
    (j : ℕ) (p : Result Seed d H N) : Model.Response d :=
  confineResponse R η (queryPoint A j p.1)
    (dataResponse constant (confinedQuery A R j p.1) p.1.2.1.2 p.2.1
      (cubicResponse j p.2.2) (quarticResponse j p.2.2)
      (correction (p.1.2.1.1, confinedQuery A R j p.1)))

theorem assembled_measurable (A : Model.Algorithm d Seed) (constant R η : ℝ)
    (correction : (Fin N → Vec d) × Vec d → Model.Response d) (hc : Measurable correction)
    (j : ℕ) : Measurable (assembled (H := H) A constant R η correction j) := by
  have hx : Measurable (fun p : Result Seed d H N => queryPoint A j p.1) :=
    (queryPoint_measurable A j).comp measurable_fst
  have hz : Measurable (fun p : Result Seed d H N => confinedQuery A R j p.1) :=
    (confinedQuery_measurable A R j).comp measurable_fst
  have hb : Measurable (fun p : Result Seed d H N => correction (p.1.2.1.1, confinedQuery A R j p.1)) :=
    hc.comp (measurable_fst.snd.fst.fst.prodMk hz)
  have h3 := (cubicResponse_measurable (d := d) (H := H) j).comp
    (measurable_snd.snd : Measurable (fun p : Result Seed d H N => p.2.2))
  have h4 := (quarticResponse_measurable (d := d) (H := H) j).comp
    (measurable_snd.snd : Measurable (fun p : Result Seed d H N => p.2.2))
  have hvec : Measurable (fun p : Result Seed d H N =>
      ![confinedQuery A R j p.1, p.1.2.1.2, p.2.1, cubicResponse j p.2.2, quarticResponse j p.2.2]) := by
    apply measurable_pi_lambda
    intro i
    fin_cases i
    · exact hz
    · exact measurable_fst.snd.fst.snd
    · exact measurable_snd.fst
    · exact h3
    · exact h4
  have hd := (dataResponse_continuous (d := d) constant).measurable.comp (hvec.prodMk hb)
  exact (confineResponse_continuous (d := d) R η).measurable.comp (hx.prodMk hd)

def finishQuery (A : Model.Algorithm d Seed) (constant R η σ₃ σ₄ : ℝ)
    (correction : (Fin N → Vec d) × Vec d → Model.Response d)
    (j : ℕ) (p : Result Seed d H N) : State Seed d H N :=
  (p.1.1, (p.1.2.1,
    (Function.update p.1.2.2.1 j (assembled A constant R η correction j p),
      (queryRows A σ₃ σ₄ R j p.1, p.2.2))))

theorem finishQuery_measurable (A : Model.Algorithm d Seed) (constant R η σ₃ σ₄ : ℝ)
    (correction : (Fin N → Vec d) × Vec d → Model.Response d) (hc : Measurable correction)
    (j : ℕ) : Measurable (finishQuery (H := H) A constant R η σ₃ σ₄ correction j) := by
  have hh : Measurable (fun p : Result Seed d H N =>
      Function.update p.1.2.2.1 j (assembled A constant R η correction j p)) := by
    apply measurable_pi_lambda
    intro k
    by_cases hk : k = j
    · subst k
      simpa only [Function.update_self] using assembled_measurable A constant R η correction hc j
    · simpa only [Function.update_of_ne hk] using
        (measurable_pi_apply k).comp (measurable_fst.snd.snd.fst :
          Measurable (fun p : Result Seed d H N => p.1.2.2.1))
  exact measurable_fst.fst.prodMk (measurable_fst.snd.fst.prodMk
    (hh.prodMk (((queryRows_measurable A σ₃ σ₄ R j).comp measurable_fst).prodMk measurable_snd.snd)))

def sourceQueryCommand (A : Model.Algorithm d Seed) (constant τ a σ₃ σ₄ R η : ℝ)
    (correction : (Fin N → Vec d) × Vec d → Model.Response d) (hc : Measurable correction)
    (j : ℕ) : ScheduledHaar.PhysicalRequest (E := Vec d) (State Seed d H N) ×
      AccessibleReferenceCompiler.Update (E := Vec d) (State Seed d H N) :=
  GaussianReferenceCommand.queryCommand 1 (confinedQuery A R j) (confinedQuery_measurable A R j)
    (queryInput A τ a σ₃ σ₄ R j) (queryInput_measurable A τ a σ₃ σ₄ R j)
    (privateNoise j) (privateNoise_measurable j)
    (finishQuery A constant R η σ₃ σ₄ correction j) (finishQuery_measurable A constant R η σ₃ σ₄ correction hc j)

end MatchingBounds1005.ReferenceState
