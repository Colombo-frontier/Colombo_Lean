import Bilevel.TransportAuxiliaryFrameEvent
import Bilevel.TransportAuxiliaryFrameSchedule

/-! The actual original-prior execution, its Borel dependence on all draws,
and literal selected-frame replay. Every query/terminal insertion below
uses this same execution, not an independently reconstructed shadow run. -/
noncomputable section
open MeasureTheory
universe u v
namespace Bilevel.TransportAuxiliaryFrame
open EuclideanGaussian
set_option autoImplicit false
variable {C : Type u} {S : Type v} [MeasurableSpace C] [MeasurableSpace S]
  {n D k T B : ℕ}

def originalRun (P : Schedule (k+1) T)
    (A : Driver (C × TransportNetwork.Latent n D) S (k+1) T D B)
    (hT : T+1 ≤ D) (initial : C × TransportNetwork.Latent n D → S)
    (p : C × TransportNetworkAuxiliary.Sample n D (k+1)) (N : ℕ) :=
  run P A N 0 (originalInitial initial p) (originalColumns hT p.2)

theorem originalColumns_measurable (hT : T+1 ≤ D) :
    Measurable (originalColumns (n:=n) (k:=k) hT) := by
  apply measurable_pi_lambda
  intro i
  exact TransportNetworkAuxiliary.auxiliary_frame_measurable (T+1) hT i

theorem originalRun_measurable (P : Schedule (k+1) T)
    (A : Driver (C × TransportNetwork.Latent n D) S (k+1) T D B)
    (hT : T+1 ≤ D) (initial : C × TransportNetwork.Latent n D → S)
    (hi : Measurable initial) (N : ℕ) :
    Measurable (fun p => originalRun P A hT initial p N) := by
  let Z := C × TransportNetworkAuxiliary.Sample n D (k+1)
  have hc : Measurable (fun p : Z => (p.1,p.2.1)) :=
    measurable_fst.prodMk (measurable_fst.comp measurable_snd)
  have hs : Measurable (fun p : Z => originalInitial (T:=T) initial p) :=
    hc.prodMk ((hi.comp hc).prodMk measurable_const)
  have hU : Measurable (fun p : Z => originalColumns hT p.2) :=
    (originalColumns_measurable (n:=n) hT).comp measurable_snd
  exact (run_measurable P A N 0).comp (hs.prodMk hU)

theorem originalRun_prefix (P : Schedule (k+1) T)
    (A : Driver (C × TransportNetwork.Latent n D) S (k+1) T D B)
    (hT : T+1 ≤ D) (initial : C × TransportNetwork.Latent n D → S)
    (p : C × TransportNetworkAuxiliary.Sample n D (k+1)) (N : ℕ) :
    (originalRun P A hT initial p N).2.2=actualStore P N (originalColumns hT p.2) :=
  run_initialStore P A N (p.1,p.2.1) (initial (p.1,p.2.1)) (originalColumns hT p.2)

theorem originalRun_valid_prefix (P : Schedule (k+1) T)
    (A : Driver (C × TransportNetwork.Latent n D) S (k+1) T D B)
    (hT : T+1 ≤ D) (initial : C × TransportNetwork.Latent n D → S)
    (p : C × TransportNetworkAuxiliary.Sample n D (k+1)) (N : ℕ) (i : Fin (k+1)) :
    ChiPrefixEvaluation.ValidStore T ((originalRun P A hT initial p N).2.2 i) := by
  rw [originalRun_prefix]
  exact ChiPrefixEvaluation.actualStore_valid T (P.count N i) (originalColumns hT p.2 i)
    (P.bound N i) (TransportNetworkAuxiliary.auxiliary_frame_orthonormal (T+1) hT i p.2)

theorem original_selected_replay (P : Schedule (k+1) T)
    (A : Driver (C × TransportNetwork.Latent n D) S (k+1) T D B)
    (hT : T+1 ≤ D) (i : Fin (k+1)) (hB : 0 < B)
    (initial : C × TransportNetwork.Latent n D → S)
    (p : C × TransportNetworkAuxiliary.Sample n D (k+1)) (N : ℕ) :
    SourceFrameActions.run (selectedBatchRules P A i hB) (N*B) 0
      (selectedInitial hT i initial (IndependentFrame.auxiliaryExpose hT i p).1)
      (IndependentFrame.auxiliaryExpose hT i p).2 =
      (otherColumns hT i (fun l => p.2.2 (i.succAbove l)),originalRun P A hT initial p N) := by
  simpa only [Nat.zero_mul] using selected_batch_run_actual P A i hB N 0
    (otherColumns hT i (fun l => p.2.2 (i.succAbove l))) (originalColumns hT p.2)
    (fun j hj => otherColumns_agree hT i p.2 j hj) (originalInitial initial p)

theorem original_query_mem (P : Schedule (k+1) T)
    (A : Driver (C × TransportNetwork.Latent n D) S (k+1) T D B)
    (hT : T+1 ≤ D) (i : Fin (k+1)) (hB : 0 < B)
    (initial : C × TransportNetwork.Latent n D → S)
    (p : C × TransportNetworkAuxiliary.Sample n D (k+1)) (N : ℕ) (b : Fin B) :
    A.queries N (originalRun P A hT initial p N) b ∈
      preSpace P A i hB N (otherColumns hT i (fun l => p.2.2 (i.succAbove l)))
        (originalColumns hT p.2) (originalInitial initial p) :=
  query_mem_preSpace P A i hB N _ _ (fun j hj => otherColumns_agree hT i p.2 j hj) _ b

theorem original_output_mem (P : Schedule (k+1) T)
    (A : Driver (C × TransportNetwork.Latent n D) S (k+1) T D B)
    (hT : T+1 ≤ D) (i : Fin (k+1)) (hB : 0 < B)
    (initial : C × TransportNetwork.Latent n D → S)
    (p : C × TransportNetworkAuxiliary.Sample n D (k+1)) (N : ℕ) :
    A.output (originalRun P A hT initial p N) ∈
      terminalSpace P A i hB N (otherColumns hT i (fun l => p.2.2 (i.succAbove l)))
        (originalColumns hT p.2) (originalInitial initial p) :=
  output_mem_terminalSpace P A i hB N _ _ (fun j hj => otherColumns_agree hT i p.2 j hj) _

end Bilevel.TransportAuxiliaryFrame
