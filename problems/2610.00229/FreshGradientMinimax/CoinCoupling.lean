import FreshGradientMinimax.CoinTranscript

/-! A fixed coin word can be used in the unstopped, pathwise transcript
coupling. This connects finite iid words to the existing first-exit theorem. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax
open MeasureTheory ProbabilityTheory

def coinRead {N : ℕ} (w : Fin N → Bool) (t : ℕ) : Bool :=
  if h : t < N then w ⟨t, h⟩ else false

theorem coinRead_fin {N : ℕ} (w : Fin N → Bool) (i : Fin N) : coinRead w i.val = w i := by
  simp only [coinRead, dif_pos i.isLt]

namespace Algorithm
variable {dx dy : ℕ} {Seed : Type*} [MeasurableSpace Seed] (A : Algorithm dx dy Seed)

theorem coinRun_time (q : Bool → Joint dx dy → Joint dx dy) (c : ℕ → Bool) (N : ℕ) (seed : Seed) :
    A.coinRun q N (fun i => c i.val) seed = A.deterministicRun (fun t => q (c t)) N seed := by
  induction N with
  | zero => rfl
  | succ n ih =>
    simpa only [coinRun, deterministicRun, Fin.val_last] using
      congrArg (A.deterministicStep (q (c n)) n) ih

theorem coinRun_eq_deterministicRun (q : Bool → Joint dx dy → Joint dx dy)
    {N : ℕ} (w : Fin N → Bool) (seed : Seed) :
    A.coinRun q N w seed = A.deterministicRun (fun t => q (coinRead w t)) N seed := by
  have h := A.coinRun_time q (coinRead w) N seed
  simpa only [coinRead_fin] using h

theorem coin_first_exit_output_identity (q : Bool → Joint dx dy → Joint dx dy)
    (qaux : ℕ → Joint dx dy → Joint dx dy) {N : ℕ} (w : Fin N → Bool) (seed : Seed)
    (hlocal : ∀ t < N,
      q (coinRead w t) (A.query t (A.deterministicRun qaux t seed)) =
        qaux t (A.query t (A.deterministicRun qaux t seed))) :
    A.output N (A.coinRun q N w seed) = A.output N (A.deterministicRun qaux N seed) := by
  rw [A.coinRun_eq_deterministicRun]
  exact A.first_exit_output_identity _ qaux seed N hlocal

end Algorithm
end FreshGradientMinimax
