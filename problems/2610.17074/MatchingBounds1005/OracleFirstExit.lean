import MatchingBounds1005.Model
import Mathlib.Tactic

/-! Exact deterministic first-exit coupling for arbitrary full-history
policies, including an unqueried final output. -/
noncomputable section

namespace MatchingBounds1005.Model

def replyTranscript {d : ℕ} {Seed : Type} [MeasurableSpace Seed]
    (reply : (t : ℕ) → Seed → (Fin t → Response d) → Response d) (seed : Seed) :
    (t : ℕ) → Fin t → Response d
  | 0 => Fin.elim0
  | t + 1 => Fin.snoc (replyTranscript reply seed t) (reply t seed (replyTranscript reply seed t))

theorem transcript_eq_replyTranscript {d : ℕ} {Seed : Type} [MeasurableSpace Seed]
    (A : Algorithm d Seed) (f : Space d → ℝ)
    (reply : (t : ℕ) → Seed → (Fin t → Response d) → Response d)
    (seed : Seed) (T : ℕ)
    (hexact : ∀ t, t < T → reply t seed (replyTranscript reply seed t) =
      oracle f (A.query t seed (replyTranscript reply seed t))) :
    transcript A f seed T = replyTranscript reply seed T := by
  induction T with
  | zero => rfl
  | succ t ih =>
    have hprev := ih (fun s hs => hexact s (Nat.lt_trans hs (Nat.lt_succ_self t)))
    simp only [transcript, replyTranscript, hprev, hexact t (Nat.lt_succ_self t)]

/-- An unqueried output consumes no response and is nevertheless included
in the event that precludes success. -/
def FirstExit {d T : ℕ} {Seed : Type} [MeasurableSpace Seed]
    (reply : (t : ℕ) → Seed → (Fin t → Response d) → Response d)
    (safe : (t : ℕ) → Seed → (Fin t → Response d) → Prop)
    (outputSafe : Seed → (Fin T → Response d) → Prop) : Set Seed :=
  {seed | (∃ t, t < T ∧ ¬ safe t seed (replyTranscript reply seed t)) ∨
    ¬ outputSafe seed (replyTranscript reply seed T)}

theorem success_subset_firstExit {d T : ℕ} {Seed : Type} [MeasurableSpace Seed]
    (A : Algorithm d Seed) (f : Space d → ℝ) (ε : ℝ)
    (reply : (t : ℕ) → Seed → (Fin t → Response d) → Response d)
    (safe : (t : ℕ) → Seed → (Fin t → Response d) → Prop)
    (outputSafe : Seed → (Fin T → Response d) → Prop)
    (hexact : ∀ t seed h, safe t seed h → reply t seed h = oracle f (A.query t seed h))
    (hcert : ∀ seed h, outputSafe seed h → ε < ‖gradient f (A.output T seed h)‖) :
    Success A f ε T ⊆ FirstExit reply safe outputSafe := by
  intro seed hs
  by_contra hn
  have hsafe : ∀ t, t < T → safe t seed (replyTranscript reply seed t) := by
    intro t ht
    by_contra hbad
    exact hn (Or.inl ⟨t, ht, hbad⟩)
  have hout : outputSafe seed (replyTranscript reply seed T) := by
    by_contra hbad
    exact hn (Or.inr hbad)
  have ht := transcript_eq_replyTranscript A f reply seed T
    (fun t hlt => hexact t seed _ (hsafe t hlt))
  have hc := hcert seed _ hout
  change ‖gradient f (A.output T seed (transcript A f seed T))‖ ≤ ε at hs
  rw [ht] at hs
  exact (not_lt_of_ge hs) hc

end MatchingBounds1005.Model
