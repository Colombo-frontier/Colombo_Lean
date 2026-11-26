import NCBall.ShadowState
import NCBall.OracleTranscript

/-! # First-disagreement coupling for the concrete hidden-room functions -/

noncomputable section
open Set Metric
namespace NCBall

variable {S Ω : Type*} [MeasurableSpace S] {n H : ℕ}

def realRoomReply (p : RoomQueryPolicy S n H) (M : ℕ) (ρ γ lam : ℝ)
    (c : Ω → ℕ → Space n) (V : Ω → Fin H → ℕ → Space n)
    (t : ℕ) (h : LinearHistory S t) (z : Ω) : ℝ :=
  chainValue M ρ γ lam (c z) (V z (p.handle t h)) (p.point t h)

def shadowRoomReply (p : RoomQueryPolicy S n H) (M q₀ : ℕ) (ρ γ lam : ℝ)
    (c : Ω → ℕ → Space n) (V : Ω → Fin H → ℕ → Space n)
    (t : ℕ) (h : LinearHistory S t) (z : Ω) : ℝ :=
  shadowValue M (shadowStage p ρ q₀ t h) ρ γ lam
    (c z) (V z (p.handle t h)) (p.point t h)

def shadowQueryBad (p : RoomQueryPolicy S n H) (M q₀ : ℕ) (ρ : ℝ)
    (c : Ω → ℕ → Space n) (t : ℕ) (h : LinearHistory S t) (z : Ω) : Prop :=
  earlyRoomHit M (shadowStage p ρ q₀ t h) ρ (c z) (p.point t h)

theorem concrete_shadow_reply_agrees (p : RoomQueryPolicy S n H) (M q₀ : ℕ)
    {ρ γ lam : ℝ} (hρ : 0 < ρ) (c : Ω → ℕ → Space n)
    (V : Ω → Fin H → ℕ → Space n) (t : ℕ) (h : LinearHistory S t) (z : Ω)
    (hs : ¬shadowQueryBad p M q₀ ρ c t h z) :
    realRoomReply p M ρ γ lam c V t h z = shadowRoomReply p M q₀ ρ γ lam c V t h z :=
  (shadowValue_eq_real_of_no_early_hit M _ hρ (c z) (V z (p.handle t h)) (p.point t h) hs).symm

theorem concrete_shadow_histories_agree (p : RoomQueryPolicy S n H) (M q₀ N : ℕ)
    {ρ γ lam : ℝ} (hρ : 0 < ρ) (c : Ω → ℕ → Space n)
    (V : Ω → Fin H → ℕ → Space n) (w : S × Ω)
    (hsafe : ∀ t < N, ¬shadowQueryBad p M q₀ ρ c t
      (oracleTranscript (shadowRoomReply p M q₀ ρ γ lam c V) t w) w.2) :
    ∀ t ≤ N,
      oracleTranscript (realRoomReply p M ρ γ lam c V) t w =
        oracleTranscript (shadowRoomReply p M q₀ ρ γ lam c V) t w :=
  oracleTranscript_eq_of_no_bad _ _ _ (concrete_shadow_reply_agrees p M q₀ hρ c V) N w hsafe

/-- The real algorithm cannot output in the terminal room under budget unless
the concrete shadow trajectory or its final output makes an early future hit. -/
theorem real_terminal_hit_implies_shadow_early_hit (p : RoomQueryPolicy S n H)
    {M q₀ N : ℕ} (hq : 0 < q₀) (hN : N < M * q₀)
    {ρ γ lam : ℝ} (hρ : 0 < ρ) (c : Ω → ℕ → Space n)
    (V : Ω → Fin H → ℕ → Space n) (out : LinearHistory S N → Space n) (w : S × Ω)
    (hterminal : out (oracleTranscript (realRoomReply p M ρ γ lam c V) N w) ∈
      closedBall (c w.2 M) ρ) :
    (∃ t < N, shadowQueryBad p M q₀ ρ c t
      (oracleTranscript (shadowRoomReply p M q₀ ρ γ lam c V) t w) w.2) ∨
      earlyRoomHit M (shadowStage p ρ q₀ N
        (oracleTranscript (shadowRoomReply p M q₀ ρ γ lam c V) N w)) ρ (c w.2)
          (out (oracleTranscript (shadowRoomReply p M q₀ ρ γ lam c V) N w)) := by
  classical
  by_cases hb : ∃ t < N, shadowQueryBad p M q₀ ρ c t
      (oracleTranscript (shadowRoomReply p M q₀ ρ γ lam c V) t w) w.2
  · exact Or.inl hb
  · right
    push_neg at hb
    have he := concrete_shadow_histories_agree p M q₀ N hρ c V w hb N le_rfl
    rw [he] at hterminal
    exact ⟨M, shadowStage_unfinished p ρ hq hN _, le_rfl, hterminal⟩

end NCBall
