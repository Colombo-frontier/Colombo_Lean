import NCBall.FullRoomHit

/-! # A complete finite-query terminal-room bound

The finite union over current and future rooms costs a polynomial prefactor.
This gives a larger absolute logarithmic dimension constant than the sharp
first-hit presentation, while preserving the intended lower-bound order.
-/

noncomputable section
open MeasureTheory Set Metric
open scoped BigOperators ENNReal
namespace NCBall

variable {R : Type*} [MeasurableSpace R] {n H M : ℕ}

def fullShadowEarlyEvent (p : RoomQueryPolicy R n H) (q₀ : ℕ) (ρ γ lam σ scale : ℝ)
    (t : ℕ) (x : LinearHistory R t → Space n) : Set (R × RoomLatents n H M) :=
  {w | let h := oracleTranscript (fullShadowReply p q₀ ρ γ lam σ scale) t w
    earlyRoomHit M (shadowStage p ρ q₀ t h) ρ (fullRoomCenters ρ scale w.2) (x h)}

theorem fullShadowEarlyEvent_eq_union (p : RoomQueryPolicy R n H) (q₀ : ℕ)
    (ρ γ lam σ scale : ℝ) (t : ℕ) (x : LinearHistory R t → Space n) :
    fullShadowEarlyEvent (M := M) p q₀ ρ γ lam σ scale t x =
      ⋃ j : Fin M, ⋃ k : Fin (M + 1),
        if j.val < k.val then fullShadowHit p q₀ ρ γ lam σ scale t j.val k.val x else ∅ := by
  classical
  ext w
  simp only [mem_iUnion]
  constructor
  · rintro ⟨k, hjk, hkM, hx⟩
    let r := shadowStage p ρ q₀ t
      (oracleTranscript (fullShadowReply p q₀ ρ γ lam σ scale) t w)
    have hr : r < M := lt_of_lt_of_le hjk hkM
    refine ⟨⟨r, hr⟩, ⟨k, by omega⟩, ?_⟩
    rw [if_pos hjk]
    exact ⟨rfl, hx⟩
  · rintro ⟨j, k, hw⟩
    split_ifs at hw with hjk
    · exact ⟨k.val, hw.1 ▸ hjk, by omega, hw.2⟩
    · exact False.elim hw

theorem fullShadowEarlyEvent_measurable (p : RoomQueryPolicy R n H) (q₀ : ℕ)
    (ρ γ lam σ scale : ℝ) (t : ℕ) (x : LinearHistory R t → Space n)
    (hx : Measurable x) :
    MeasurableSet (fullShadowEarlyEvent (M := M) p q₀ ρ γ lam σ scale t x) := by
  rw [fullShadowEarlyEvent_eq_union]
  apply MeasurableSet.iUnion
  intro j
  apply MeasurableSet.iUnion
  intro k
  split_ifs
  · exact fullShadowHit_measurable p q₀ ρ γ lam σ scale t j.val k.val x hx
  · exact MeasurableSet.empty

theorem full_shadow_early_hit_bound (ν : Measure R) [IsProbabilityMeasure ν]
    (p : RoomQueryPolicy R n H) {q₀ : ℕ} (hq : 0 < q₀) (hn : 0 < n)
    {ρ σ : ℝ} (hρ : 0 < ρ) (hσ : 0 < σ) (γ lam : ℝ)
    (hqcap : (q₀ : ℝ) ≤ n * σ ^ 2 / 16) (t : ℕ)
    (x : LinearHistory R t → Space n) (hx : Measurable x) :
    (ν.prod (roomLatentLaw n H M))
      (fullShadowEarlyEvent p q₀ ρ γ lam σ (Real.sqrt (n : ℝ))⁻¹ t x) ≤
      (M : ℝ≥0∞) * (M + 1) * ENNReal.ofReal (Real.exp (-(n : ℝ) / 8)) := by
  classical
  rw [fullShadowEarlyEvent_eq_union]
  let μ := ν.prod (roomLatentLaw n H M)
  let b := ENNReal.ofReal (Real.exp (-(n : ℝ) / 8))
  let A : Fin M → Fin (M + 1) → Set (R × RoomLatents n H M) := fun j k =>
    if j.val < k.val then fullShadowHit p q₀ ρ γ lam σ (Real.sqrt (n : ℝ))⁻¹ t j.val k.val x else ∅
  have ha (j : Fin M) (k : Fin (M + 1)) : μ (A j k) ≤ b := by
    dsimp only [A]
    split_ifs with hjk
    · exact full_shadow_future_hit_bound ν p j hjk hq hn hρ hσ γ lam hqcap t x hx
    · simp
  calc
    μ (⋃ j, ⋃ k, A j k) ≤ ∑ j, μ (⋃ k, A j k) := measure_iUnion_fintype_le _ _
    _ ≤ ∑ j, ∑ k, μ (A j k) := Finset.sum_le_sum fun j _ => measure_iUnion_fintype_le _ _
    _ ≤ ∑ _j : Fin M, ∑ _k : Fin (M + 1), b :=
      Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ => ha j k
    _ = _ := by simp [b, mul_assoc]

def fullRealTerminalEvent (p : RoomQueryPolicy R n H) (ρ γ lam σ scale : ℝ)
    (N : ℕ) (out : LinearHistory R N → Space n) : Set (R × RoomLatents n H M) :=
  {w | out (oracleTranscript (fullRealReply p ρ γ lam σ scale) N w) ∈
    closedBall (fullRoomCenters ρ scale w.2 M) ρ}

theorem full_chain_terminal_bound (ν : Measure R) [IsProbabilityMeasure ν]
    (p : RoomQueryPolicy R n H) {q₀ N : ℕ} (hq : 0 < q₀) (hN : N < M * q₀) (hn : 0 < n)
    {ρ σ : ℝ} (hρ : 0 < ρ) (hσ : 0 < σ) (γ lam : ℝ)
    (hqcap : (q₀ : ℝ) ≤ n * σ ^ 2 / 16)
    (out : LinearHistory R N → Space n) (hout : Measurable out) :
    (ν.prod (roomLatentLaw n H M))
      (fullRealTerminalEvent p ρ γ lam σ (Real.sqrt (n : ℝ))⁻¹ N out) ≤
      (N + 1 : ℝ≥0∞) * (M : ℝ≥0∞) * (M + 1) *
        ENNReal.ofReal (Real.exp (-(n : ℝ) / 8)) := by
  let scale := (Real.sqrt (n : ℝ))⁻¹
  let μ := ν.prod (roomLatentLaw n H M)
  let b := (M : ℝ≥0∞) * (M + 1) * ENNReal.ofReal (Real.exp (-(n : ℝ) / 8))
  let A := fun t : Fin N => fullShadowEarlyEvent (M := M) p q₀ ρ γ lam σ scale t.val (p.point t.val)
  let B := fullShadowEarlyEvent (M := M) p q₀ ρ γ lam σ scale N out
  have hcontain : fullRealTerminalEvent p ρ γ lam σ scale N out ⊆ (⋃ t, A t) ∪ B := by
    intro w hw
    have hc := real_terminal_hit_implies_shadow_early_hit p hq hN hρ
      (fullRoomCenters ρ scale) (latentSamples σ scale) out w hw
    rcases hc with ⟨t, ht, hh⟩ | hh
    · exact Or.inl (mem_iUnion.mpr ⟨⟨t, ht⟩, hh⟩)
    · exact Or.inr hh
  have ha (t : Fin N) : μ (A t) ≤ b :=
    full_shadow_early_hit_bound ν p hq hn hρ hσ γ lam hqcap t.val _ (p.measurable_point t.val)
  have hb : μ B ≤ b := full_shadow_early_hit_bound ν p hq hn hρ hσ γ lam hqcap N out hout
  calc
    μ (fullRealTerminalEvent p ρ γ lam σ scale N out) ≤ μ ((⋃ t, A t) ∪ B) := measure_mono hcontain
    _ ≤ μ (⋃ t, A t) + μ B := measure_union_le _ _
    _ ≤ (∑ t, μ (A t)) + b := add_le_add (measure_iUnion_fintype_le _ _) hb
    _ ≤ (∑ _t : Fin N, b) + b := add_le_add_right (Finset.sum_le_sum fun t _ => ha t) b
    _ = _ := by simp [b, add_mul, mul_assoc]

end NCBall
