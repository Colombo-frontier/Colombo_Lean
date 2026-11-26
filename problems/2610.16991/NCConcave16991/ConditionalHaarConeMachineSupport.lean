import NCConcave16991.ConditionalHaarConeMachineOptional
import NCConcave16991.ConeReferenceSupport

/-! # Actual observed Haar columns and the current unfinished source rows -/

open Set MeasureTheory

namespace NCConcave16991.Haar.ConeMachine

noncomputable section

variable (k n M : ℕ) (R : ℝ) (hR : 0 < R)
  {Ω : Type*} [MeasurableSpace Ω]
  (P : OraclePolicy.AdaptivePolicy (Domain (FrameSpace k) M R hR) (n := n)
    (dx := ConeProblem.primalDimension (FrameSpace k) M) Ω)

def observedSupport (seed : Ω) (hn : 0 < n) (q : ℝ)
    (rows : Fin (M + 1) → Fin n → FrameSpace k) (e : Fin n ↪ Fin k)
    (j : Fin (M + 1)) (t : ℕ) : Finset (Fin k) :=
  Finset.univ.biUnion (fun τ : Fin t ↦
    (selectedRead k n M R hR hn e j (runWithRows (FrameSpace k) n M R hR P seed hn q rows τ.val)).toFinset)

theorem selected_support_eq (seed : Ω) (hn : 0 < n) (q : ℝ) (e : Fin n ↪ Fin k)
    (j : Fin (M + 1)) (others : Fin (M + 1) → Fin n → FrameSpace k)
    (Q : OrthogonalGroup k) (t : ℕ) :
    OptionalReveal.support (selectedRead k n M R hR hn e j)
      (selectedUpdate k n M R hR P seed hn q j others)
      (initial (FrameSpace k) n M R hR) (ColumnReveal.columnOracle Q) t =
      observedSupport k n M R hR P seed hn q (combineRows k n M e j others Q) e j t := by
  unfold OptionalReveal.support observedSupport
  congr 1
  funext τ
  rw [selected_run_eq]

theorem mem_observedSupport_iff (seed : Ω) (hn : 0 < n) (q : ℝ)
    (rows : Fin (M + 1) → Fin n → FrameSpace k) (e : Fin n ↪ Fin k)
    (j : Fin (M + 1)) (t : ℕ) (i : Fin n) :
    e i ∈ observedSupport k n M R hR P seed hn q rows e j t ↔
      (j,i) ∈ rawSupport (FrameSpace k) n M R hR P seed hn q rows t := by
  constructor
  · intro h
    obtain ⟨τ, hτ, hm⟩ := Finset.mem_biUnion.mp h
    cases hr : request (FrameSpace k) n M R hR hn
        (runWithRows (FrameSpace k) n M R hR P seed hn q rows τ.val) with
    | inl _ => simp [selectedRead, hr] at hm
    | inr ri =>
      by_cases hj : ri.1 = j
      · have he : e i = e ri.2 := by
          simpa only [selectedRead, hr, Sum.elim_inr, if_pos hj, Option.toFinset_some,
            Finset.mem_singleton] using hm
        have hi : ri.2 = i := (e.injective he).symm
        apply (mem_rawSupport_iff (FrameSpace k) n M R hR P seed hn q rows t (j,i)).mpr
        refine ⟨τ.val, τ.isLt, ?_⟩
        have hp : ri = (j,i) := Prod.ext hj hi
        simpa only [hp] using hr
      · simp [selectedRead, hr, hj] at hm
  · intro h
    rcases (mem_rawSupport_iff (FrameSpace k) n M R hR P seed hn q rows t (j,i)).mp h with ⟨τ,hτ,hr⟩
    apply Finset.mem_biUnion.mpr
    exact ⟨⟨τ,hτ⟩, Finset.mem_univ _, by simp [selectedRead, hr]⟩

/-- The same small current seen set can be used for every unfinished stage. -/
theorem boundary_unseen_not_observed (seed : Ω) (hn : 0 < n) (q : ℝ)
    (rows : Fin (M + 1) → Fin n → FrameSpace k) (e : Fin n ↪ Fin k)
    (j : Fin (M + 1)) (t : ℕ) (i : Fin n)
    (hfuture : (boundary (FrameSpace k) n M R hR P seed hn q rows t).progress.1 ≤ j.val)
    (hi : i ∉ (boundary (FrameSpace k) n M R hR P seed hn q rows t).progress.2) :
    e i ∉ observedSupport k n M R hR P seed hn q rows e j ((n + 2) * t) := by
  intro hm
  have hr := (mem_observedSupport_iff k n M R hR P seed hn q rows e j _ i).mp hm
  exact hi (boundary_rawSupport_upper (FrameSpace k) n M R hR P seed hn q rows t (j,i) hr hfuture).2

theorem observedSupport_measurable (hn : 0 < n) (q : ℝ) (e : Fin n ↪ Fin k)
    (j : Fin (M + 1)) (t : ℕ) : Measurable
    (fun p : Ω × (Fin (M + 1) → Fin n → FrameSpace k) ↦ observedSupport k n M R hR P p.1 hn q p.2 e j t) := by
  have hm : Measurable (fun p : Ω × (Fin (M + 1) → Fin n → FrameSpace k) ↦
      fun τ : Fin t ↦ selectedRead k n M R hR hn e j
        (runWithRows (FrameSpace k) n M R hR P p.1 hn q p.2 τ.val)) :=
    measurable_pi_iff.mpr (fun τ ↦ (selectedRead_measurable k n M R hR hn e j).comp
      (runWithRows_measurable (FrameSpace k) n M R hR P hn q τ.val))
  exact (measurable_of_countable (fun v : Fin t → Option (Fin k) ↦
    Finset.univ.biUnion (fun τ ↦ (v τ).toFinset))).comp hm

/-- The actual optional-Haar tail applies to the actual phased machine,
after fixing every other rotation and the private seed. -/
theorem machine_finite_probe_union_tail {N : ℕ} (seed : Ω) (hn : 0 < n) (q : ℝ)
    (e : Fin n ↪ Fin k) (j : Fin (M + 1)) (others : Fin (M + 1) → Fin n → FrameSpace k)
    (budget : ℕ) (hbudget : budget < k) (time : Fin N → ℕ) (htime : ∀ t, time t ≤ budget)
    (g : Fin N → State (FrameSpace k) n M R hR → FrameSpace k) (hg : ∀ t, Measurable (g t))
    {C : ℝ} (hC : 0 ≤ C) (hgb : ∀ t s, ‖g t s‖ ≤ C)
    (i : Fin N → Fin n) {r : ℝ} (hr : 0 < r) :
    (haarLaw k).real {Q | ∃ t, e (i t) ∉ observedSupport k n M R hR P seed hn q
        (combineRows k n M e j others Q) e j (time t) ∧
      r ≤ |inner ℝ (g t (runWithRows (FrameSpace k) n M R hR P seed hn q
        (combineRows k n M e j others Q) (time t))) (ColumnReveal.columnOracle Q (e (i t)))|} ≤
      (N : ℝ) * C ^ 2 / (((k - budget : ℕ) : ℝ) * r ^ 2) := by
  have h := OptionalReveal.finite_adaptive_probe_union_tail
    (selectedRead k n M R hR hn e j) (selectedRead_measurable k n M R hR hn e j)
    (selectedUpdate k n M R hR P seed hn q j others)
    (selectedUpdate_measurable k n M R hR P seed hn q j others)
    (initial (FrameSpace k) n M R hR) budget hbudget time htime g hg hC hgb (fun t ↦ e (i t)) hr
  simpa only [selected_support_eq, selected_run_eq] using h

end

end NCConcave16991.Haar.ConeMachine
