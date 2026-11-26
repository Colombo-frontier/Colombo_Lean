import NCConcave16991.ConditionalHaarConeMachineSupport

/-! # Actual product-Haar probability bounds for the phased reference machine -/

open Set MeasureTheory
open scoped InnerProductSpace BigOperators

namespace NCConcave16991.Haar.ConeMachine

noncomputable section

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency true

attribute [local irreducible] runWithRows observedSupport

variable (k n M : ℕ) (R : ℝ) (hR : 0 < R)
  {Ω : Type*} [MeasurableSpace Ω]
  (P : OraclePolicy.AdaptivePolicy (Domain (FrameSpace k) M R hR) (n := n)
    (dx := ConeProblem.primalDimension (FrameSpace k) M) Ω)

def stageBad {N : ℕ} (hn : 0 < n) (q : ℝ) (e : Fin n ↪ Fin k) (j : Fin (M + 1))
    (time : Fin N → ℕ) (g : Fin N → Ω → State (FrameSpace k) n M R hR → FrameSpace k)
    (i : Fin N → Fin n) (r : ℝ) : Set (Ω × (Fin (M + 1) → OrthogonalGroup k)) :=
  {p | ∃ a, e (i a) ∉ observedSupport k n M R hR P p.1 hn q (frameRows k n M e p.2) e j (time a) ∧
    r ≤ |⟪g a p.1 (runWithRows (FrameSpace k) n M R hR P p.1 hn q (frameRows k n M e p.2) (time a)),
      orthogonalLinearIsometryEquiv (p.2 j) (basisVector (e (i a)))⟫_ℝ|}

theorem stageBad_measurable {N : ℕ} (hn : 0 < n) (q : ℝ) (e : Fin n ↪ Fin k) (j : Fin (M + 1))
    (time : Fin N → ℕ) (g : Fin N → Ω → State (FrameSpace k) n M R hR → FrameSpace k)
    (hg : ∀ a, Measurable (Function.uncurry (g a))) (i : Fin N → Fin n) (r : ℝ) :
    MeasurableSet (stageBad k n M R hR P hn q e j time g i r) := by
  have hrows : Measurable (fun p : Ω × (Fin (M + 1) → OrthogonalGroup k) ↦ frameRows k n M e p.2) :=
    (frameRows_measurable k n M e).comp measurable_snd
  have hrun (a : Fin N) : Measurable (fun p : Ω × (Fin (M + 1) → OrthogonalGroup k) ↦
      runWithRows (FrameSpace k) n M R hR P p.1 hn q (frameRows k n M e p.2) (time a)) :=
    (runWithRows_measurable (FrameSpace k) n M R hR P hn q (time a)).comp (measurable_fst.prodMk hrows)
  have hsupp (a : Fin N) : Measurable (fun p : Ω × (Fin (M + 1) → OrthogonalGroup k) ↦
      observedSupport k n M R hR P p.1 hn q (frameRows k n M e p.2) e j (time a)) :=
    (observedSupport_measurable k n M R hR P hn q e j (time a)).comp (measurable_fst.prodMk hrows)
  have hint (a : Fin N) : Measurable (fun p : Ω × (Fin (M + 1) → OrthogonalGroup k) ↦
      ⟪g a p.1 (runWithRows (FrameSpace k) n M R hR P p.1 hn q (frameRows k n M e p.2) (time a)),
        orthogonalLinearIsometryEquiv (p.2 j) (basisVector (e (i a)))⟫_ℝ) :=
    ((hg a).comp (measurable_fst.prodMk (hrun a))).inner
      ((continuous_orthogonalLinearIsometryEquiv_apply (basisVector (e (i a)))).measurable.comp
        ((measurable_pi_apply j).comp measurable_snd))
  have hbad (a : Fin N) : MeasurableSet {p : Ω × (Fin (M + 1) → OrthogonalGroup k) |
      e (i a) ∉ observedSupport k n M R hR P p.1 hn q (frameRows k n M e p.2) e j (time a) ∧
      r ≤ |⟪g a p.1 (runWithRows (FrameSpace k) n M R hR P p.1 hn q (frameRows k n M e p.2) (time a)),
        orthogonalLinearIsometryEquiv (p.2 j) (basisVector (e (i a)))⟫_ℝ|} :=
    ((hsupp a) (({A : Finset (Fin k) | e (i a) ∉ A} : Set (Finset (Fin k))).to_countable.measurableSet)).inter
      (measurableSet_le measurable_const (continuous_abs.measurable.comp (hint a)))
  simpa only [stageBad, Set.ofPred_exists] using MeasurableSet.iUnion hbad

/-- Every law and every query in this bound is literal: actual private seed,
independent finite Haar matrices, and the actual phased machine run. -/
theorem stageBad_mass_le {N : ℕ} (ν : Measure Ω) [IsProbabilityMeasure ν]
    (hn : 0 < n) (q : ℝ) (e : Fin n ↪ Fin k) (j : Fin (M + 1))
    (budget : ℕ) (hbudget : budget < k) (time : Fin N → ℕ) (htime : ∀ a, time a ≤ budget)
    (g : Fin N → Ω → State (FrameSpace k) n M R hR → FrameSpace k)
    (hg : ∀ a, Measurable (Function.uncurry (g a))) {C : ℝ} (hC : 0 ≤ C)
    (hgb : ∀ a seed s, ‖g a seed s‖ ≤ C) (i : Fin N → Fin n) {r : ℝ} (hr : 0 < r) :
    (ν.prod (rotationLaw k (M + 1))).real (stageBad k n M R hR P hn q e j time g i r) ≤
      (N : ℝ) * C ^ 2 / (((k - budget : ℕ) : ℝ) * r ^ 2) := by
  apply seeded_rotation_coordinate_event_bound ν j (stageBad_measurable k n M R hR P hn q e j time g hg i r)
  intro seed others
  have h := machine_finite_probe_union_tail k n M R hR P seed hn q e j
    (frameRows k n M e (Fin.insertNth j 1 others)) budget hbudget time htime
    (fun a ↦ g a seed) (fun a ↦ (hg a).comp (measurable_const.prodMk measurable_id))
    hC (fun a s ↦ hgb a seed s) i hr
  simpa only [stageBad, mem_ofPred_eq, combineRows_frame_insert, Fin.insertNth_apply_same,
    ColumnReveal.columnOracle] using h

def allStageBad {N : ℕ} (hn : 0 < n) (q : ℝ) (e : Fin n ↪ Fin k)
    (time : Fin N → ℕ) (g : Fin (M + 1) → Fin N → Ω → State (FrameSpace k) n M R hR → FrameSpace k)
    (i : Fin N → Fin n) (r : ℝ) : Set (Ω × (Fin (M + 1) → OrthogonalGroup k)) :=
  ⋃ j, stageBad k n M R hR P hn q e j time (g j) i r

theorem allStageBad_measurable {N : ℕ} (hn : 0 < n) (q : ℝ) (e : Fin n ↪ Fin k)
    (time : Fin N → ℕ) (g : Fin (M + 1) → Fin N → Ω → State (FrameSpace k) n M R hR → FrameSpace k)
    (hg : ∀ j a, Measurable (Function.uncurry (g j a))) (i : Fin N → Fin n) (r : ℝ) :
    MeasurableSet (allStageBad k n M R hR P hn q e time g i r) :=
  MeasurableSet.iUnion (fun j ↦ stageBad_measurable k n M R hR P hn q e j time (g j) (hg j) i r)

theorem allStageBad_mass_le {N : ℕ} (ν : Measure Ω) [IsProbabilityMeasure ν]
    (hn : 0 < n) (q : ℝ) (e : Fin n ↪ Fin k)
    (budget : ℕ) (hbudget : budget < k) (time : Fin N → ℕ) (htime : ∀ a, time a ≤ budget)
    (g : Fin (M + 1) → Fin N → Ω → State (FrameSpace k) n M R hR → FrameSpace k)
    (hg : ∀ j a, Measurable (Function.uncurry (g j a))) {C : ℝ} (hC : 0 ≤ C)
    (hgb : ∀ j a seed s, ‖g j a seed s‖ ≤ C) (i : Fin N → Fin n) {r : ℝ} (hr : 0 < r) :
    (ν.prod (rotationLaw k (M + 1))).real (allStageBad k n M R hR P hn q e time g i r) ≤
      (M + 1 : ℝ) * (N : ℝ) * C ^ 2 / (((k - budget : ℕ) : ℝ) * r ^ 2) := by
  calc
    _ ≤ ∑ j : Fin (M + 1), (ν.prod (rotationLaw k (M + 1))).real
        (stageBad k n M R hR P hn q e j time (g j) i r) := measureReal_iUnion_fintype_le _
    _ ≤ ∑ _j : Fin (M + 1), (N : ℝ) * C ^ 2 / (((k - budget : ℕ) : ℝ) * r ^ 2) :=
      Finset.sum_le_sum (fun j _ ↦ stageBad_mass_le k n M R hR P ν hn q e j budget hbudget time htime
        (g j) (hg j) hC (hgb j) i hr)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]; ring

end

end NCConcave16991.Haar.ConeMachine
