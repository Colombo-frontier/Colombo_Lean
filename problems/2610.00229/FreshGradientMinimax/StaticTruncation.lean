import FreshGradientMinimax.MaskedKernel

/-! The static truncation index in (30), with zero-based stage indices. There
are T+1 primal stages and two dual link coordinates at each noninitial stage.
The index depends only on the query, never on a transcript or past reveals. -/

set_option autoImplicit false
noncomputable section
namespace FreshGradientMinimax
open MeasureTheory

def staticStage (T : ℕ) (active : Fin (T + 1) → Prop) : ℕ := by
  classical
  exact Finset.univ.sup (fun i => if active i then i.val else 0)

theorem staticStage_le_iff (T : ℕ) (active : Fin (T + 1) → Prop) (k : ℕ) :
    staticStage T active ≤ k ↔ ∀ i, active i → i.val ≤ k := by
  classical
  unfold staticStage
  rw [Finset.sup_le_iff]
  constructor
  · intro h i hi
    simpa only [if_pos hi] using h i (Finset.mem_univ i)
  · intro h i _
    split_ifs with hi
    · exact h i hi
    · exact Nat.zero_le _

theorem staticStage_le (T : ℕ) (active : Fin (T + 1) → Prop) : staticStage T active ≤ T :=
  (staticStage_le_iff _ _ _).mpr (fun i _ => Nat.le_of_lt_succ i.isLt)

theorem active_le_staticStage {T : ℕ} (active : Fin (T + 1) → Prop)
    (i : Fin (T + 1)) (hi : active i) : i.val ≤ staticStage T active :=
  (staticStage_le_iff _ _ _).mp le_rfl i hi

theorem inactive_above_staticStage {T : ℕ} (active : Fin (T + 1) → Prop)
    (i : Fin (T + 1)) (hi : staticStage T active < i.val) : ¬active i := by
  intro ha
  exact (not_lt_of_ge (active_le_staticStage active i ha)) hi

theorem measurable_finite_nat_sup {Q I : Type*} [MeasurableSpace Q]
    (s : Finset I) (f : I → Q → ℕ) (hf : ∀ i ∈ s, Measurable (f i)) :
    Measurable (fun q => s.sup (fun i => f i q)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    simp only [Finset.sup_insert]
    exact (hf i (Finset.mem_insert_self i s)).sup
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

theorem staticStage_measurable {Q : Type*} [MeasurableSpace Q] (T : ℕ)
    (active : Q → Fin (T + 1) → Prop)
    (ha : ∀ i, MeasurableSet {q | active q i}) : Measurable (fun q => staticStage T (active q)) := by
  classical
  apply measurable_finite_nat_sup
  intro i _
  exact Measurable.ite (ha i) measurable_const measurable_const

def thresholdActive {T : ℕ} (r : ℝ) (u : Fin (T + 1) → ℝ)
    (v : Fin (T + 1) → Bool → ℝ) (i : Fin (T + 1)) : Prop :=
  1 / 4 < |u i| ∨ (i.val ≠ 0 ∧ (r < |v i true| ∨ r < |v i false|))

def thresholdStage {T : ℕ} (r : ℝ) (u : Fin (T + 1) → ℝ)
    (v : Fin (T + 1) → Bool → ℝ) : ℕ := staticStage T (thresholdActive r u v)

theorem thresholdStage_le {T : ℕ} (r : ℝ) (u : Fin (T + 1) → ℝ)
    (v : Fin (T + 1) → Bool → ℝ) : thresholdStage r u v ≤ T := staticStage_le _ _

theorem thresholdStage_hidden {T : ℕ} (r : ℝ) (u : Fin (T + 1) → ℝ)
    (v : Fin (T + 1) → Bool → ℝ) (i : Fin (T + 1)) (hi : thresholdStage r u v < i.val) :
    |u i| ≤ 1 / 4 ∧ |v i true| ≤ r ∧ |v i false| ≤ r := by
  have hn := inactive_above_staticStage (thresholdActive r u v) i hi
  have hi0 : i.val ≠ 0 := by omega
  exact ⟨le_of_not_gt (fun h => hn (Or.inl h)),
    le_of_not_gt (fun h => hn (Or.inr ⟨hi0, Or.inl h⟩)),
    le_of_not_gt (fun h => hn (Or.inr ⟨hi0, Or.inr h⟩))⟩

theorem thresholdStage_at_most {T : ℕ} (r : ℝ) (u : Fin (T + 1) → ℝ)
    (v : Fin (T + 1) → Bool → ℝ) (k : ℕ)
    (h : ∀ i : Fin (T + 1), k < i.val →
      |u i| ≤ 1 / 4 ∧ |v i true| ≤ r ∧ |v i false| ≤ r) : thresholdStage r u v ≤ k := by
  apply (staticStage_le_iff _ _ _).mpr
  intro i hi
  by_contra hik
  have hh := h i (Nat.lt_of_not_ge hik)
  rcases hi with hu | ⟨_, ht | hf⟩
  · exact (not_lt_of_ge hh.1) hu
  · exact (not_lt_of_ge hh.2.1) ht
  · exact (not_lt_of_ge hh.2.2) hf

theorem thresholdStage_measurable {Q : Type*} [MeasurableSpace Q] {T : ℕ} (r : ℝ)
    (u : Q → Fin (T + 1) → ℝ) (v : Q → Fin (T + 1) → Bool → ℝ)
    (hu : ∀ i, Measurable (fun q => u q i)) (hv : ∀ i b, Measurable (fun q => v q i b)) :
    Measurable (fun q => thresholdStage r (u q) (v q)) := by
  apply staticStage_measurable
  intro i
  unfold thresholdActive
  have hp : MeasurableSet {q | (1 / 4 : ℝ) < |u q i|} :=
    measurableSet_lt measurable_const (continuous_abs.measurable.comp (hu i))
  have ht : MeasurableSet {q | r < |v q i true|} :=
    measurableSet_lt measurable_const (continuous_abs.measurable.comp (hv i true))
  have hf : MeasurableSet {q | r < |v q i false|} :=
    measurableSet_lt measurable_const (continuous_abs.measurable.comp (hv i false))
  have hc : MeasurableSet {q : Q | i.val ≠ 0} := by
    by_cases hi : i.val = 0 <;> simp [hi]
  exact hp.union (hc.inter (ht.union hf))

def thresholdStageIndex {T : ℕ} (r : ℝ) (u : Fin (T + 1) → ℝ)
    (v : Fin (T + 1) → Bool → ℝ) : Fin (T + 1) :=
  ⟨thresholdStage r u v, Nat.lt_succ_of_le (thresholdStage_le r u v)⟩

theorem thresholdStageIndex_measurable {Q : Type*} [MeasurableSpace Q] {T : ℕ} (r : ℝ)
    (u : Q → Fin (T + 1) → ℝ) (v : Q → Fin (T + 1) → Bool → ℝ)
    (hu : ∀ i, Measurable (fun q => u q i)) (hv : ∀ i b, Measurable (fun q => v q i b)) :
    Measurable (fun q => thresholdStageIndex r (u q) (v q)) := by
  have hm : Measurable (fun n : ℕ => (⟨n % (T + 1), Nat.mod_lt n (Nat.succ_pos T)⟩ : Fin (T + 1))) :=
    measurable_of_countable _
  convert hm.comp (thresholdStage_measurable r u v hu hv) using 1
  funext q
  apply Fin.ext
  exact (Nat.mod_eq_of_lt (Nat.lt_succ_of_le (thresholdStage_le r (u q) (v q)))).symm

theorem measurable_selected_truncation {Q R : Type*} [MeasurableSpace Q] [MeasurableSpace R]
    {T : ℕ} (k : Q → Fin (T + 1)) (hk : Measurable k)
    (F : Fin (T + 1) → Q → R) (hF : ∀ i, Measurable (F i)) :
    Measurable (fun q => F (k q) q) := by
  have h : Measurable (fun z : Q × Fin (T + 1) => F z.2 z.1) :=
    measurable_from_prod_countable (fun i => hF i)
  exact h.comp (measurable_id.prodMk hk)

end FreshGradientMinimax
