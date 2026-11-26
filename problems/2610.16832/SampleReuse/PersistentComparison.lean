import SampleReuse.PersistentFrontier
import SecondOrder.FirstOrderComparison

/-! Pathwise comparison for immutable reusable sample tables. Handle choice
is adaptive, and the same table is used on every revisit. -/

open SecondOrder
open scoped Classical
namespace SampleReuse
noncomputable section
variable {d T : ℕ} {Handle S : Type*}

abbrev PersistentFirstOrderPolicy (d T : ℕ) (Handle S : Type*) :=
  QueryPolicy (Point (FirstOrderDimension d T) × Handle) (RichReply (FirstOrderDimension d T)) S

def persistentRichRun (P : PersistentFirstOrderPolicy d T Handle S)
    (Θ : Fin (T + 1) → Fin d → Bool) (A β : ℝ) {R : ℝ}
    (table : Handle → FirstOrderCoefficients d T R) : ℕ → S
  | 0 => P.initial
  | n + 1 => let s := persistentRichRun P Θ A β table n
    let q := P.query n s
    P.update n s (richReply (scaledFirstOrderSample Θ A β) (table q.2) q.1)

def persistentComparisonStep (P : PersistentFirstOrderPolicy d T Handle S)
    (Θ : Fin (T + 1) → Fin d → Bool) (A β : ℝ) {R : ℝ}
    (table : Handle → FirstOrderCoefficients d T R) (n : ℕ) (s : ℕ × S) : ℕ × S :=
  let q := P.query n s.2
  let k := firstOrderLimitedProgress Θ β q.1 (s.1 + 1)
  (max s.1 k, P.update n s.2 (scaledFirstOrderTruncatedReply Θ A β (table q.2) k q.1))

def persistentComparisonRun (P : PersistentFirstOrderPolicy d T Handle S)
    (Θ : Fin (T + 1) → Fin d → Bool) (A β : ℝ) {R : ℝ}
    (table : Handle → FirstOrderCoefficients d T R) : ℕ → ℕ × S
  | 0 => (0, P.initial)
  | n + 1 => persistentComparisonStep P Θ A β table n (persistentComparisonRun P Θ A β table n)

def persistentComparisonQuery (P : PersistentFirstOrderPolicy d T Handle S)
    (Θ : Fin (T + 1) → Fin d → Bool) (A β : ℝ) {R : ℝ}
    (table : Handle → FirstOrderCoefficients d T R) (n : ℕ) :=
  P.query n (persistentComparisonRun P Θ A β table n).2

def persistentComparisonIndex (P : PersistentFirstOrderPolicy d T Handle S)
    (Θ : Fin (T + 1) → Fin d → Bool) (A β : ℝ) {R : ℝ}
    (table : Handle → FirstOrderCoefficients d T R) (n : ℕ) :=
  firstOrderLimitedProgress Θ β (persistentComparisonQuery P Θ A β table n).1
    ((persistentComparisonRun P Θ A β table n).1 + 1)

theorem persistentComparison_progress_succ (P : PersistentFirstOrderPolicy d T Handle S)
    (Θ : Fin (T + 1) → Fin d → Bool) (A β : ℝ) {R : ℝ}
    (table : Handle → FirstOrderCoefficients d T R) (n : ℕ) :
    (persistentComparisonRun P Θ A β table (n + 1)).1 =
      max (persistentComparisonRun P Θ A β table n).1 (persistentComparisonIndex P Θ A β table n) := rfl

theorem persistentComparison_progress_mono (P : PersistentFirstOrderPolicy d T Handle S)
    (Θ : Fin (T + 1) → Fin d → Bool) (A β : ℝ) {R : ℝ}
    (table : Handle → FirstOrderCoefficients d T R) :
    Monotone (fun n => (persistentComparisonRun P Θ A β table n).1) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [persistentComparison_progress_succ]
  exact le_max_left _ _

theorem persistentComparison_index_le_next (P : PersistentFirstOrderPolicy d T Handle S)
    (Θ : Fin (T + 1) → Fin d → Bool) (A β : ℝ) {R : ℝ}
    (table : Handle → FirstOrderCoefficients d T R) (n : ℕ) :
    persistentComparisonIndex P Θ A β table n ≤ (persistentComparisonRun P Θ A β table (n + 1)).1 := by
  rw [persistentComparison_progress_succ]
  exact le_max_right _ _

theorem persistentComparison_progress_step (P : PersistentFirstOrderPolicy d T Handle S)
    (Θ : Fin (T + 1) → Fin d → Bool) (A β : ℝ) {R : ℝ}
    (table : Handle → FirstOrderCoefficients d T R) (n : ℕ) :
    (persistentComparisonRun P Θ A β table (n + 1)).1 ≤
      (persistentComparisonRun P Θ A β table n).1 + 1 := by
  rw [persistentComparison_progress_succ]
  exact max_le (Nat.le_succ _) (firstOrderLimitedProgress_le Θ β _ _).2

def persistentNoFarJump (P : PersistentFirstOrderPolicy d T Handle S)
    (Θ : Fin (T + 1) → Fin d → Bool) (A β : ℝ) {R : ℝ}
    (table : Handle → FirstOrderCoefficients d T R) (N : ℕ) : Prop :=
  ∀ n, n < N → ∀ i, (persistentComparisonRun P Θ A β table n).1 + 1 ≤ i.val →
    ¬0 < firstOrderBlockCompletion (Θ i)
      (firstOrderDilation d T β (persistentComparisonQuery P Θ A β table n).1 i)

/-- Actual full scalar jets and comparison replies coincide on every safe
path, with exactly the same persistent table and adaptive handle choices. -/
theorem persistentComparison_coupling (P : PersistentFirstOrderPolicy d T Handle S)
    (Θ : Fin (T + 1) → Fin d → Bool) (A β : ℝ) {R : ℝ}
    (table : Handle → FirstOrderCoefficients d T R) :
    ∀ N, persistentNoFarJump P Θ A β table N →
      persistentRichRun P Θ A β table N = (persistentComparisonRun P Θ A β table N).2 := by
  intro N
  induction N with
  | zero => intro _; rfl
  | succ N ih =>
    intro hsafe
    have hs : persistentNoFarJump P Θ A β table N := fun n hn => hsafe n (by omega)
    have he := ih hs
    simp only [persistentRichRun, he]
    change P.update N (persistentComparisonRun P Θ A β table N).2
      (richReply (scaledFirstOrderSample Θ A β)
        (table (persistentComparisonQuery P Θ A β table N).2)
        (persistentComparisonQuery P Θ A β table N).1) =
      P.update N (persistentComparisonRun P Θ A β table N).2
        (scaledFirstOrderTruncatedReply Θ A β (table (persistentComparisonQuery P Θ A β table N).2)
          (persistentComparisonIndex P Θ A β table N) (persistentComparisonQuery P Θ A β table N).1)
    rw [firstOrderLimitedProgress_reply Θ A β _ _ _ (hsafe N (by omega))]
    rfl

theorem persistentTruncatedReply_prefix
    (Θ Θ' : Fin (T + 1) → Fin d → Bool) (A β : ℝ) {R : ℝ}
    (z z' : FirstOrderCoefficients d T R) (k : ℕ)
    (hΘ : ∀ i, i.val < k → Θ i = Θ' i) (hz : ∀ i, i.val ≤ k → z i = z' i)
    (x : Point (FirstOrderDimension d T)) :
    scaledFirstOrderTruncatedReply Θ A β z k x = scaledFirstOrderTruncatedReply Θ' A β z' k x := by
  by_cases hk : k ≤ T
  · exact scaledFirstOrderTruncatedReply_prefix_invariant Θ Θ' A β z z' hk hΘ hz x
  · have he : Θ = Θ' := funext (fun i => hΘ i (by omega))
    have hez : z = z' := funext (fun i => hz i (by omega))
    rw [he, hez]

/-- Before a block is reached, replacing every hidden vector and every
coefficient of every handle in the later blocks leaves the whole state
unchanged. This proves prefix dependence for the immutable table model. -/
theorem persistentComparison_prefix (P : PersistentFirstOrderPolicy d T Handle S)
    (Θ : Fin (T + 1) → Fin d → Bool) (A β : ℝ) {R : ℝ}
    (table : Handle → FirstOrderCoefficients d T R) :
    ∀ n (Θ' : Fin (T + 1) → Fin d → Bool) (table' : Handle → FirstOrderCoefficients d T R),
      (∀ i, i.val < (persistentComparisonRun P Θ A β table n).1 + 1 → Θ i = Θ' i) →
      (∀ r i, i.val < (persistentComparisonRun P Θ A β table n).1 + 1 → table r i = table' r i) →
      persistentComparisonRun P Θ A β table n = persistentComparisonRun P Θ' A β table' n := by
  intro n
  induction n with
  | zero => intro _ _ _ _; rfl
  | succ n ih =>
    intro Θ' table' hΘ hz
    have hmono : (persistentComparisonRun P Θ A β table n).1 ≤
        (persistentComparisonRun P Θ A β table (n + 1)).1 :=
      persistentComparison_progress_mono P Θ A β table (Nat.le_succ n)
    have hp : ∀ i, i.val < (persistentComparisonRun P Θ A β table n).1 + 1 → Θ i = Θ' i :=
      fun i hi => hΘ i (by omega)
    have hs := ih Θ' table' hp (fun r i hi => hz r i (by omega))
    have hk := firstOrderLimitedProgress_prefix Θ Θ' β (persistentComparisonQuery P Θ A β table n).1
      ((persistentComparisonRun P Θ A β table n).1 + 1) hp
    have hreply := persistentTruncatedReply_prefix Θ Θ' A β
      (table (persistentComparisonQuery P Θ A β table n).2)
      (table' (persistentComparisonQuery P Θ A β table n).2)
      (persistentComparisonIndex P Θ A β table n)
      (fun i hi => hΘ i (by have hh := persistentComparison_index_le_next P Θ A β table n; omega))
      (fun i hi => hz _ i (by have hh := persistentComparison_index_le_next P Θ A β table n; omega))
      (persistentComparisonQuery P Θ A β table n).1
    change persistentComparisonStep P Θ A β table n (persistentComparisonRun P Θ A β table n) =
      persistentComparisonStep P Θ' A β table' n (persistentComparisonRun P Θ' A β table' n)
    rw [← hs]
    apply Prod.ext
    · exact congrArg (max (persistentComparisonRun P Θ A β table n).1) hk
    · change P.update n (persistentComparisonRun P Θ A β table n).2
        (scaledFirstOrderTruncatedReply Θ A β (table (persistentComparisonQuery P Θ A β table n).2)
          (persistentComparisonIndex P Θ A β table n) (persistentComparisonQuery P Θ A β table n).1) =
        P.update n (persistentComparisonRun P Θ A β table n).2
          (scaledFirstOrderTruncatedReply Θ' A β (table' (persistentComparisonQuery P Θ A β table n).2)
            (firstOrderLimitedProgress Θ' β (persistentComparisonQuery P Θ A β table n).1
              ((persistentComparisonRun P Θ A β table n).1 + 1))
            (persistentComparisonQuery P Θ A β table n).1)
      rw [← hk]
      exact congrArg (P.update n (persistentComparisonRun P Θ A β table n).2) hreply

end
end SampleReuse
