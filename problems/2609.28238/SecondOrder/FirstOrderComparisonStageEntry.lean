import SecondOrder.FirstOrderComparisonWeights

open scoped Classical ENNReal

namespace SecondOrder
noncomputable section
variable {d T : ℕ} {S : Type*}

/-- Entry to a positive stage is tested before sampling the first response
with that index. Stage zero starts at the deterministic initial history. -/
def firstOrderStageEntry (P : FirstOrderPolicy d T S) (Θ : Fin (T+1) → (Fin d → Bool))
    (A β : ℝ) {R : ℝ} (z : ℕ → FirstOrderCoefficients d T R) (stage n : ℕ) : Prop :=
  (firstOrderComparisonRun P Θ A β z n).1<stage ∧ firstOrderComparisonIndex P Θ A β z n=stage

theorem firstOrderStageEntry_progress (P : FirstOrderPolicy d T S)
    (Θ : Fin (T+1) → (Fin d → Bool)) (A β : ℝ) {R : ℝ}
    (z : ℕ → FirstOrderCoefficients d T R) {stage n : ℕ}
    (he : firstOrderStageEntry P Θ A β z stage n) :
    (firstOrderComparisonRun P Θ A β z n).1+1=stage ∧
      (firstOrderComparisonRun P Θ A β z (n+1)).1=stage := by
  have hi : firstOrderComparisonIndex P Θ A β z n≤(firstOrderComparisonRun P Θ A β z n).1+1 :=
    (firstOrderLimitedProgress_le Θ β _ _).2
  have h1 := he.1
  have h2 := he.2
  constructor
  · omega
  · rw [firstOrderComparisonRun_progress_succ, h2, max_eq_right (by omega)]

theorem firstOrderStageEntry_no_previous (P : FirstOrderPolicy d T S)
    (Θ : Fin (T+1) → (Fin d → Bool)) (A β : ℝ) {R : ℝ}
    (z : ℕ → FirstOrderCoefficients d T R) {stage n : ℕ}
    (he : firstOrderStageEntry P Θ A β z stage n) :
    ∀ t, t<n → firstOrderComparisonIndex P Θ A β z t<stage := by
  intro t ht
  have h1 := firstOrderComparisonIndex_le_next P Θ A β z t
  have h2 : (firstOrderComparisonRun P Θ A β z (t+1)).1≤(firstOrderComparisonRun P Θ A β z n).1 :=
    firstOrderComparisonRun_progress_mono P Θ A β z (by omega)
  exact lt_of_le_of_lt (h1.trans h2) he.1

theorem firstOrderStageEntry_unique (P : FirstOrderPolicy d T S)
    (Θ : Fin (T+1) → (Fin d → Bool)) (A β : ℝ) {R : ℝ}
    (z : ℕ → FirstOrderCoefficients d T R) {stage n k : ℕ}
    (hn : firstOrderStageEntry P Θ A β z stage n) (hk : firstOrderStageEntry P Θ A β z stage k) : n=k := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · have hh := firstOrderStageEntry_no_previous P Θ A β z hk n h
    rw [hn.2] at hh
    exact Nat.lt_irrefl _ hh
  · have hh := firstOrderStageEntry_no_previous P Θ A β z hn k h
    rw [hk.2] at hh
    exact Nat.lt_irrefl _ hh

/-- The entry event and pre-response state ignore the new hidden block.
This is proved by pointwise replacement of every unrevealed hidden vector. -/
theorem firstOrderStageEntry_prefix (P : FirstOrderPolicy d T S)
    (Θ Θ' : Fin (T+1) → (Fin d → Bool)) (A β : ℝ) {R : ℝ}
    (z : ℕ → FirstOrderCoefficients d T R) (stage n : ℕ)
    (hΘ : ∀ i, i.val<stage → Θ i=Θ' i)
    (he : firstOrderStageEntry P Θ A β z stage n) :
    firstOrderStageEntry P Θ' A β z stage n ∧
      firstOrderComparisonRun P Θ A β z n=firstOrderComparisonRun P Θ' A β z n := by
  have hp := (firstOrderStageEntry_progress P Θ A β z he).1
  have hprefix : ∀ i, i.val<(firstOrderComparisonRun P Θ A β z n).1+1 → Θ i=Θ' i :=
    fun i hi => hΘ i (by omega)
  have hs := firstOrderComparisonRun_hidden_prefix P Θ A β z n Θ' hprefix
  have hi := firstOrderComparisonIndex_hidden_prefix P Θ Θ' A β z n hprefix
  refine ⟨⟨?_,?_⟩,hs⟩
  · rw [←hs]
    exact he.1
  · rw [←hi]
    exact he.2

theorem firstOrderStageEntry_iff_prefix (P : FirstOrderPolicy d T S)
    (Θ Θ' : Fin (T+1) → (Fin d → Bool)) (A β : ℝ) {R : ℝ}
    (z : ℕ → FirstOrderCoefficients d T R) (stage n : ℕ)
    (hΘ : ∀ i, i.val<stage → Θ i=Θ' i) :
    firstOrderStageEntry P Θ A β z stage n ↔ firstOrderStageEntry P Θ' A β z stage n :=
  ⟨fun he => (firstOrderStageEntry_prefix P Θ Θ' A β z stage n hΘ he).1,
    fun he => (firstOrderStageEntry_prefix P Θ' Θ A β z stage n (fun i hi => (hΘ i hi).symm) he).1⟩

/-- Entry likelihoods as well as entry states depend only on earlier hidden
blocks. This is the density-level input for conditioning on an entry history. -/
theorem firstOrderStageEntry_weight_prefix (P : FirstOrderPolicy d T S)
    (Θ Θ' : Fin (T+1) → (Fin d → Bool)) (A β R : ℝ) (hR : 2≤R)
    (z : ℕ → FirstOrderCoefficients d T R) (stage n : ℕ)
    (hΘ : ∀ i, i.val<stage → Θ i=Θ' i) :
    (if firstOrderStageEntry P Θ A β z stage n then firstOrderComparisonWeight P Θ A β R hR z n else 0)=
    (if firstOrderStageEntry P Θ' A β z stage n then firstOrderComparisonWeight P Θ' A β R hR z n else 0) := by
  have he := firstOrderStageEntry_iff_prefix P Θ Θ' A β z stage n hΘ
  by_cases h : firstOrderStageEntry P Θ A β z stage n
  · rw [if_pos h, if_pos (he.mp h)]
    apply firstOrderComparisonWeight_hidden_prefix P Θ A β R hR z n Θ'
    have hp := (firstOrderStageEntry_progress P Θ A β z h).1
    intro i hi
    exact hΘ i (by omega)
  · rw [if_neg h, if_neg (fun h' => h (he.mpr h'))]

end
end SecondOrder

