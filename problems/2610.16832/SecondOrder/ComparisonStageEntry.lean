import SecondOrder.ComparisonWeights

open scoped Classical ENNReal

namespace SecondOrder
noncomputable section
variable {m T : ℕ} {S : Type*}

/-- Entry to a positive stage is tested before sampling the first response
with that index. Stage zero starts at the deterministic initial history. -/
def curvatureStageEntry (P : CurvaturePolicy m T S) (Θ : Fin (T+1) → BalancedVector m)
    (A β : ℝ) {R : ℝ} (z : ℕ → CurvatureCoefficients m T R) (stage n : ℕ) : Prop :=
  (curvatureComparisonRun P Θ A β z n).1<stage ∧ curvatureComparisonIndex P Θ A β z n=stage

theorem curvatureStageEntry_progress (P : CurvaturePolicy m T S)
    (Θ : Fin (T+1) → BalancedVector m) (A β : ℝ) {R : ℝ}
    (z : ℕ → CurvatureCoefficients m T R) {stage n : ℕ}
    (he : curvatureStageEntry P Θ A β z stage n) :
    (curvatureComparisonRun P Θ A β z n).1+1=stage ∧
      (curvatureComparisonRun P Θ A β z (n+1)).1=stage := by
  have hi : curvatureComparisonIndex P Θ A β z n≤(curvatureComparisonRun P Θ A β z n).1+1 :=
    (curvatureLimitedProgress_le Θ β _ _).2
  have h1 := he.1
  have h2 := he.2
  constructor
  · omega
  · rw [curvatureComparisonRun_progress_succ, h2, max_eq_right (by omega)]

theorem curvatureStageEntry_no_previous (P : CurvaturePolicy m T S)
    (Θ : Fin (T+1) → BalancedVector m) (A β : ℝ) {R : ℝ}
    (z : ℕ → CurvatureCoefficients m T R) {stage n : ℕ}
    (he : curvatureStageEntry P Θ A β z stage n) :
    ∀ t, t<n → curvatureComparisonIndex P Θ A β z t<stage := by
  intro t ht
  have h1 := curvatureComparisonIndex_le_next P Θ A β z t
  have h2 : (curvatureComparisonRun P Θ A β z (t+1)).1≤(curvatureComparisonRun P Θ A β z n).1 :=
    curvatureComparisonRun_progress_mono P Θ A β z (by omega)
  exact lt_of_le_of_lt (h1.trans h2) he.1

theorem curvatureStageEntry_unique (P : CurvaturePolicy m T S)
    (Θ : Fin (T+1) → BalancedVector m) (A β : ℝ) {R : ℝ}
    (z : ℕ → CurvatureCoefficients m T R) {stage n k : ℕ}
    (hn : curvatureStageEntry P Θ A β z stage n) (hk : curvatureStageEntry P Θ A β z stage k) : n=k := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · have hh := curvatureStageEntry_no_previous P Θ A β z hk n h
    rw [hn.2] at hh
    exact Nat.lt_irrefl _ hh
  · have hh := curvatureStageEntry_no_previous P Θ A β z hn k h
    rw [hk.2] at hh
    exact Nat.lt_irrefl _ hh

/-- The entry event and pre-response state ignore the new hidden block.
This is proved by pointwise replacement of every unrevealed hidden vector. -/
theorem curvatureStageEntry_prefix (P : CurvaturePolicy m T S)
    (Θ Θ' : Fin (T+1) → BalancedVector m) (A β : ℝ) {R : ℝ}
    (z : ℕ → CurvatureCoefficients m T R) (stage n : ℕ)
    (hΘ : ∀ i, i.val<stage → Θ i=Θ' i)
    (he : curvatureStageEntry P Θ A β z stage n) :
    curvatureStageEntry P Θ' A β z stage n ∧
      curvatureComparisonRun P Θ A β z n=curvatureComparisonRun P Θ' A β z n := by
  have hp := (curvatureStageEntry_progress P Θ A β z he).1
  have hprefix : ∀ i, i.val<(curvatureComparisonRun P Θ A β z n).1+1 → Θ i=Θ' i :=
    fun i hi => hΘ i (by omega)
  have hs := curvatureComparisonRun_hidden_prefix P Θ A β z n Θ' hprefix
  have hi := curvatureComparisonIndex_hidden_prefix P Θ Θ' A β z n hprefix
  refine ⟨⟨?_,?_⟩,hs⟩
  · rw [←hs]
    exact he.1
  · rw [←hi]
    exact he.2

theorem curvatureStageEntry_iff_prefix (P : CurvaturePolicy m T S)
    (Θ Θ' : Fin (T+1) → BalancedVector m) (A β : ℝ) {R : ℝ}
    (z : ℕ → CurvatureCoefficients m T R) (stage n : ℕ)
    (hΘ : ∀ i, i.val<stage → Θ i=Θ' i) :
    curvatureStageEntry P Θ A β z stage n ↔ curvatureStageEntry P Θ' A β z stage n :=
  ⟨fun he => (curvatureStageEntry_prefix P Θ Θ' A β z stage n hΘ he).1,
    fun he => (curvatureStageEntry_prefix P Θ' Θ A β z stage n (fun i hi => (hΘ i hi).symm) he).1⟩

/-- Entry likelihoods as well as entry states depend only on earlier hidden
blocks. This is the density-level input for conditioning on an entry history. -/
theorem curvatureStageEntry_weight_prefix (P : CurvaturePolicy m T S)
    (Θ Θ' : Fin (T+1) → BalancedVector m) (A β R : ℝ) (hR : 2≤R)
    (z : ℕ → CurvatureCoefficients m T R) (stage n : ℕ)
    (hΘ : ∀ i, i.val<stage → Θ i=Θ' i) :
    (if curvatureStageEntry P Θ A β z stage n then curvatureComparisonWeight P Θ A β R hR z n else 0)=
    (if curvatureStageEntry P Θ' A β z stage n then curvatureComparisonWeight P Θ' A β R hR z n else 0) := by
  have he := curvatureStageEntry_iff_prefix P Θ Θ' A β z stage n hΘ
  by_cases h : curvatureStageEntry P Θ A β z stage n
  · rw [if_pos h, if_pos (he.mp h)]
    apply curvatureComparisonWeight_hidden_prefix P Θ A β R hR z n Θ'
    have hp := (curvatureStageEntry_progress P Θ A β z h).1
    intro i hi
    exact hΘ i (by omega)
  · rw [if_neg h, if_neg (fun h' => h (he.mpr h'))]

end
end SecondOrder
