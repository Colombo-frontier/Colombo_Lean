import Bilevel.ChiFrontierAdvance
import Bilevel.ChiSourceReleaseCounter

/-! A current Bernoulli success supplies the active evaluator's exact
retained-prefix advance along every reachable macro/inner path. -/
noncomputable section
namespace Bilevel.ChiTreeProgress
open ChiCarrier ChiRecursive
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem inner_frontierAdvance (D : Geometry E) (n : ℕ → ℕ)
    (hsize : ∀ j I,(D j I).n=n (j+1)) (J q : ℕ) (i : Fin (n 0+1))
    (hi : i.val ≤ counter n (J+1) q 0 []) :
    FrontierAdvance D (innerCounter n J q) (innerCounter n J (q+1)) J 0 [i.val] := by
  have ho := inner_budgetTree D n hsize J q J 0 [i.val] rfl (by omega)
  have hn := inner_budgetTree D n hsize J (q+1) J 0 [i.val] rfl (by omega)
  have hb (s : ℕ) : nodeBudget n (J+1) 0 s [i.val] = childBudget (capacity n J 1) i.val s := by
    simp only [nodeBudget,Nat.add_sub_cancel,Nat.zero_add]
  have hp : counter n (J+1) q 0 [] = parentPrefix (n 0+1) (capacity n J 1) q := by
    simp only [counter,List.length_nil,if_true,Nat.sub_zero,nodeBudget,nodePrefix]
  rw [hp] at hi
  rcases lt_or_eq_of_le hi with hi|hi
  · apply completed_frontierAdvance
    apply ho.completed
    rw [hb,earlier_child_complete _ _ _ _ (capacity_pos n J 1) hi]
    exact (capacity_shift n J 0 1).le
  · have he : i.val = q / capacity n J 1 := by
      have hit := i.isLt
      change i.val = min (n 0+1) (q / capacity n J 1) at hi
      omega
    rw [hb (q+1),childBudget_success _ _ _ (capacity_pos n J 1),if_pos he,← hb q] at hn
    exact ho.frontierAdvance hn

theorem source_frontierAdvance (initial : Scale) (ratios resolutions weight : ℕ → ℝ)
    (A Kminus ζ cn CR : ℝ)
    (U : ∀ j,List ℕ → ChiBoundedChain.Space (ChiBoundedChain.sourceChainIndex cn (ratios j) (resolutions j)) →ₗᵢ[ℝ] E)
    (macroN J q : ℕ) (i : Fin (macroN+1))
    (hi : i.val ≤ counter (sourceCounts macroN cn ratios resolutions) (J+1) q 0 []) :
    let D := sourceGeometry initial ratios resolutions weight A Kminus ζ cn CR U
    FrontierAdvance D (innerCounter (sourceCounts macroN cn ratios resolutions) J q)
      (innerCounter (sourceCounts macroN cn ratios resolutions) J (q+1)) J 0 [i.val] := by
  dsimp only
  exact inner_frontierAdvance (sourceGeometry initial ratios resolutions weight A Kminus ζ cn CR U)
    (sourceCounts macroN cn ratios resolutions) (fun _ _ => rfl) J q i hi

end Bilevel.ChiTreeProgress
