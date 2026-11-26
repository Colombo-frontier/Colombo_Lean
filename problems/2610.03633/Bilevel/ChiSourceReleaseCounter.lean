import Bilevel.ChiHierarchyReleaseCounter
import Bilevel.ChiRecursiveSourceGeometry

/-! Canonical release policy for the actual source geometry. Its branching
counts are computed from the same sourceChainIndex used by the encoded
frames, including the independent macro width/length. -/
noncomputable section
namespace Bilevel.ChiTreeProgress
open ChiCarrier ChiRecursive ChiBoundedChain

def sourceCounts (macroN : ℕ) (cn : ℝ) (ratios resolutions : ℕ → ℝ) : ℕ → ℕ
  | 0 => macroN
  | j+1 => sourceChainIndex cn (ratios j) (resolutions j)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable (initial : Scale) (ratios resolutions weight : ℕ → ℝ) (A Kminus ζ cn CR : ℝ)
  (U : ∀ j,List ℕ → Space (sourceChainIndex cn (ratios j) (resolutions j)) →ₗᵢ[ℝ] E)
  (macroN J q : ℕ)

theorem source_release_future (t : ℕ) (ht : t<J) (P : List ℕ)
    (i : Fin (sourceChainIndex cn (ratios t) (resolutions t)+1))
    (hi : innerCounter (sourceCounts macroN cn ratios resolutions) J q t P ≤ i.val) :
    innerCounter (sourceCounts macroN cn ratios resolutions) J q (t+1) (child P i.val)≤
      (sourceGeometry initial ratios resolutions weight A Kminus ζ cn CR U (t+1) (child P i.val)).n :=
  inner_future (sourceGeometry initial ratios resolutions weight A Kminus ζ cn CR U)
    (sourceCounts macroN cn ratios resolutions) (fun _ _ => rfl) J q t ht P i hi

theorem source_release_frontier (macroIndex : ℕ) (V : Submodule ℝ E) :
    let D := sourceGeometry initial ratios resolutions weight A Kminus ζ cn CR U
    let r := innerCounter (sourceCounts macroN cn ratios resolutions) J q
    FrontierKnown D r (enlargedSpace V (nextRelease D r J 0 [macroIndex])) J 0 [macroIndex] :=
  inner_single_release _ _ (fun _ _ => rfl) J q macroIndex V

theorem source_release_is_column (macroIndex : ℕ)
    (hq : nodeBudget (sourceCounts macroN cn ratios resolutions) (J+1) 0 q [macroIndex]<
      capacity (fun k => sourceChainIndex cn (ratios k) (resolutions k)) J 0) :
    let D := sourceGeometry initial ratios resolutions weight A Kminus ζ cn CR U
    let r := innerCounter (sourceCounts macroN cn ratios resolutions) J q
    ∃ level P,∃ k : Fin ((D level P).n+1),level=J ∧ P.length=J+1 ∧
      k.val=r level P ∧ nextRelease D r J 0 [macroIndex]=(D level P).frame (basis k) := by
  dsimp only
  have hb := inner_budgetTree (sourceGeometry initial ratios resolutions weight A Kminus ζ cn CR U)
    (sourceCounts macroN cn ratios resolutions) (fun _ _ => rfl) J q J 0 [macroIndex] rfl (by omega)
  simpa only [Nat.zero_add,List.length_singleton,Nat.add_comm] using hb.nextRelease_column hq

end Bilevel.ChiTreeProgress
