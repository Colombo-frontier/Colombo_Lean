import Bilevel.ChiCanonicalFrontierAdvance

/-! An unreleased macro coordinate has an incomplete level-zero child in
the actual canonical success counter, including the zero-success state. -/
noncomputable section
namespace Bilevel.ChiHierarchyIndex
open ChiTreeProgress

theorem canonicalCounter_macro_future (counts : ℕ → ℕ) (J q : ℕ) (i : Fin (counts 0+1))
    (hi : counter counts (J+1) q 0 [] ≤ i.val) :
    canonicalCounter counts J q 0 [i.val]≤counts 1 := by
  rw [canonicalCounter_legal counts J q 0 [i.val] (Nat.zero_le J) (legal_macro counts i) rfl]
  exact counter_future counts (J+1) q 0 [] (Nat.zero_lt_succ J) i hi

end Bilevel.ChiHierarchyIndex
