import NCConcave16991.DenseWeakBankEntropy
import NCConcave16991.DenseWeakConditionalInformation

/-! # Actual conditional pushforwards of a finite static experiment -/

noncomputable section

open scoped BigOperators

namespace NCConcave16991.DenseWeakHiding.FiniteLaw

attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

variable {A H B : Type*} [Fintype A] [Fintype H] [Fintype B]

theorem map_pair_fst_mass (P : FiniteLaw A) (history : A → H) (reply : A → B) (h : H) :
    (P.map (fun a ↦ (history a,reply a))).fst.mass h = P.eventMass {a | history a = h} := by
  simp only [fst, rowMass, map, eventMass]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : history a = h <;> simp [Prod.mk.injEq, ha]

variable {I J : Type*} [Fintype I] [Fintype J]

/-- Conditioning the actual observed joint law equals pushing forward the
original static law restricted to the actual observation fibre. -/
theorem conditionalPair_map_mass (P : FiniteLaw A) (history : A → H)
    (pair : A → I × J) (h : H)
    (hh : 0 < (P.map (fun a ↦ (history a,pair a))).fst.mass h) (z : I × J) :
    ((P.map (fun a ↦ (history a,pair a))).conditionalPair h hh).mass z =
      ((P.condition {a | history a = h}
        (by simpa only [map_pair_fst_mass] using hh)).map pair).mass z := by
  have hden : rowMass (P.map (fun a ↦ (history a,pair a))).mass h =
      P.eventMass {a | history a = h} := map_pair_fst_mass P history pair h
  simp only [conditionalPair, conditionalMass]
  rw [hden]
  simp only [map, condition, Set.mem_setOf_eq]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : history a = h <;> by_cases hp : pair a = z <;>
    simp [Prod.mk.injEq, ha, hp]

end NCConcave16991.DenseWeakHiding.FiniteLaw
