import GradientHessian.ClockedOracleExpansion

/-! Exact pathwise cost of ordinary-query expansion: every original
ordinary instruction costs one call, every rich instruction costs r calls,
and the expanded policy never makes a rich query. -/

namespace GradientHessian.ClockedOracle
open MeasureTheory
open scoped BigOperators

variable {Seed W X Y Z : Type*} [MeasurableSpace Seed] [MeasurableSpace W]
  [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z] {r : ℕ}

theorem sum_range_blocks (f : ℕ → ℕ) (L B : ℕ) :
    (∑ k ∈ Finset.range (L*B),f k)=∑ i ∈ Finset.range L,∑ j ∈ Finset.range B,f (i*B+j) := by
  induction L with
  | zero => simp
  | succ L ih => rw [Nat.succ_mul,Finset.sum_range_add,ih,Finset.sum_range_succ]

theorem Program.expandedKind_clock (p : Program Seed W X Y Z) (r i j : ℕ) (hj : j<r+1) :
    p.expandedKind r (i*(r+1)+j)=
      if p.kind i=2 then if j<r then 1 else 0 else if j=0 then p.kind i else 0 := by
  simp only [expandedKind,batchIndex_clock r i j hj,batchSlot_clock r i j hj]

theorem Program.expanded_block_count (p : Program Seed W X Y Z) (r i : ℕ) :
    (∑ j ∈ Finset.range (r+1),if p.expandedKind r (i*(r+1)+j)=1 then 1 else 0)=
      (if p.kind i=1 then 1 else 0)+r*(if p.kind i=2 then 1 else 0) := by
  have he : (∑ j ∈ Finset.range (r+1),if p.expandedKind r (i*(r+1)+j)=1 then 1 else 0)=
      ∑ j ∈ Finset.range (r+1),
        if (if p.kind i=2 then if j<r then (1:Fin 3) else 0 else if j=0 then p.kind i else 0)=1 then 1 else 0 := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [p.expandedKind_clock r i j (Finset.mem_range.mp hj)]
  rw [he]
  by_cases hk : p.kind i=2
  · rw [hk]
    simp only [ite_true,show (2:Fin 3)≠1 from by decide,ite_false,mul_one,zero_add]
    have hj (j : ℕ) : (if (if j<r then (1:Fin 3) else 0)=1 then (1:ℕ) else 0)=if j<r then 1 else 0 := by
      by_cases hh : j<r <;> simp [hh]
    simp_rw [hj]
    rw [Finset.sum_range_succ]
    have hsum : (∑ j ∈ Finset.range r,if j<r then (1:ℕ) else 0)=r := by
      calc
        _ = ∑ j ∈ Finset.range r,(1:ℕ) := by
          apply Finset.sum_congr rfl
          intro j hj
          simp [Finset.mem_range.mp hj]
        _ = r := by simp
    rw [hsum]
    simp
  · simp only [hk,if_false,mul_zero,add_zero]
    have hj (j : ℕ) :
        (if (if j=0 then p.kind i else 0)=1 then (1:ℕ) else 0)=
          if j=0 then (if p.kind i=1 then 1 else 0) else 0 := by
      by_cases hh : j=0 <;> simp [hh]
    simp_rw [hj]
    simp [Finset.sum_ite_eq']

theorem Program.expand_ordinary_count (p : Program Seed W X Y Z) (b : Batch X Y Z r) :
    (p.expand b).count 1=p.count 1+r*p.count 2 := by
  change (∑ k ∈ Finset.range (p.length*(r+1)),if p.expandedKind r k=1 then 1 else 0)=_
  rw [sum_range_blocks]
  simp_rw [p.expanded_block_count]
  simp only [count,Finset.sum_add_distrib,Finset.mul_sum]

theorem Program.expanded_caps (p : Program Seed W X Y Z) (b : Batch X Y Z r)
    (ordinary : X → Y) (rich : X → Z) :
    (p.expand b).policy.HasCaps ordinary rich (p.count 1+r*p.count 2) 0 := by
  have h := (p.expand b).hasCaps ordinary rich
  rwa [p.expand_ordinary_count b,p.expand_rich_count b] at h

end GradientHessian.ClockedOracle
