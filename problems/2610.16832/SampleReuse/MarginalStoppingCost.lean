import SampleReuse.MarginalLazyStopping

open SecondOrder
open scoped Classical ENNReal BigOperators
namespace SampleReuse
noncomputable section
variable {Ξ H S : Type} {d : ℕ} {R : ℝ}

theorem marginalLazyGradientCount_mono
    (P : Ξ → OracleAlgorithm (MarginalQuery H d) (PersistentReply d) (Point d) S)
    (ε : ℝ) (v : Point d) (w : Ξ × (ℕ → SignedCoefficient R)) :
    Monotone (fun N => (marginalLazyObservation P ε v N w).1) := by
  intro n m hnm
  dsimp only [marginalLazyObservation]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hnm) (fun _ _ _ => Nat.zero_le _)

theorem marginalFreeze_lazy_query_before
    (P : OracleAlgorithm (MarginalQuery H d) (PersistentReply d) (Point d) S)
    (stop : ℕ → S → Bool) (idle : H) (ε : ℝ) (v : Point d)
    (tape : ℕ → SignedCoefficient R) (n : ℕ)
    (hs : ∀ k ≤ n, stop k (lazyPersistentRun (marginalAsPersistent P).toQueryPolicy (marginalLazyReply ε v) tape k).1 = false) :
    (marginalFreeze P stop idle).query n
      (lazyPersistentRun (marginalAsPersistent (marginalFreeze P stop idle)).toQueryPolicy
        (marginalLazyReply ε v) tape n).1 =
      P.query n (lazyPersistentRun (marginalAsPersistent P).toQueryPolicy (marginalLazyReply ε v) tape n).1 := by
  rw [marginalFreeze_asPersistent,
    freezeOracle_lazy_before (marginalAsPersistent P) stop ((false,0),idle) _ _ n (fun k hk => hs k hk.le)]
  change (if stop n _ = true then _ else _) = _
  rw [hs n le_rfl]
  rfl

theorem marginalFreeze_lazy_query_after
    (P : OracleAlgorithm (MarginalQuery H d) (PersistentReply d) (Point d) S)
    (stop : ℕ → S → Bool) (idle : H) (ε : ℝ) (v : Point d)
    (tape : ℕ → SignedCoefficient R) {k n : ℕ}
    (hk : marginalLazyFirstStop P stop ε v tape k) (hn : k ≤ n) :
    ((marginalFreeze P stop idle).query n
      (lazyPersistentRun (marginalAsPersistent (marginalFreeze P stop idle)).toQueryPolicy
        (marginalLazyReply ε v) tape n).1).1 = false := by
  rw [marginalFreeze_lazy_first_stop P stop idle ε v tape hk hn]
  rfl

theorem marginalFreeze_lazy_count_stopped
    (P : Ξ → OracleAlgorithm (MarginalQuery H d) (PersistentReply d) (Point d) S)
    (stop : Ξ → ℕ → S → Bool) (idle : H) (ε : ℝ) (v : Point d)
    (w : Ξ × (ℕ → SignedCoefficient R)) {k N : ℕ}
    (hk : marginalLazyFirstStop (P w.1) (stop w.1) ε v w.2 k) (hN : k ≤ N) :
    (marginalLazyObservation (fun ξ => marginalFreeze (P ξ) (stop ξ) idle) ε v N w).1 =
      (marginalLazyObservation P ε v k w).1 := by
  obtain ⟨r,rfl⟩ := Nat.exists_eq_add_of_le hN
  dsimp only [marginalLazyObservation]
  rw [Finset.sum_range_add]
  have hzero : (∑ j ∈ Finset.range r,
      if ((marginalFreeze (P w.1) (stop w.1) idle).query (k+j)
        (lazyPersistentRun (marginalAsPersistent (marginalFreeze (P w.1) (stop w.1) idle)).toQueryPolicy
          (marginalLazyReply ε v) w.2 (k+j)).1).1 then 1 else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    rw [marginalFreeze_lazy_query_after (P w.1) (stop w.1) idle ε v w.2 hk (by omega)]
    rfl
  rw [hzero,Nat.add_zero]
  apply Finset.sum_congr rfl
  intro j hj
  rw [marginalFreeze_lazy_query_before (P w.1) (stop w.1) idle ε v w.2 j
    (fun u hu => hk.2 u (by have := Finset.mem_range.mp hj; omega))]

/-- The extended gradient count is exactly the number of original gradient
requests before the actual first stop. Idling contributes no gradients. -/
theorem marginalLazyExtendedGradientCount_at_stop
    (P : Ξ → OracleAlgorithm (MarginalQuery H d) (PersistentReply d) (Point d) S)
    (stop : Ξ → ℕ → S → Bool) (idle : H) (ε : ℝ) (v : Point d)
    (w : Ξ × (ℕ → SignedCoefficient R)) {k : ℕ}
    (hk : marginalLazyFirstStop (P w.1) (stop w.1) ε v w.2 k) :
    marginalLazyExtendedGradientCount P stop idle ε v w = (marginalLazyObservation P ε v k w).1 := by
  apply le_antisymm
  · apply iSup_le
    intro N
    by_cases hN : k ≤ N
    · rw [marginalFreeze_lazy_count_stopped P stop idle ε v w hk hN]
    · have hm := marginalLazyGradientCount_mono (fun ξ => marginalFreeze (P ξ) (stop ξ) idle) ε v w
        (show N ≤ k by omega)
      dsimp only at hm
      rw [marginalFreeze_lazy_count_stopped P stop idle ε v w hk le_rfl] at hm
      exact_mod_cast hm
  · have hh := le_iSup (fun N : ℕ =>
      ((marginalLazyObservation (fun ξ => marginalFreeze (P ξ) (stop ξ) idle) ε v N w).1 : ℝ≥0∞)) k
    rwa [marginalFreeze_lazy_count_stopped P stop idle ε v w hk le_rfl] at hh

end
end SampleReuse
