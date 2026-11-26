import MinimaxAudit.SourcePotential
import MinimaxAudit.Chain

/-! Exact ideal-chain gap algebra. Geometric comparison points are supplied
explicitly; a later source instance theorem must prove their feasibility. -/
namespace MinimaxAudit

noncomputable def sourceWeight (q : ℝ) (n : ℕ) (i : Fin (n+1)) : ℝ := q ^ (n - i.1)

@[simp] theorem sourceWeight_last (q : ℝ) (n : ℕ) : sourceWeight q n (Fin.last n) = 1 := by
  simp [sourceWeight]
@[simp] theorem sourceWeight_zero (q : ℝ) (n : ℕ) : sourceWeight q n 0 = q ^ n := by
  simp [sourceWeight]

theorem sourceWeight_step (q : ℝ) (n : ℕ) (i : Fin n) :
    sourceWeight q n i.castSucc = q * sourceWeight q n i.succ := by
  unfold sourceWeight
  simp only [Fin.val_castSucc, Fin.val_succ]
  have he : n - i.1 = (n - (i.1 + 1)) + 1 := by omega
  rw [he, pow_succ]
  ring

theorem sourceWeight_energy (q : ℝ) (n : ℕ) :
    (∑ i : Fin (n+1), (sourceWeight q n i) ^ 2) -
      q * (∑ i : Fin n, sourceWeight q n i.castSucc * sourceWeight q n i.succ) = 1 := by
  rw [Fin.sum_univ_castSucc]
  rw [Finset.mul_sum]
  have hsum : (∑ i : Fin n, q * (sourceWeight q n i.castSucc * sourceWeight q n i.succ)) =
      ∑ i : Fin n, (sourceWeight q n i.castSucc) ^ 2 := by
    apply Finset.sum_congr rfl
    intro i _
    rw [sourceWeight_step q n i]
    ring
  rw [hsum, sourceWeight_last]
  ring

theorem sourceWeight_linear_telescope (q : ℝ) (n : ℕ) (a : Fin (n+1) → ℝ) :
    (∑ i : Fin (n+1), sourceWeight q n i * a i) -
      q * (∑ i : Fin n, sourceWeight q n i.succ * a i.castSucc) = a (Fin.last n) := by
  rw [Fin.sum_univ_castSucc, Finset.mul_sum]
  have hsum : (∑ i : Fin n, q * (sourceWeight q n i.succ * a i.castSucc)) =
      ∑ i : Fin n, sourceWeight q n i.castSucc * a i.castSucc := by
    apply Finset.sum_congr rfl
    intro i _
    rw [sourceWeight_step q n i]
    ring
  rw [hsum, sourceWeight_last]
  ring

noncomputable def idealScalarValue {n : ℕ} (q c base : ℝ) (a b : Fin (n+1) → ℝ) : ℝ :=
  base - c * b 0 - q * (∑ i : Fin n, a i.castSucc * b i.succ) -
    q / 2 * (a (Fin.last n)) ^ 2

/-- This is the exact finite-sum expansion behind the ideal witness. The
base-difference hypothesis is separated so its geometric instantiation cannot
be silently assumed. -/
theorem idealScalarValue_witness_difference (q c s baseDual basePrimal : ℝ)
    (n : ℕ) (a b : Fin (n+1) → ℝ)
    (hbase : baseDual - basePrimal =
      -s * (∑ i : Fin (n+1), sourceWeight q n i * a i) -
      s ^ 2 / 2 * (∑ i : Fin (n+1), (sourceWeight q n i) ^ 2)) :
    idealScalarValue q c baseDual
        (fun i => a i + s * sourceWeight q n i / 2)
        (fun i => b i - s * sourceWeight q n i / 2) -
      idealScalarValue q c basePrimal
        (fun i => a i + s * sourceWeight q n i / 2)
        (fun i => b i + s * sourceWeight q n i / 2) =
      s * (q ^ n * c - a (Fin.last n)) - s ^ 2 / 2 := by
  have hmodule (i : Fin n) :
      (a i.castSucc + s * sourceWeight q n i.castSucc / 2) *
        (b i.succ - s * sourceWeight q n i.succ / 2) -
      (a i.castSucc + s * sourceWeight q n i.castSucc / 2) *
        (b i.succ + s * sourceWeight q n i.succ / 2) =
      -s * (sourceWeight q n i.succ * a i.castSucc) -
        s ^ 2 / 2 * (sourceWeight q n i.castSucc * sourceWeight q n i.succ) := by ring
  have hsum :
      (∑ i : Fin n, (a i.castSucc + s * sourceWeight q n i.castSucc / 2) *
        (b i.succ - s * sourceWeight q n i.succ / 2)) -
      (∑ i : Fin n, (a i.castSucc + s * sourceWeight q n i.castSucc / 2) *
        (b i.succ + s * sourceWeight q n i.succ / 2)) =
      -s * (∑ i : Fin n, sourceWeight q n i.succ * a i.castSucc) -
        s ^ 2 / 2 * (∑ i : Fin n, sourceWeight q n i.castSucc * sourceWeight q n i.succ) := by
    rw [← Finset.sum_sub_distrib]
    simp_rw [hmodule]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have hl := sourceWeight_linear_telescope q n a
  have he := sourceWeight_energy q n
  unfold idealScalarValue
  dsimp only
  rw [sourceWeight_zero]
  linear_combination hbase - q * hsum - s * hl - s ^ 2 / 2 * he

end MinimaxAudit
