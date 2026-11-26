import SecondOrder.BernoulliMixtureCalculus
import SecondOrder.Weights

open scoped BigOperators Classical

namespace SecondOrder
noncomputable section

/-- Zero means no successful gate; a gate at index i selects payload i+1. -/
def lastSuccess : {n : ℕ} → (Fin n → Bool) → ℕ
  | 0, _ => 0
  | n+1, w => if w (Fin.last n) then n+1 else lastSuccess (fun i => w i.castSucc)

theorem lastSuccess_le {n : ℕ} (w : Fin n → Bool) : lastSuccess w ≤ n := by
  induction n with
  | zero => simp [lastSuccess]
  | succ n ih =>
    simp only [lastSuccess]
    split_ifs
    · exact le_rfl
    · exact (ih _).trans (Nat.le_succ n)

theorem sum_bool_snoc {n : ℕ} (X : (Fin (n+1) → Bool) → ℝ) :
    ∑ w, X w = ∑ past : Fin n → Bool, ∑ z : Bool, X (Fin.snoc past z) := by
  let e : ((Fin n → Bool) × Bool) ≃ (Fin (n+1) → Bool) :=
    (Equiv.prodComm _ _).trans (Fin.snocEquiv (fun _ => Bool))
  rw [← Equiv.sum_comp e X, Fintype.sum_prod_type]
  rfl

theorem bernoulliDensity_sum {ι : Type*} [Fintype ι] (p : ι → ℝ) :
    ∑ w, bernoulliDensity p w = 1 := by
  unfold bernoulliDensity
  rw [← Fintype.prod_sum]
  simp [Fintype.sum_bool, binaryMass]

theorem bernoulliDensity_snoc (b : ℕ → ℝ) (n : ℕ) (past : Fin n → Bool) (z : Bool) :
    bernoulliDensity (fun i : Fin (n+1) => b i) (Fin.snoc past z) =
      bernoulliDensity (fun i : Fin n => b i) past * binaryMass (b n) z := by
  simp [bernoulliDensity, Fin.prod_univ_castSucc]

def lastSuccessAverage (b V : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ w : Fin n → Bool, bernoulliDensity (fun i : Fin n => b i) w * V (lastSuccess w)

theorem lastSuccessAverage_step (b V : ℕ → ℝ) (n : ℕ) :
    lastSuccessAverage b V (n+1) = (1-b n)*lastSuccessAverage b V n + b n*V (n+1) := by
  unfold lastSuccessAverage
  rw [sum_bool_snoc]
  simp only [Fintype.sum_bool, bernoulliDensity_snoc, lastSuccess, Fin.snoc_last,
    Fin.snoc_castSucc, Bool.false_eq_true, if_false, if_true, binaryMass]
  simp only [Finset.sum_add_distrib]
  have ha : (∑ w : Fin n → Bool, bernoulliDensity (fun i : Fin n => b i) w * b n * V (n+1)) = b n*V (n+1) := by
    rw [← Finset.sum_mul, ← Finset.sum_mul]
    have hs := bernoulliDensity_sum (fun i : Fin n => b i)
    convert congrArg (fun t : ℝ => t*b n*V (n+1)) hs using 1 <;> congr 2
    · apply Finset.sum_congr (by ext w; simp)
      intro w _
      rfl
    · simp only [one_mul]
  rw [ha]
  have hb : (∑ w : Fin n → Bool, bernoulliDensity (fun i : Fin n => b i) w * (1-b n) * V (lastSuccess w)) =
      (1-b n)*∑ w : Fin n → Bool, bernoulliDensity (fun i : Fin n => b i) w * V (lastSuccess w) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro w _
    ring
  rw [hb]
  ring

def reverseSelectorValue (b V : ℕ → ℝ) (n : ℕ) : ℝ :=
  tailProduct b n 0*V 0 + ∑ i ∈ Finset.range n, b i*tailProduct b n (i+1)*V (i+1)

theorem tailProduct_succ_top (b : ℕ → ℝ) {n p : ℕ} (hp : p ≤ n) :
    tailProduct b (n+1) p = tailProduct b n p*(1-b n) := by
  exact Finset.prod_Ico_succ_top hp _

theorem reverseSelectorValue_step (b V : ℕ → ℝ) (n : ℕ) :
    reverseSelectorValue b V (n+1) = (1-b n)*reverseSelectorValue b V n + b n*V (n+1) := by
  unfold reverseSelectorValue
  rw [Finset.sum_range_succ, tailProduct_succ_top b (Nat.zero_le n), tailProduct_self]
  have hs : (∑ i ∈ Finset.range n, b i*tailProduct b (n+1) (i+1)*V (i+1)) =
      (1-b n)*∑ i ∈ Finset.range n, b i*tailProduct b n (i+1)*V (i+1) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [tailProduct_succ_top b (by have := Finset.mem_range.mp hi; omega)]
    ring
  rw [hs]
  ring

/-- The manuscript's reverse weights are exactly the law of the last success.
This is a polynomial identity, so it includes gate values zero and one. -/
theorem lastSuccessAverage_eq_reverseSelector (b V : ℕ → ℝ) (n : ℕ) :
    lastSuccessAverage b V n = reverseSelectorValue b V n := by
  induction n with
  | zero => simp [lastSuccessAverage, reverseSelectorValue, lastSuccess, bernoulliDensity, tailProduct]
  | succ n ih => rw [lastSuccessAverage_step, reverseSelectorValue_step, ih]

end
end SecondOrder
