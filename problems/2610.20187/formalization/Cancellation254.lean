import Audit254

noncomputable section

/-! The recursion-tree counting step, proved from an explicit finite tree.
Good nodes have only a left child; bad nodes may have both children.
Connecting the paper's actual interval algorithm to this tree and obtaining
the logarithmic chain bound remain separate obligations. -/
namespace Paper254

inductive RestartTree where
  | empty
  | good (left : RestartTree)
  | bad (left right : RestartTree)
deriving Repr

namespace RestartTree

def goodCount : RestartTree → ℕ
  | .empty => 0
  | .good l => l.goodCount + 1
  | .bad l r => l.goodCount + r.goodCount

def badCount : RestartTree → ℕ
  | .empty => 0
  | .good l => l.badCount
  | .bad l r => l.badCount + r.badCount + 1

def initialGoodRun : RestartTree → ℕ
  | .empty => 0
  | .good l => l.initialGoodRun + 1
  | .bad _ _ => 0

def ChainsBounded (L : ℕ) : RestartTree → Prop
  | .empty => True
  | .good l => l.initialGoodRun + 1 ≤ L ∧ l.ChainsBounded L
  | .bad l r => l.ChainsBounded L ∧ r.ChainsBounded L

theorem initialGoodRun_le {L : ℕ} {t : RestartTree} (h : t.ChainsBounded L) :
    t.initialGoodRun ≤ L := by
  cases t with
  | empty => exact Nat.zero_le _
  | good l => exact h.1
  | bad l r => exact Nat.zero_le _

theorem count_aux (t : RestartTree) (L : ℕ) (h : t.ChainsBounded L) :
    t.goodCount ≤ L * (2 * t.badCount) + t.initialGoodRun := by
  induction t with
  | empty => simp [goodCount, badCount, initialGoodRun]
  | good l ih =>
    have hl := ih h.2
    simp only [goodCount, badCount, initialGoodRun]
    omega
  | bad l r ihl ihr =>
    have hl := ihl h.1
    have hr := ihr h.2
    have hdl := initialGoodRun_le h.1
    have hdr := initialGoodRun_le h.2
    simp only [goodCount, badCount, initialGoodRun]
    nlinarith

/-- No node-count inequality is assumed: it follows by tree induction. -/
theorem goodCount_le (t : RestartTree) (L : ℕ) (h : t.ChainsBounded L) :
    t.goodCount ≤ L * (2 * t.badCount + 1) := by
  have h1 := count_aux t L h
  have h2 := initialGoodRun_le h
  nlinarith

def charge (H : ℝ) (L : ℕ) : RestartTree → ℝ
  | .empty => 0
  | .good l => H / (64 * L) + charge H L l
  | .bad l r => -(127 * H / 128) + charge H L l + charge H L r

theorem charge_eq (t : RestartTree) (H : ℝ) (L : ℕ) :
    t.charge H L = H / (64 * L) * t.goodCount - 127 * H / 128 * t.badCount := by
  induction t with
  | empty => simp [charge, goodCount, badCount]
  | good l ih => simp only [charge, goodCount, badCount, Nat.cast_add, Nat.cast_one, ih]; ring
  | bad l r ihl ihr =>
    simp only [charge, goodCount, badCount, Nat.cast_add, Nat.cast_one, ihl, ihr]
    ring

/-- Cancellation is now verified for every finite tree with bounded good runs. -/
theorem total_charge_le (t : RestartTree) (H : ℝ) (L : ℕ)
    (hH : 0 ≤ H) (hL : 0 < L) (h : t.ChainsBounded L) :
    t.charge H L ≤ H / 64 := by
  rw [charge_eq]
  apply Audit254.recursion_cancellation H L t.goodCount t.badCount hH
  · exact_mod_cast hL
  · positivity
  · exact_mod_cast goodCount_le t L h

/-- A size witness for an interval decomposition. At a good node the left
interval is strictly less than half the parent's size. At a bad node the
charged prefix is nonempty, hence the children's total size is smaller.
These are integer length conditions, not a node-count bound. -/
def Sized : RestartTree → ℕ → Prop
  | .empty, n => n = 0
  | .good l, n => ∃ nl, 2 * nl < n ∧ l.Sized nl
  | .bad l r, n => ∃ nl nr, nl + nr < n ∧ l.Sized nl ∧ r.Sized nr

theorem pow_initialGoodRun_le (t : RestartTree) (n : ℕ) (h : t.Sized n) :
    2 ^ t.initialGoodRun ≤ n + 1 := by
  induction t generalizing n with
  | empty => simp [initialGoodRun]
  | good l ih =>
    obtain ⟨nl, hn, hl⟩ := h
    have hp := ih nl hl
    simp only [initialGoodRun, pow_succ]
    omega
  | bad l r ihl ihr => simp [initialGoodRun]

/-- The logarithmic good-chain limit is derived from interval sizes.
Choosing L=ceil(log2(T+1)) gives T+1 <= 2^L. -/
theorem chainsBounded_of_size (t : RestartTree) (n L : ℕ)
    (h : t.Sized n) (hsize : n + 1 ≤ 2 ^ L) : t.ChainsBounded L := by
  induction t generalizing n with
  | empty => trivial
  | good l ih =>
    obtain ⟨nl, hn, hl⟩ := h
    constructor
    · have hp := pow_initialGoodRun_le (.good l) n ⟨nl, hn, hl⟩
      exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp (le_trans hp hsize)
    · exact ih nl hl (by omega)
  | bad l r ihl ihr =>
    obtain ⟨nl, nr, hn, hl, hr⟩ := h
    exact ⟨ihl nl hl (by omega), ihr nr hr (by omega)⟩

theorem cancellation_of_interval_sizes (t : RestartTree) (n L : ℕ) (H : ℝ)
    (h : t.Sized n) (hsize : n + 1 ≤ 2 ^ L) (hL : 0 < L) (hH : 0 ≤ H) :
    t.charge H L ≤ H / 64 :=
  total_charge_le t H L hH hL (chainsBounded_of_size t n L h hsize)

end RestartTree
end Paper254
#print axioms Paper254.RestartTree.goodCount_le
#print axioms Paper254.RestartTree.total_charge_le
#print axioms Paper254.RestartTree.cancellation_of_interval_sizes
