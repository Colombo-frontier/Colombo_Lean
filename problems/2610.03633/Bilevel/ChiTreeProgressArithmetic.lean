import Bilevel.ChiFrontierProtocol

/-! Actual sequential completion counters for a finite recursive tree.
One success increments one child budget; parent prefixes count completed
children. These counters are public combinatorial data, not oracle premises. -/
namespace Bilevel.ChiTreeProgress

def capacity (n : ℕ → ℕ) : ℕ → ℕ → ℕ
  | 0,j => n j+1
  | d+1,j => (n j+1)*capacity n d (j+1)

theorem capacity_pos (n : ℕ → ℕ) (d j : ℕ) : 0<capacity n d j := by
  induction d generalizing j with
  | zero => exact Nat.succ_pos _
  | succ d ih => exact Nat.mul_pos (Nat.succ_pos _) (ih (j+1))

def childBudget (cap i q : ℕ) : ℕ := min cap (q-i*cap)
def parentPrefix (count cap q : ℕ) : ℕ := min count (q/cap)

theorem childBudget_le (cap i q : ℕ) : childBudget cap i q≤cap := Nat.min_le_left _ _

theorem earlier_child_complete (count cap q i : ℕ) (hcap : 0<cap)
    (hi : i<parentPrefix count cap q) : childBudget cap i q=cap := by
  have hq : i+1≤q/cap := (Nat.succ_le_iff.mpr hi).trans (Nat.min_le_right _ _)
  have hm := (Nat.le_div_iff_mul_le hcap).mp hq
  have hs : cap≤q-i*cap := by rw [Nat.add_mul,Nat.one_mul] at hm;omega
  exact Nat.min_eq_left hs

theorem future_child_incomplete (count cap q i : ℕ) (hcap : 0<cap)
    (hi : i<count) (hp : parentPrefix count cap q ≤ i) : childBudget cap i q<cap := by
  have hquot : q/cap<count := by
    by_contra h
    have hh : parentPrefix count cap q=count := Nat.min_eq_left (by omega)
    rw [hh] at hp
    omega
  have hqi : q/cap ≤ i := by simpa only [parentPrefix,Nat.min_eq_right hquot.le] using hp
  have hmul := Nat.mul_le_mul_right cap hqi
  have hrem := Nat.mod_lt q hcap
  have hsplit := Nat.div_add_mod q cap
  rw [Nat.mul_comm cap (q/cap)] at hsplit
  have hlt : q < i*cap+cap := by omega
  have hs : q-i*cap<cap := by omega
  exact (Nat.min_le_right _ _).trans_lt hs

theorem childBudget_complete (cap i : ℕ) : childBudget cap i ((i+1)*cap)=cap := by
  dsimp [childBudget]
  rw [Nat.add_mul,Nat.one_mul]
  omega

theorem childBudget_success (cap i q : ℕ) (hcap : 0<cap) :
    childBudget cap i (q+1)=childBudget cap i q+if i=q/cap then 1 else 0 := by
  have hsplit := Nat.div_add_mod q cap
  rw [Nat.mul_comm cap (q/cap)] at hsplit
  have hrem := Nat.mod_lt q hcap
  rcases lt_trichotomy i (q/cap) with hi|hi|hi
  · have hm := Nat.mul_le_mul_right cap (show i+1≤q/cap by omega)
    have hfull : cap≤q-i*cap := by rw [Nat.add_mul,Nat.one_mul] at hm;omega
    have hfull' : cap≤q+1-i*cap := by omega
    simp only [childBudget,Nat.min_eq_left hfull,Nat.min_eq_left hfull',if_neg (by omega : i≠q/cap),add_zero]
  · subst i
    have hs : q-q/cap*cap=q%cap := by omega
    have hs' : q+1-q/cap*cap=q%cap+1 := by omega
    simp only [childBudget,hs,hs',Nat.min_eq_right hrem.le,Nat.min_eq_right (by omega : q%cap+1≤cap),if_pos rfl,if_true]
  · have hm := Nat.mul_le_mul_right cap (show q/cap+1 ≤ i by omega)
    have hzero : q-i*cap=0 := by rw [Nat.add_mul,Nat.one_mul] at hm;omega
    have hzero' : q+1-i*cap=0 := by rw [Nat.add_mul,Nat.one_mul] at hm;omega
    simp only [childBudget,hzero,hzero',Nat.min_zero,if_neg (by omega : i≠q/cap),add_zero]

end Bilevel.ChiTreeProgress
