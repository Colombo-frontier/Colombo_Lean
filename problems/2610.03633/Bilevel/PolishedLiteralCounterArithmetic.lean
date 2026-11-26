import Bilevel.PolishedLiteralPrefixSchedules

/-! Exact lexicographic quotient/remainder arithmetic for the source
flat activation counter and its pre-activation block counts. -/
namespace Bilevel.PolishedLiteralActualObserver
set_option autoImplicit false

def flatCounts (S M a : ℕ) (i : Fin S) : ℕ :=
  if i.val<min a (S*M)/M then M else
    if i.val=min a (S*M)/M then min a (S*M)%M else 0

theorem lex_prefix_iff (M b i j : ℕ) (hM : 0<M) (hj : j<M) :
    j+M*i<b ↔ j<(if i<b/M then M else if i=b/M then b%M else 0) := by
  have he := Nat.div_add_mod b M
  have hm := Nat.mod_lt b hM
  by_cases hi : i<b/M
  · rw [if_pos hi]
    have hp := Nat.mul_le_mul_left M (show i+1≤b/M by omega)
    constructor
    · intro _;exact hj
    · intro _
      calc
        j+M*i<M+M*i := Nat.add_lt_add_right hj _
        _=M*(i+1) := by ring
        _≤M*(b/M) := hp
        _≤b := by omega
  · rw [if_neg hi]
    by_cases hiq : i=b/M
    · rw [if_pos hiq,hiq]
      omega
    · rw [if_neg hiq]
      have hp := Nat.mul_le_mul_left M (show b/M+1 ≤ i by omega)
      have hlt : b<M*(b/M+1) := Nat.lt_mul_div_succ b hM
      constructor
      · intro hh
        have hle : M*i≤j+M*i := Nat.le_add_left _ _
        omega
      · omega

theorem flatCounts_prefix_iff {S M a : ℕ} (hM : 0<M) (i : Fin S) (j : Fin M) :
    (finProdFinEquiv (i,j)).val<min (S*M) a ↔ j.val<flatCounts S M a i := by
  change j.val+M*i.val<min (S*M) a ↔ _
  rw [Nat.min_comm (S*M) a]
  exact lex_prefix_iff M (min a (S*M)) i.val j.val hM j.isLt

theorem flatCounts_current_bound {S M a : ℕ} (hM : 0<M) (i : Fin S)
    (hi : min a (S*M)/M ≤ i.val) : flatCounts S M a i≤M-1 := by
  unfold flatCounts
  split_ifs with hlt heq
  · omega
  · have := Nat.mod_lt (min a (S*M)) hM
    omega
  · omega

/-- The newly activated current coordinate lies in the success-extended
flat prefix. Completed earlier blocks already lie in that prefix. -/
theorem flatCounts_active_prefix {S M a : ℕ} (hM : 0<M) (i : Fin S) (j : Fin M)
    (hj : j.val<(if i.val≤min a (S*M)/M then flatCounts S M a i+1 else 0)) :
    (finProdFinEquiv (i,j)).val<min (S*M) (a+1) := by
  let b := min a (S*M)
  have he : M*(b/M)+b%M=b := Nat.div_add_mod b M
  have hm : b%M<M := Nat.mod_lt b hM
  by_cases hi : i.val<b/M
  · have hcount : flatCounts S M a i=M := by
      change (if i.val<b/M then M else if i.val=b/M then b%M else 0)=M
      rw [if_pos hi]
    have hp := (flatCounts_prefix_iff (a:=a) hM i j).mpr (by simpa only [hcount] using j.isLt)
    exact hp.trans_le (min_le_min_left _ (by omega : a≤a+1))
  · by_cases hiq : i.val=b/M
    · have hbcap : b<S*M := by
        have hle : b≤S*M := min_le_right _ _
        by_contra hnot
        have hb : b=S*M := le_antisymm hle (Nat.le_of_not_gt hnot)
        have hr : b/M=S := by rw [hb];simp [hM.ne']
        have := i.isLt
        omega
      have ha : a<S*M := by
        by_contra hnot
        have hb : b=S*M := min_eq_right (Nat.le_of_not_gt hnot)
        exact (Nat.ne_of_lt hbcap) hb
      have hb : b=a := min_eq_left (Nat.le_of_lt ha)
      have hle : i.val≤b/M := by omega
      have hcount : flatCounts S M a i=b%M := by
        change (if i.val<b/M then M else if i.val=b/M then b%M else 0)=b%M
        rw [if_neg hi,if_pos hiq]
      have hj' : j.val≤b%M := by
        change j.val<(if i.val≤b/M then flatCounts S M a i+1 else 0) at hj
        rw [if_pos hle,hcount] at hj
        omega
      change j.val+M*i.val<min (S*M) (a+1)
      rw [min_eq_right (by omega : a+1≤S*M)]
      nlinarith
    · have hle : ¬i.val≤min a (S*M)/M := by change ¬i.val≤b/M;omega
      simp only [if_neg hle] at hj
      omega

end Bilevel.PolishedLiteralActualObserver
