import Schedule254

namespace Paper254

def activeHistories (t : ℕ) : Finset ℕ :=
  (Finset.Icc 1 t).filter (fun i => t-i ≤ historyLifetime i)

theorem mem_activeHistories (t i : ℕ) : i ∈ activeHistories t ↔ HistoryActive t i := by
  simp only [activeHistories, Finset.mem_filter, Finset.mem_Icc, HistoryActive]
  tauto

theorem divisible_predecessor_reconstruct {t i b : ℕ} (hit : i ≤ t) (hdiv : b ∣ i) :
    i+b*((t-i)/b)+t%b = t := by
  have he : t = i+(t-i) := by omega
  have hm : (t-i)%b = t%b := by
    conv_rhs => rw [he, Nat.add_mod, Nat.mod_eq_zero_of_dvd hdiv, zero_add, Nat.mod_mod]
  have hd := Nat.mod_add_div (t-i) b
  omega

theorem activeHistories_card (t : ℕ) :
    (activeHistories t).card ≤ 5*(Nat.log 2 t+1) := by
  let f := fun i => (padicValNat 2 i, (t-i)/(2^padicValNat 2 i))
  let target := (Finset.range (Nat.log 2 t+1)) ×ˢ (Finset.range 5)
  have hmaps : Set.MapsTo f (activeHistories t) target := by
    intro i hi
    have hai := (mem_activeHistories t i).mp hi
    have hp := pow_padicValNat_dvd (p := 2) (n := i)
    have hpow : 2^padicValNat 2 i ≤ t :=
      le_trans (Nat.le_of_dvd (show 0 < i from hai.1) hp) hai.2.1
    have hk := Nat.le_log_of_pow_le (by norm_num : 1 < (2 : ℕ)) hpow
    have hb : 0 < 2^padicValNat 2 i := by positivity
    have hsize : t-i ≤ 4*(2^padicValNat 2 i) := by
      simpa [historyLifetime, pow_add, Nat.mul_comm] using hai.2.2
    have hq : (t-i)/(2^padicValNat 2 i) ≤ 4 := by
      have hh := Nat.div_le_div_right (c := 2^padicValNat 2 i) hsize
      simpa [Nat.mul_div_cancel, ne_of_gt hb] using hh
    exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by dsimp [f]; omega),
      Finset.mem_range.mpr (by dsimp [f]; omega)⟩
  have hinj : Set.InjOn f (activeHistories t) := by
    intro i hi j hj heq
    have hai := (mem_activeHistories t i).mp hi
    have haj := (mem_activeHistories t j).mp hj
    have hk : padicValNat 2 i = padicValNat 2 j := congrArg Prod.fst heq
    have hq := congrArg Prod.snd heq
    change (t-i)/(2^padicValNat 2 i) = (t-j)/(2^padicValNat 2 j) at hq
    have hri := divisible_predecessor_reconstruct hai.2.1 (pow_padicValNat_dvd (p := 2) (n := i))
    have hrj := divisible_predecessor_reconstruct haj.2.1 (pow_padicValNat_dvd (p := 2) (n := j))
    rw [hk] at hq hri
    rw [hq] at hri
    omega
  have hc := Finset.card_le_card_of_injOn f hmaps hinj
  simpa [target, Finset.card_product, Nat.mul_comm] using hc

end Paper254
#print axioms Paper254.activeHistories_card
