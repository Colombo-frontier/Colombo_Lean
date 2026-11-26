import RobustHistories254

noncomputable section
namespace Paper254

theorem InexactHistorySystem.low_variation {T : ℕ} {r delta ε ζ : ℕ → ℝ} {lam a B q : ℝ}
    (S : InexactHistorySystem T r delta ε ζ lam a B q)
    (hlam : 0<lam) (ha : 0≤a) (hB : 0≤B) (hq : 0<q) (hd : ∀ t,0≤delta t)
    (L : ℕ) (hL : 1≤L) (hpow : T<2^L)
    (start n₀ : ℕ) (hn : 0<n₀) (hend : start+n₀≤T)
    (hvar : intervalCharge delta start (n₀-1) ≤ variationThreshold L a B lam q) :
    intervalCharge r start n₀ ≤ restartThreshold L a B lam/64+
      intervalCharge (totalLocalError ε ζ) start n₀/lam := by
  let H := restartThreshold L a B lam
  let C := H/(64*L)
  let error := totalLocalError ε ζ
  let shifted := fun t=>r (start+t)
  let shiftedError := fun t=>error (start+t)
  have hLr : (1 : ℝ)≤L := by exact_mod_cast hL
  have hLp : (0 : ℝ)<L := by linarith
  have hH : 0≤H := by dsimp [H,restartThreshold]; positivity
  have hC : 0≤C := by dsimp [C]; positivity
  have haH : 128*a≤H := by
    have hratio : 0≤B/lam := div_nonneg hB hlam.le
    dsimp [H,restartThreshold]
    nlinarith [mul_nonneg (show 0≤(L:ℝ)-1 by linarith) ha,mul_nonneg hLp.le hratio]
  have hpay : 2*C*L≤H-a := by
    have he : 2*C*L=H/32 := by dsimp [C]; field_simp; ring
    rw [he]
    linarith
  have hcase : ∀ b n,0<n → b+n≤n₀ → ∃ left,2*left<n ∧
      (intervalCharge shifted (b+left) (n-left) ≤ C+intervalCharge shiftedError (b+left) (n-left)/lam ∨
        ∃ j,0<j ∧ j≤n-left ∧
          intervalCharge shifted (b+left) j ≤ -(H-a)+intervalCharge shiftedError (b+left) j/lam) := by
    intro b n hnpos hnend
    obtain ⟨i,hstart,hmid,hactive⟩ := streaming_history_cover
      (start+b+1) (start+b+n) (by omega) (by omega)
    have hi : 0 < i := by omega
    let j₀ := i-1
    let left := j₀-(start+b)
    have hid : j₀=start+b+left := by dsimp [j₀,left]; omega
    have hbirth : j₀+1=i := by dsimp [j₀]; omega
    have hleft : 2*left<n := by dsimp [left,j₀]; omega
    have hsuffix : 0<n-left := by omega
    have heactive : HistoryActive (j₀+(n-left)) (j₀+1) := by
      rw [hbirth,show j₀+(n-left)=start+b+n by omega]
      exact hactive
    have hp : intervalCharge delta j₀ (n-left-1) ≤ variationThreshold L a B lam q :=
      (intervalCharge_subinterval_le delta hd start (n₀-1) j₀ (n-left-1)
        (by omega) (by omega)).trans hvar
    refine ⟨left,hleft,?_⟩
    by_cases hdraw : ∀ j ≤ n-left, -H ≤ intervalCharge (S.charge j₀) j₀ j-intervalCharge ε j₀ j/lam
    · left
      have hg := S.good_suffix hlam ha hB hq hd L hLr j₀ (n-left) hsuffix
        (by omega) heactive hp hdraw
      change intervalCharge (fun t=>r (start+t)) (b+left) (n-left) ≤
        C+intervalCharge (fun t=>error (start+t)) (b+left) (n-left)/lam
      rw [intervalCharge_shift,intervalCharge_shift,show start+(b+left)=j₀ by omega]
      exact hg
    · right
      push_neg at hdraw
      obtain ⟨j,hjlen,hjbad⟩ := hdraw
      have hjpos : 0<j := by
        by_contra h
        have hj0 : j=0 := by omega
        subst j
        simp only [intervalCharge,Finset.range_zero,Finset.sum_empty,zero_div,sub_zero] at hjbad
        linarith
      have hjactive : HistoryActive (j₀+j) (j₀+1) :=
        historyActive_prefix heactive (by omega) (by omega)
      have hb := S.bad_prefix j₀ j hjpos (by omega) hjactive H hjbad.le
      refine ⟨j,hjpos,hjlen,?_⟩
      change intervalCharge (fun t=>r (start+t)) (b+left) j ≤
        -(H-a)+intervalCharge (fun t=>error (start+t)) (b+left) j/lam
      rw [intervalCharge_shift,intervalCharge_shift,show start+(b+left)=j₀ by omega]
      linarith
  have hh := robust_interval_restart shifted shiftedError n₀ L C (H-a) lam hC hpay
    hcase 0 n₀ L (by omega) le_rfl (by omega)
  have he : C*L=H/64 := by dsimp [C]; field_simp
  rw [he] at hh
  change intervalCharge (fun t=>r (start+t)) 0 n₀ ≤
    H/64+intervalCharge (fun t=>error (start+t)) 0 n₀/lam at hh
  simpa only [intervalCharge_shift,Nat.add_zero] using hh

/-- Full fixed-scale robustness: local history and master errors are
counted once, including across all restart and partition boundaries. -/
theorem InexactHistorySystem.fixed_scale {T : ℕ} {r delta ε ζ : ℕ → ℝ} {lam a B q : ℝ}
    (S : InexactHistorySystem T r delta ε ζ lam a B q)
    (hlam : 0<lam) (ha : 0≤a) (hB : 0<B) (hq : 0<q) (hd : ∀ t,0≤delta t)
    (L : ℕ) (hL : 1≤L) (hpow : T<2^L) :
    intervalCharge r 0 T ≤ (restartThreshold L a B lam/64)*
      (1+intervalCharge delta 0 (T-1)/variationThreshold L a B lam q)+
      intervalCharge (totalLocalError ε ζ) 0 T/lam := by
  have hLp : (0 : ℝ)<L := by exact_mod_cast (by omega : 0<L)
  have hH : 0<restartThreshold L a B lam := by dsimp [restartThreshold]; positivity
  have hV : 0<variationThreshold L a B lam q := by dsimp [variationThreshold]; positivity
  exact robust_variation_partition r (totalLocalError ε ζ) delta T
    (restartThreshold L a B lam/64) (variationThreshold L a B lam q) lam hd
    (by positivity) hV (fun s n hn hend hvar=>S.low_variation hlam ha hB.le hq hd L hL hpow s n hn hend hvar)
    0 T (by omega)

end Paper254
#print axioms Paper254.InexactHistorySystem.fixed_scale
