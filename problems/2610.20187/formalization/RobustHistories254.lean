import RobustEnergy254
import SparseBranches254

noncomputable section
open scoped BigOperators
namespace Paper254

/-- Local conditions of the inexact-history lemma, stated before any
global regret conclusion. The global error envelopes are shared by all
histories, which is essential when selected intervals change. -/
structure InexactHistorySystem (T : ℕ) (r delta ε ζ : ℕ → ℝ) (lam a B q : ℝ) where
  charge : ℕ → ℕ → ℝ
  pre : ℕ → ℕ → ℝ
  post : ℕ → ℕ → ℝ
  pre_nonneg : ∀ i t,0 ≤ pre i t
  post_nonneg : ∀ i t,0 ≤ post i t
  birth : ∀ i,i<T → pre i i ≤ B
  step : ∀ i t,i ≤ t → t<T → HistoryActive (t+1) (i+1) →
    lam*charge i t ≤ pre i t-post i t+ε t
  movement : ∀ i t,i ≤ t → t+1<T → HistoryActive (t+2) (i+1) →
    Real.sqrt (pre i (t+1)) ≤ Real.sqrt (post i t)+delta t/(Real.sqrt 2*Real.sqrt q)
  prefix_bound : ∀ i n,0<n → i+n ≤ T → HistoryActive (i+n) (i+1) →
    intervalCharge r i n ≤ intervalCharge (charge i) i n+a+intervalCharge ζ i n/lam

def totalLocalError (ε ζ : ℕ → ℝ) : ℕ → ℝ := fun t=>ε t+ζ t

theorem local_error_interval (ε ζ : ℕ → ℝ) (i n : ℕ) :
    intervalCharge (totalLocalError ε ζ) i n=intervalCharge ε i n+intervalCharge ζ i n :=
  intervalCharge_add_functions ε ζ i n

theorem InexactHistorySystem.good_suffix {T : ℕ} {r delta ε ζ : ℕ → ℝ} {lam a B q : ℝ}
    (S : InexactHistorySystem T r delta ε ζ lam a B q)
    (hlam : 0<lam) (ha : 0≤a) (hB : 0≤B) (hq : 0<q)
    (hd : ∀ t,0≤delta t) (L : ℝ) (hL : 1≤L)
    (i n : ℕ) (hn : 0<n) (hend : i+n≤T) (hactive : HistoryActive (i+n) (i+1))
    (hvar : intervalCharge delta i (n-1) ≤ variationThreshold L a B lam q)
    (hdraw : ∀ j≤n,-restartThreshold L a B lam ≤
      intervalCharge (S.charge i) i j-intervalCharge ε i j/lam) :
    intervalCharge r i n ≤ restartThreshold L a B lam/(64*L)+
      intervalCharge (totalLocalError ε ζ) i n/lam := by
  let H := restartThreshold L a B lam
  let z := intervalCharge delta i (n-1)/(Real.sqrt 2*Real.sqrt q)
  have hH : 0≤H := by dsimp [H,restartThreshold]; positivity
  have hz : 0≤z := by dsimp [z]; exact div_nonneg (intervalCharge_nonneg delta hd _ _) (by positivity)
  have hsmall : z ≤ Real.sqrt (B+lam*H)/(512*L) :=
    variation_threshold_movement q (B+lam*H) L (intervalCharge delta i (n-1)) hq
      (by positivity) (by linarith) (intervalCharge_nonneg delta hd _ _) hvar
  have hg := good_history_budget a B lam L z ha hB hlam hL hz hsmall
  have hh := robust_drawdown_bound (n-1)
    (fun t=>S.charge i (i+t)) (fun t=>ε (i+t))
    (fun t=>S.pre i (i+t)) (fun t=>S.post i (i+t))
    (fun t=>delta (i+t)/(Real.sqrt 2*Real.sqrt q)) lam H B hlam
    (fun t _=>S.pre_nonneg i (i+t)) (fun t _=>S.post_nonneg i (i+t))
    (fun t _=>div_nonneg (hd _) (by positivity))
    (by simpa only [Nat.add_zero] using S.birth i (by omega))
    (by intro j hj; exact hdraw j (by omega))
    (by
      intro t ht
      exact S.step i (i+t) (by omega) (by omega)
        (historyActive_prefix hactive (by omega) (by omega)))
    (by
      intro t ht
      exact S.movement i (i+t) (by omega) (by omega)
        (historyActive_prefix hactive (by omega) (by omega)))
  have hsum : (∑ t ∈ Finset.range (n-1),delta (i+t)/(Real.sqrt 2*Real.sqrt q))=z := by
    dsimp [z,intervalCharge]
    rw [Finset.sum_div]
  rw [hsum,show n-1+1=n by omega] at hh
  change intervalCharge (S.charge i) i n ≤ (Real.sqrt (B+lam*H)+z)^2/lam-H+
    intervalCharge ε i n/lam at hh
  have hm := S.prefix_bound i n hn hend hactive
  rw [local_error_interval]
  dsimp [restartThreshold] at hg ⊢
  change a+(Real.sqrt (B+lam*H)+z)^2/lam-H ≤ H/(64*L) at hg
  change intervalCharge r i n ≤ H/(64*L)+(intervalCharge ε i n+intervalCharge ζ i n)/lam
  rw [add_div]
  linarith

theorem InexactHistorySystem.bad_prefix {T : ℕ} {r delta ε ζ : ℕ → ℝ} {lam a B q : ℝ}
    (S : InexactHistorySystem T r delta ε ζ lam a B q)
    (i n : ℕ) (hn : 0<n) (hend : i+n≤T) (hactive : HistoryActive (i+n) (i+1))
    (H : ℝ) (hbad : intervalCharge (S.charge i) i n-intervalCharge ε i n/lam ≤ -H) :
    intervalCharge r i n ≤ a-H+intervalCharge (totalLocalError ε ζ) i n/lam := by
  have hm := S.prefix_bound i n hn hend hactive
  rw [local_error_interval,add_div]
  linarith

end Paper254
#print axioms Paper254.InexactHistorySystem.good_suffix
#print axioms Paper254.InexactHistorySystem.bad_prefix
