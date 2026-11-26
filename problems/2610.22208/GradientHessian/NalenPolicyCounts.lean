import GradientHessian.NalenPolicy
import Mathlib.Algebra.Order.Floor.Div

/-! Exact literal instruction counts for the NALEN machine, including
initialization and every complete-block candidate evaluation. -/

namespace GradientHessian.NalenPolicy
open scoped BigOperators

theorem sum_positive_mod (N q : ℕ) :
    (∑ n ∈ Finset.range N,if (n+1)%q=0 then 1 else 0)=N/q := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ,ih]
    simp [Nat.succ_div,Nat.dvd_iff_mod_eq_zero,add_ite]

theorem sum_zero_mod (N m : ℕ) (hm : 0<m) :
    (∑ n ∈ Finset.range N,if n%m=0 then 1 else 0)=(N+m-1)/m := by
  cases N with
  | zero => simp [Nat.div_eq_of_lt (show m-1<m by omega)]
  | succ N =>
    rw [Finset.sum_range_succ',sum_positive_mod]
    have he : N+1+m-1=N+m := by omega
    rw [he,Nat.add_div_right _ hm]
    simp

theorem ordinary_schedule_count (m q N : ℕ) :
    (∑ k ∈ Finset.range (1+4*N),if kind m q k=1 then 1 else 0)=1+2*N+N/q := by
  have h (N : ℕ) :
      (∑ k ∈ Finset.range (1+4*N),if kind m q k=1 then 1 else 0)=
        1+2*N+∑ n ∈ Finset.range N,if (n+1)%q=0 then 1 else 0 := by
    induction N with
    | zero =>
      simp only [Nat.mul_zero,Nat.add_zero,Finset.sum_range_succ,Finset.sum_range_zero,kind_initial]
      norm_num [Fin.ext_iff]
    | succ N ih =>
      have he : 1+4*(N+1)=(1+4*N)+1+1+1+1 := by omega
      rw [he,Finset.sum_range_succ,Finset.sum_range_succ,Finset.sum_range_succ,Finset.sum_range_succ,ih]
      have h2 : 1+4*N+1+1=1+4*N+2 := by omega
      have h3 : 1+4*N+1+1+1=1+4*N+3 := by omega
      rw [h2,h3,kind_snapshot,kind_predict,kind_correct,kind_candidate,Finset.sum_range_succ]
      split_ifs <;> omega
  rw [h,sum_positive_mod]

theorem rich_schedule_count (m q N : ℕ) (hm : 0<m) :
    (∑ k ∈ Finset.range (1+4*N),if kind m q k=2 then 1 else 0)=(N+m-1)/m := by
  have h (N : ℕ) :
      (∑ k ∈ Finset.range (1+4*N),if kind m q k=2 then 1 else 0)=
        ∑ n ∈ Finset.range N,if n%m=0 then 1 else 0 := by
    induction N with
    | zero =>
      simp only [Nat.mul_zero,Nat.add_zero,Finset.sum_range_succ,Finset.sum_range_zero,kind_initial]
      norm_num [Fin.ext_iff]
    | succ N ih =>
      have he : 1+4*(N+1)=(1+4*N)+1+1+1+1 := by omega
      rw [he,Finset.sum_range_succ,Finset.sum_range_succ,Finset.sum_range_succ,Finset.sum_range_succ,ih]
      have h2 : 1+4*N+1+1=1+4*N+2 := by omega
      have h3 : 1+4*N+1+1+1=1+4*N+3 := by omega
      rw [h2,h3,kind_snapshot,kind_predict,kind_correct,kind_candidate,Finset.sum_range_succ]
      split_ifs <;> omega
  rw [h,sum_zero_mod N m hm]

theorem policy_exact_caps (d : ℕ) {D : ℝ} (hD : 0≤D) (η : ℝ) (m q N : ℕ) (hm : 0<m)
    (ordinary : Model.Point d → Model.OrdinaryReply d) (rich : Model.Point d → Model.RichReply d) :
    (policy d hD η m q N).HasCaps ordinary rich (1+2*N+N/q) ((N+m-1)/m) := by
  have h := policy_schedule_caps d hD η m q N ordinary rich
  change (policy d hD η m q N).HasCaps ordinary rich
    (∑ k ∈ Finset.range (1+4*N),if kind m q k=1 then 1 else 0)
    (∑ k ∈ Finset.range (1+4*N),if kind m q k=2 then 1 else 0) at h
  rwa [ordinary_schedule_count,rich_schedule_count m q N hm] at h

theorem policy_source_caps (d : ℕ) {D : ℝ} (hD : 0≤D) (η : ℝ) (m q N : ℕ) (hm : 0<m)
    (ordinary : Model.Point d → Model.OrdinaryReply d) (rich : Model.Point d → Model.RichReply d) :
    (policy d hD η m q N).HasCaps ordinary rich (3*N+1) (N ⌈/⌉ m) := by
  intro seed n
  obtain ⟨ho,hr⟩ := policy_exact_caps d hD η m q N hm ordinary rich seed n
  refine ⟨ho.trans ?_,hr⟩
  have := Nat.div_le_self N q
  omega

end GradientHessian.NalenPolicy
