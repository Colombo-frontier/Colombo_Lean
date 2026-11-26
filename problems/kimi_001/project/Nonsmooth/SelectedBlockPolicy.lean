import Nonsmooth.AdaptiveBlockPolicy

set_option autoImplicit false
namespace Nonsmooth
noncomputable section

/-- A controller selects the full local value-query policy at each fixed-length block. -/
def selectedBlockPolicy {C S X : Type} (p : C → Policy Unit S X) (T : ℕ)
    (next : C → S → C) (out : C → X) (c0 : C) : Policy Unit (C × S) X where
  initial _ := (c0, (p c0).initial ())
  query t _ st := (p st.1).query (t % T) () st.2
  update t _ st y :=
    let st' := (p st.1).update (t % T) () st.2 y
    if (t + 1) % T = 0 then (next st.1 st', (p (next st.1 st')).initial ()) else (st.1, st')
  output _ st := out st.1

def selectedBlockController {C S X : Type} (p : C → Policy Unit S X) (T : ℕ)
    (next : C → S → C) (f : X → ℝ) (c0 : C) : ℕ → C
  | 0 => c0
  | m + 1 => let c := selectedBlockController p T next f c0 m
      next c ((p c).run f () T)

theorem selectedBlockPolicy_run_prefix {C S X : Type} (p : C → Policy Unit S X) {T : ℕ}
    (next : C → S → C) (out : C → X) (c0 : C)
    (f : X → ℝ) (m : ℕ) (c : C)
    (hstart : (selectedBlockPolicy p T next out c0).run f () (m * T) = (c, (p c).initial ()))
    (n : ℕ) (hn : n < T) :
    (selectedBlockPolicy p T next out c0).run f () (m * T + n) =
      (c, (p c).run f () n) := by
  induction n with
  | zero => simpa only [Nat.add_zero, Policy.run] using hstart
  | succ n ih =>
    have hn' : n < T := by omega
    have hi := ih hn'
    rw [show m * T + (n + 1) = (m * T + n) + 1 by omega, Policy.run, hi]
    have hmod : (m * T + n) % T = n := by simp [Nat.add_mod, Nat.mod_eq_of_lt hn']
    have hmodnext : (m * T + n + 1) % T ≠ 0 := by
      rw [show m * T + n + 1 = m * T + (n + 1) by omega]
      simp [Nat.add_mod, Nat.mod_eq_of_lt hn]
    simp only [selectedBlockPolicy, hmod, if_neg hmodnext, Policy.run]

theorem selectedBlockPolicy_run_one_block {C S X : Type} (p : C → Policy Unit S X) {T : ℕ}
    (hT : 0 < T) (next : C → S → C) (out : C → X) (c0 : C)
    (f : X → ℝ) (m : ℕ) (c : C)
    (hstart : (selectedBlockPolicy p T next out c0).run f () (m * T) = (c, (p c).initial ())) :
    (selectedBlockPolicy p T next out c0).run f () ((m + 1) * T) =
      (next c ((p c).run f () T), (p (next c ((p c).run f () T))).initial ()) := by
  have hpref := selectedBlockPolicy_run_prefix p next out c0 f m c hstart (T - 1) (by omega)
  have hboundary : (m + 1) * T = (m * T + (T - 1)) + 1 := by
    rw [Nat.add_mul, Nat.one_mul]
    omega
  rw [hboundary, Policy.run, hpref]
  have hmod : (m * T + (T - 1)) % T = T - 1 := by
    simp [Nat.add_mod, Nat.mod_eq_of_lt (show T - 1 < T by omega)]
  have hmodnext : (m * T + (T - 1) + 1) % T = 0 := by
    rw [← hboundary]
    simp
  simp only [selectedBlockPolicy, hmod, hmodnext, if_true]
  conv_rhs => rw [show T = (T - 1) + 1 by omega, Policy.run]

theorem selectedBlockPolicy_run_exact {C S X : Type} (p : C → Policy Unit S X) {T : ℕ}
    (hT : 0 < T) (next : C → S → C) (out : C → X) (c0 : C)
    (f : X → ℝ) (m : ℕ) :
    (selectedBlockPolicy p T next out c0).run f () (m * T) =
      (selectedBlockController p T next f c0 m, (p (selectedBlockController p T next f c0 m)).initial ()) := by
  induction m with
  | zero => simp only [Nat.zero_mul, Policy.run, selectedBlockPolicy, selectedBlockController]
  | succ m ih => exact selectedBlockPolicy_run_one_block p hT next out c0 f m _ ih

theorem selectedBlockPolicy_result_exact {C S X : Type} (p : C → Policy Unit S X) {T : ℕ}
    (hT : 0 < T) (next : C → S → C) (out : C → X) (c0 : C)
    (f : X → ℝ) (m : ℕ) :
    (selectedBlockPolicy p T next out c0).result f () (m * T) =
      out (selectedBlockController p T next f c0 m) := by
  unfold Policy.result
  rw [selectedBlockPolicy_run_exact p hT]
  rfl

end
end Nonsmooth
