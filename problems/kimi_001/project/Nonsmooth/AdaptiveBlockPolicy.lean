import Nonsmooth.CyclicPeakLegality

set_option autoImplicit false
namespace Nonsmooth
noncomputable section

/-- A discrete controller chooses the geometric simulation for each fixed-length query block. -/
def adaptiveBlockPolicy {C S I X : Type} (p : Policy Unit S I) (T : ℕ)
    (q : C → I → X) (next : C → I → C) (out : C → X) (c0 : C) : Policy Unit (C × S) X where
  initial _ := (c0, p.initial ())
  query t _ st := q st.1 (p.query (t % T) () st.2)
  update t _ st y :=
    let st' := p.update (t % T) () st.2 y
    if (t + 1) % T = 0 then (next st.1 (p.output () st'), p.initial ()) else (st.1, st')
  output _ st := out st.1

def adaptiveBlockController {C S I X : Type} (p : Policy Unit S I) (T : ℕ)
    (q : C → I → X) (next : C → I → C) (f : X → ℝ) (c0 : C) : ℕ → C
  | 0 => c0
  | m + 1 => let c := adaptiveBlockController p T q next f c0 m
      next c (p.result (fun i => f (q c i)) () T)

theorem adaptiveBlockPolicy_run_prefix {C S I X : Type} (p : Policy Unit S I) {T : ℕ}
    (q : C → I → X) (next : C → I → C) (out : C → X) (c0 : C)
    (f : X → ℝ) (m : ℕ) (c : C)
    (hstart : (adaptiveBlockPolicy p T q next out c0).run f () (m * T) = (c, p.initial ()))
    (n : ℕ) (hn : n < T) :
    (adaptiveBlockPolicy p T q next out c0).run f () (m * T + n) =
      (c, p.run (fun i => f (q c i)) () n) := by
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
    simp only [adaptiveBlockPolicy, hmod, if_neg hmodnext, Policy.run]

theorem adaptiveBlockPolicy_run_one_block {C S I X : Type} (p : Policy Unit S I) {T : ℕ}
    (hT : 0 < T) (q : C → I → X) (next : C → I → C) (out : C → X) (c0 : C)
    (f : X → ℝ) (m : ℕ) (c : C)
    (hstart : (adaptiveBlockPolicy p T q next out c0).run f () (m * T) = (c, p.initial ())) :
    (adaptiveBlockPolicy p T q next out c0).run f () ((m + 1) * T) =
      (next c (p.result (fun i => f (q c i)) () T), p.initial ()) := by
  have hpref := adaptiveBlockPolicy_run_prefix p q next out c0 f m c hstart (T - 1) (by omega)
  have hboundary : (m + 1) * T = (m * T + (T - 1)) + 1 := by
    rw [Nat.add_mul, Nat.one_mul]
    omega
  rw [hboundary, Policy.run, hpref]
  have hmod : (m * T + (T - 1)) % T = T - 1 := by
    simp [Nat.add_mod, Nat.mod_eq_of_lt (show T - 1 < T by omega)]
  have hmodnext : (m * T + (T - 1) + 1) % T = 0 := by
    rw [← hboundary]
    simp
  simp only [adaptiveBlockPolicy, hmod, hmodnext, if_true, Policy.result]
  conv_rhs => rw [show T = (T - 1) + 1 by omega, Policy.run]

theorem adaptiveBlockPolicy_run_exact {C S I X : Type} (p : Policy Unit S I) {T : ℕ}
    (hT : 0 < T) (q : C → I → X) (next : C → I → C) (out : C → X) (c0 : C)
    (f : X → ℝ) (m : ℕ) :
    (adaptiveBlockPolicy p T q next out c0).run f () (m * T) =
      (adaptiveBlockController p T q next f c0 m, p.initial ()) := by
  induction m with
  | zero => simp only [Nat.zero_mul, Policy.run, adaptiveBlockPolicy, adaptiveBlockController]
  | succ m ih => exact adaptiveBlockPolicy_run_one_block p hT q next out c0 f m _ ih

theorem adaptiveBlockPolicy_result_exact {C S I X : Type} (p : Policy Unit S I) {T : ℕ}
    (hT : 0 < T) (q : C → I → X) (next : C → I → C) (out : C → X) (c0 : C)
    (f : X → ℝ) (m : ℕ) :
    (adaptiveBlockPolicy p T q next out c0).result f () (m * T) =
      out (adaptiveBlockController p T q next f c0 m) := by
  unfold Policy.result
  rw [adaptiveBlockPolicy_run_exact p hT]
  rfl

end
end Nonsmooth
