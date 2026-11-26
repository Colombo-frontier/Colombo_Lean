import Bilevel.TransportAuxiliaryFrameStore

/-! A deterministic stage schedule lifted to actual transport rounds.
The round t query uses stage floor(t/length); a completion at t+1 reveals
only after that query. No random success coin is introduced. -/
noncomputable section
namespace Bilevel.TransportAuxiliaryFrame
set_option autoImplicit false

theorem Schedule.count_mono {k T : ℕ} (P : Schedule k T) (i : Fin k) :
    Monotone (fun t => P.count t i) :=
  monotone_nat_of_le_succ (fun t => P.mono t i)

def Schedule.rounds {k T : ℕ} (P : Schedule k T) (length : ℕ) (hL : 0 < length) : Schedule k T where
  count t i := P.count (t/length) i
  zero i := by simpa only [Nat.zero_div] using P.zero i
  mono t i := P.count_mono i (Nat.div_le_div_right (by omega : t ≤ t+1))
  step t i := by
    have hd : (t+1)/length ≤ t/length+1 := by
      have hh : (t+1)/length ≤ (t+length)/length :=
        Nat.div_le_div_right (show t+1 ≤ t+length by omega)
      simpa only [Nat.add_div_right t hL] using hh
    exact (P.count_mono i hd).trans (P.step (t/length) i)
  bound t i := P.bound (t/length) i

theorem rounds_count {k T : ℕ} (P : Schedule k T) (length : ℕ) (hL : 0 < length)
    (t : ℕ) (i : Fin k) : (P.rounds length hL).count t i=P.count (t/length) i := rfl

theorem rounds_no_early_release {k T : ℕ} (P : Schedule k T) (length : ℕ) (hL : 0 < length)
    (t : ℕ) (i : Fin k) (h : (t+1)/length=t/length) :
    request (P.rounds length hL) t i=false := by
  simp only [request,Schedule.rounds,h,lt_self_iff_false,decide_false]

theorem rounds_at_completion {k T : ℕ} (P : Schedule k T) (length : ℕ) (hL : 0 < length)
    (q : ℕ) (i : Fin k) : (P.rounds length hL).count (q*length) i=P.count q i := by
  simp only [Schedule.rounds,Nat.mul_div_cancel _ hL]

end Bilevel.TransportAuxiliaryFrame
