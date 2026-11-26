import FullJet.TaylorJetRemainder
import FullJet.GradientModelBounds

open scoped BigOperators ContDiff

namespace FullJet

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {p n : ℕ}

/-- The full Taylor polynomial can be computed solely from a stored packet. -/
noncomputable def packetPolynomial (J : JetPacket p E) (h : E) : ℝ :=
  J 0 (fun _ => 0) + jetTaylor J h

/-- All estimated derivatives are obtained from the stored polynomial. -/
noncomputable def snapshotJet (J : JetPacket p E) (h : E) : JetPacket p E :=
  fullJet p (packetPolynomial J) h

theorem packetPolynomial_contDiff (J : JetPacket p E) : ContDiff ℝ ∞ (packetPolynomial J) :=
  contDiff_const.add (jetTaylor_contDiff J)

theorem packetPolynomial_fullJet (f : E → ℝ) (p : ℕ) (x : E) :
    packetPolynomial (fullJet p f x) = lineTaylor f p x := by
  funext h
  rw [lineTaylor_eq_jetTaylor]
  simp [packetPolynomial, fullJet, iteratedFDeriv_zero_apply]

theorem snapshotJet_error {f : E → ℝ} (hf : ContDiff ℝ p f) (L : ℝ) (hL : 0 ≤ L)
    (hlip : ∀ a b, ‖iteratedFDeriv ℝ p f a - iteratedFDeriv ℝ p f b‖ ≤ L * ‖a - b‖)
    (x h : E) (j : Fin (p + 1)) :
    ‖fullJet p f (x + h) j - snapshotJet (fullJet p f x) h j‖ ≤ L * ‖h‖ ^ (p - j.val + 1) := by
  have hj : j.val ≤ p := Nat.le_of_lt_succ j.isLt
  have hp : p - j.val + j.val = p := Nat.sub_add_cancel hj
  have hlip' : ∀ a b, ‖iteratedFDeriv ℝ (p - j.val + j.val) f a -
      iteratedFDeriv ℝ (p - j.val + j.val) f b‖ ≤ L * ‖a - b‖ := by
    rw [hp]
    exact hlip
  have hb := lineTaylor_jet_remainder (q := p - j.val) (j := j.val)
    (f := f) (by simpa only [← Nat.cast_add, hp] using hf) L hL
    hlip' x h
  simpa only [snapshotJet, packetPolynomial_fullJet, fullJet, hp] using hb

theorem snapshotJet_error_radius {f : E → ℝ} (hf : ContDiff ℝ p f) (L R : ℝ) (hL : 0 ≤ L)
    (hlip : ∀ a b, ‖iteratedFDeriv ℝ p f a - iteratedFDeriv ℝ p f b‖ ≤ L * ‖a - b‖)
    (x h : E) (hh : ‖h‖ ≤ R) (j : Fin (p + 1)) :
    ‖fullJet p f (x + h) j - snapshotJet (fullJet p f x) h j‖ ≤ L * R ^ (p - j.val + 1) := by
  apply (snapshotJet_error hf L hL hlip x h j).trans
  gcongr

theorem Admissible.snapshot_error {Δ L : ℝ} {f : Fin n → E → ℝ}
    (hf : Admissible p n Δ L f) (hL : 0 ≤ L) (x h : E) (j : Fin (p + 1)) :
    ‖fullJet p (average f) (x + h) j - snapshotJet (fullJet p (average f) x) h j‖ ≤
      L * ‖h‖ ^ (p - j.val + 1) :=
  snapshotJet_error (average_contDiff hf.smooth) L hL
    (average_derivative_lipschitz hf.n_pos hf.smooth L hL hf.derivative_lipschitz) x h j

end FullJet
