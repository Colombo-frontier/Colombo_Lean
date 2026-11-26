import GradientHessian.JetLocality
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.FaaDiBruno
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Tactic

/-! Pointwise second-jet algebra. Flat endpoint jets suffice: no open
plateau, compact support, or bound on the multiplying coefficient is needed. -/

noncomputable section
namespace GradientHessian.SecondJetAlgebra
open JetLocality

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def ZeroSecondJet (f : E → ℝ) (x : E) : Prop :=
  ∀ n ≤ 2, iteratedFDeriv ℝ n f x = 0

theorem richJet_eq_of_iterated_eq {f g : E → ℝ} {x : E}
    (h : ∀ n ≤ 2, iteratedFDeriv ℝ n f x = iteratedFDeriv ℝ n g x) :
    richJet f x = richJet g x := by
  have h0 : f x = g x := by
    simpa only [iteratedFDeriv_zero_apply] using
      congrArg (fun T => T (fun i : Fin 0 => Fin.elim0 i)) (h 0 (by norm_num))
  have h1 : fderiv ℝ f x = fderiv ℝ g x := by
    ext v
    simpa only [iteratedFDeriv_one_apply] using
      congrArg (fun T => T (fun _ : Fin 1 => v)) (h 1 (by norm_num))
  have h2 : fderiv ℝ (fderiv ℝ f) x = fderiv ℝ (fderiv ℝ g) x := by
    ext v w
    simpa only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons] using congrArg (fun T => T ![v,w]) (h 2 le_rfl)
  exact Prod.ext h0 (Prod.ext h1 h2)

theorem richJet_eq_zero_iff (f : E → ℝ) (x : E) : richJet f x = 0 ↔ ZeroSecondJet f x := by
  constructor
  · intro h
    have h0 : f x = 0 := congrArg Prod.fst h
    have h1 : fderiv ℝ f x = 0 := congrArg (fun t => t.2.1) h
    have h2 : fderiv ℝ (fderiv ℝ f) x = 0 := congrArg (fun t => t.2.2) h
    intro n hn
    interval_cases n
    · ext v
      simp only [iteratedFDeriv_zero_apply, h0, ContinuousMultilinearMap.zero_apply]
    · ext v
      simp only [iteratedFDeriv_one_apply, h1, ContinuousLinearMap.zero_apply,
        ContinuousMultilinearMap.zero_apply]
    · ext v
      simp only [iteratedFDeriv_two_apply, h2, ContinuousLinearMap.zero_apply,
        ContinuousMultilinearMap.zero_apply]
  · intro h
    rw [← richJet_zero x]
    apply richJet_eq_of_iterated_eq
    intro n hn
    simpa only [iteratedFDeriv_zero_fun, Pi.zero_apply] using h n hn

theorem ZeroSecondJet.value {f : E → ℝ} {x : E} (h : ZeroSecondJet f x) : f x = 0 :=
  congrArg Prod.fst ((richJet_eq_zero_iff f x).mpr h)

theorem ZeroSecondJet.first {f : E → ℝ} {x : E} (h : ZeroSecondJet f x) : fderiv ℝ f x = 0 :=
  congrArg (fun t => t.2.1) ((richJet_eq_zero_iff f x).mpr h)

theorem ZeroSecondJet.second {f : E → ℝ} {x : E} (h : ZeroSecondJet f x) :
    fderiv ℝ (fderiv ℝ f) x = 0 :=
  congrArg (fun t => t.2.2) ((richJet_eq_zero_iff f x).mpr h)

theorem zeroSecondJet_of_fderiv {f : E → ℝ} {x : E} (h0 : f x = 0)
    (h1 : fderiv ℝ f x = 0) (h2 : fderiv ℝ (fderiv ℝ f) x = 0) : ZeroSecondJet f x :=
  (richJet_eq_zero_iff f x).mp (Prod.ext h0 (Prod.ext h1 h2))

theorem ordinaryJet_eq_of_richJet_eq {f g : E → ℝ} {x : E} (h : richJet f x = richJet g x) :
    ordinaryJet f x = ordinaryJet g x := by
  have h0 : f x = g x := congrArg Prod.fst h
  have h1 : fderiv ℝ f x = fderiv ℝ g x := congrArg (fun t => t.2.1) h
  exact Prod.ext h0 h1

theorem zeroSecondJet_of_deriv {f : ℝ → ℝ} {x : ℝ}
    (h0 : f x = 0) (h1 : deriv f x = 0) (h2 : deriv (deriv f) x = 0) : ZeroSecondJet f x := by
  intro n hn
  apply norm_eq_zero.mp
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  interval_cases n
  · simp only [iteratedDeriv_zero, h0, norm_zero]
  · simp only [iteratedDeriv_one, h1, norm_zero]
  · simp only [show (2:ℕ) = 1+1 from rfl, iteratedDeriv_succ, iteratedDeriv_one,
      iteratedDeriv_zero, h2, norm_zero]

theorem ZeroSecondJet.mul_left {coefficient gate : E → ℝ} {x : E}
    (hc : ContDiff ℝ 2 coefficient) (hg : ContDiff ℝ 2 gate) (hz : ZeroSecondJet gate x) :
    ZeroSecondJet (fun y => coefficient y*gate y) x := by
  intro n hn
  apply norm_eq_zero.mp
  apply le_antisymm _ (norm_nonneg _)
  have h := norm_iteratedFDeriv_mul_le hc hg x (by exact_mod_cast hn)
  have hzero (i : ℕ) : ‖iteratedFDeriv ℝ (n-i) gate x‖ = 0 := by
    rw [hz (n-i) (by omega), norm_zero]
  simpa only [hzero, mul_zero, Finset.sum_const_zero] using h

theorem ZeroSecondJet.mul_right {coefficient gate : E → ℝ} {x : E}
    (hc : ContDiff ℝ 2 coefficient) (hg : ContDiff ℝ 2 gate) (hz : ZeroSecondJet gate x) :
    ZeroSecondJet (fun y => gate y*coefficient y) x := by
  simpa only [mul_comm] using hz.mul_left hc hg

theorem richJet_mul_zero {coefficient gate : E → ℝ} {x : E}
    (hc : ContDiff ℝ 2 coefficient) (hg : ContDiff ℝ 2 gate) (hz : ZeroSecondJet gate x) :
    richJet (fun y => coefficient y*gate y) x = 0 :=
  (richJet_eq_zero_iff _ _).mpr (hz.mul_left hc hg)

theorem mul_derivatives_zero {coefficient gate : E → ℝ} {x : E}
    (hc : ContDiff ℝ 2 coefficient) (hg : ContDiff ℝ 2 gate) (h0 : gate x = 0)
    (h1 : fderiv ℝ gate x = 0) (h2 : fderiv ℝ (fderiv ℝ gate) x = 0) :
    coefficient x*gate x = 0 ∧ fderiv ℝ (fun y => coefficient y*gate y) x = 0 ∧
      fderiv ℝ (fderiv ℝ (fun y => coefficient y*gate y)) x = 0 := by
  have h := (zeroSecondJet_of_fderiv h0 h1 h2).mul_left hc hg
  exact ⟨h.value, h.first, h.second⟩

theorem richJet_remove_gated_term {baseline coefficient gate : E → ℝ} {x : E}
    (hb : ContDiff ℝ 2 baseline) (hc : ContDiff ℝ 2 coefficient) (hg : ContDiff ℝ 2 gate)
    (hz : ZeroSecondJet gate x) :
    richJet (fun y => baseline y+coefficient y*gate y) x = richJet baseline x := by
  apply richJet_eq_of_iterated_eq
  intro n hn
  rw [iteratedFDeriv_add_apply' (hb.contDiffAt.of_le (by exact_mod_cast hn))
    ((hc.mul hg).contDiffAt.of_le (by exact_mod_cast hn)), (hz.mul_left hc hg) n hn, add_zero]

theorem richJet_remove_sub_gated_term {baseline coefficient gate : E → ℝ} {x : E}
    (hb : ContDiff ℝ 2 baseline) (hc : ContDiff ℝ 2 coefficient) (hg : ContDiff ℝ 2 gate)
    (hz : ZeroSecondJet gate x) :
    richJet (fun y => baseline y-coefficient y*gate y) x = richJet baseline x := by
  convert richJet_remove_gated_term hb hc.neg hg hz using 1
  congr 1
  funext y
  ring

theorem richJet_replace_coefficient {baseline coefficient replacement gate : E → ℝ} {x : E}
    (hb : ContDiff ℝ 2 baseline) (hc : ContDiff ℝ 2 coefficient)
    (hr : ContDiff ℝ 2 replacement) (hg : ContDiff ℝ 2 gate) (hz : ZeroSecondJet gate x) :
    richJet (fun y => baseline y+coefficient y*gate y) x =
      richJet (fun y => baseline y+replacement y*gate y) x :=
  (richJet_remove_gated_term hb hc hg hz).trans (richJet_remove_gated_term hb hr hg hz).symm

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem ZeroSecondJet.comp {outer : F → ℝ} {inner : E → F} {x : E}
    (ho : ContDiff ℝ 2 outer) (hi : ContDiff ℝ 2 inner) (hz : ZeroSecondJet outer (inner x)) :
    ZeroSecondJet (outer ∘ inner) x := by
  intro n hn
  ext v
  rw [iteratedFDeriv_comp ho.contDiffAt hi.contDiffAt (by exact_mod_cast hn)]
  simp only [FormalMultilinearSeries.taylorComp, ContinuousMultilinearMap.sum_apply,
    FormalMultilinearSeries.compAlongOrderedFinpartition_apply,
    OrderedFinpartition.applyOrderedFinpartition_apply, ftaylorSeries, ContinuousMultilinearMap.zero_apply]
  apply Finset.sum_eq_zero
  intro c _
  rw [hz c.length (c.length_le.trans hn)]
  simp only [ContinuousMultilinearMap.zero_apply]

theorem ZeroSecondJet.comp_linear {gate : F → ℝ} (hg : ContDiff ℝ 2 gate)
    (L : E →L[ℝ] F) {x : E} (hz : ZeroSecondJet gate (L x)) :
    ZeroSecondJet (gate ∘ L) x := hz.comp hg L.contDiff

end GradientHessian.SecondJetAlgebra
