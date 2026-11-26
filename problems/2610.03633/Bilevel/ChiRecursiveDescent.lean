import Bilevel.ChiRecursivePerturbation

/-! The actual one-block stop-or-descend argument. Its local base margins
are precisely the independently constructed weighted local certificates. -/
noncomputable section
namespace Bilevel.ChiRecursive

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem norm_fderiv_eq_norm_gradient (f : E → ℝ) (u : E) :
    ‖fderiv ℝ f u‖=‖gradient f u‖ := by
  simp only [gradient,LinearIsometryEquiv.norm_map]

theorem slice_stop_or_descend (D : Geometry E) (d j : ℕ) (I : List ℕ) (u : ℕ → E)
    {Cs Cr δ b w ρ Rp : ℝ} (hCs : 0≤Cs) (hCr : 0≤Cr) (hδ : 0≤δ)
    (hδsmall : δ≤releaseTolerance (Cr+Cs))
    (hell : 0≤(D j I).ell) (hh : 0<(D j I).width) (hR : 0<(D j I).radius)
    (hb : 0≤b) (hbw : b≤w) (hw1 : w≤1)
    (hs : ∀ i,‖fderiv ℝ ((D j I).selector i) (u j)‖≤
      (Cs/(D j I).width)*Real.sqrt ((D j I).selector i (u j)))
    (hr : ∀ i,‖fderiv ℝ ((D j I).residual i) (u j)‖≤
      Cr*((D j I).ell*(D j I).width)*Real.sqrt ((D j I).selector i (u j)))
    (hW : ∀ i : Fin ((D j I).n+1),|payloadValue D d (j+1) (child I i.val) u|≤δ*((D j I).ell*(D j I).width^2))
    (hglobal : b*((D j I).ell*(D j I).width)/2≤
      ‖fderiv ℝ ((D j I).localBase ρ w Rp) (u j)‖)
    (hactive : |(D j I).coordinates (u j) (Fin.last (D j I).n)|<(D j I).width/2 →
      w*((D j I).ell*(D j I).width)/2≤‖fderiv ℝ ((D j I).localBase ρ w Rp) (u j)‖) :
    b*((D j I).ell*(D j I).width)/4≤
      ‖fderiv ℝ (sliceObjective D (d+1) j I u ρ w Rp) (u j)‖ ∨
    ∃ i : Fin ((D j I).n+1),
      descentThreshold (Cr+Cs)<(D j I).selector i (u j) ∧
      (D (j+1) (child I i.val)).release (u (j+1))<1 ∧
      b*descentThreshold (Cr+Cs)≤w*(D j I).selector i (u j) ∧
      w*(D j I).selector i (u j)≤1 := by
  classical
  have hw : 0≤w := hb.trans hbw
  have hg : 0≤(D j I).ell*(D j I).width := mul_nonneg hell hh.le
  have hC : 0≤Cr+Cs := add_nonneg hCr hCs
  by_cases hex : ∃ i : Fin ((D j I).n+1),(D j I).selector i (u j)≠0
  · obtain ⟨i,hi⟩ := hex
    have hψ := (D j I).selector_range i (u j)
    have hQ := (D (j+1) (child I i.val)).release_range (u (j+1))
    by_cases hstop : (D j I).selector i (u j)≤descentThreshold (Cr+Cs) ∨
        1-releaseTolerance (Cr+Cs)≤(D (j+1) (child I i.val)).release (u (j+1))
    · left
      have hp := perturbation_norm_bound D d j I u (u j) hCs hCr hδ hell hh i hi (hs i) (hr i) (hW i)
      have hfactor := small_perturbation_factor hC hδ hδsmall hQ.1 hQ.2 hψ.1 hψ.2 hstop
      have hpert : ‖perturbation D d j I u (u j)‖≤((D j I).ell*(D j I).width)/4 := by
        have hmul := mul_le_mul_of_nonneg_left hfactor hg
        nlinarith only [hp,hmul]
      have hwp : ‖w • perturbation D d j I u (u j)‖≤w*((D j I).ell*(D j I).width)/4 := by
        rw [norm_smul w (perturbation D d j I u (u j)),Real.norm_eq_abs,abs_of_nonneg hw]
        have hh' := mul_le_mul_of_nonneg_left hpert hw
        nlinarith only [hh']
      have ha := hactive ((D j I).active_terminal_small hh i (u j) hi)
      have htri := norm_sub_le
        (fderiv ℝ ((D j I).localBase ρ w Rp) (u j)+w • perturbation D d j I u (u j))
        (w • perturbation D d j I u (u j))
      rw [add_sub_cancel_right] at htri
      rw [sliceObjective_succ_fderiv D d j I u hR]
      nlinarith only [ha,htri,hwp,mul_le_mul_of_nonneg_right hbw hg]
    · right
      push_neg at hstop
      refine ⟨i,hstop.1,?_,?_,?_⟩
      · have ht := (descentThreshold_range hC).2.2
        linarith only [hstop.2,ht]
      · exact (mul_le_mul_of_nonneg_right hbw (descentThreshold_range hC).1.le).trans
          (mul_le_mul_of_nonneg_left hstop.1.le hw)
      · exact mul_le_one₀ hw1 hψ.1 hψ.2
  · left
    have hinactive : ∀ i : Fin ((D j I).n+1),(D j I).selector i (u j)=0 := by simpa using hex
    rw [sliceObjective_succ_fderiv D d j I u hR,
      perturbation_zero_of_inactive D d j I u (u j) hinactive,smul_zero,add_zero]
    nlinarith only [hglobal,mul_nonneg hb hg]

end Bilevel.ChiRecursive
