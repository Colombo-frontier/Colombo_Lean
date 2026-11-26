import Bilevel.ChiRecursiveSlice
import Bilevel.ChiRecursiveValue

/-! The source perturbation estimate for the actual unique active child.
The bound is independent of depth and the number of inactive children. -/
noncomputable section
namespace Bilevel.ChiRecursive
open ChiBoundedChain

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem Node.active_terminal_small (D : Node E) (hh : 0<D.width)
    (i : Fin (D.n+1)) (v : E) (hi : D.selector i v≠0) :
    |D.coordinates v (Fin.last D.n)|<D.width/2 := by
  have ht := selector_active_tail_small i (D.width⁻¹ • D.coordinates v) hi (Fin.last D.n) (Fin.le_last i)
  change |D.width⁻¹*(D.coordinates v (Fin.last D.n))|<1/2 at ht
  rw [← div_eq_inv_mul,abs_div,abs_of_pos hh] at ht
  have hh' := (div_lt_iff₀ hh).mp ht
  linarith only [hh']

theorem perturbation_norm_bound (D : Geometry E) (d j : ℕ) (I : List ℕ) (u : ℕ → E) (v : E)
    {Cs Cr δ : ℝ} (hCs : 0≤Cs) (hCr : 0≤Cr) (hδ : 0≤δ)
    (hell : 0≤(D j I).ell) (hh : 0<(D j I).width)
    (i : Fin ((D j I).n+1)) (hi : (D j I).selector i v≠0)
    (hs : ‖fderiv ℝ ((D j I).selector i) v‖≤
      (Cs/(D j I).width)*Real.sqrt ((D j I).selector i v))
    (hr : ‖fderiv ℝ ((D j I).residual i) v‖≤
      Cr*((D j I).ell*(D j I).width)*Real.sqrt ((D j I).selector i v))
    (hW : |payloadValue D d (j+1) (child I i.val) u|≤δ*((D j I).ell*(D j I).width^2)) :
    ‖perturbation D d j I u v‖≤(Cr+Cs)*((D j I).ell*(D j I).width)*
      ((1-(D (j+1) (child I i.val)).release (u (j+1)))+δ)*Real.sqrt ((D j I).selector i v) := by
  let Q := (D (j+1) (child I i.val)).release (u (j+1))
  let s := Real.sqrt ((D j I).selector i v)
  let g := (D j I).ell*(D j I).width
  have hQ : 0≤Q ∧ Q≤1 := (D (j+1) (child I i.val)).release_range (u (j+1))
  have hQsub : 0≤1-Q := by linarith only [hQ.2]
  have hs0 : 0≤s := Real.sqrt_nonneg _
  have hg0 : 0≤g := mul_nonneg hell hh.le
  rw [perturbation_eq_active D d j I u v i hi]
  have h₁ : ‖(Q-1) • fderiv ℝ ((D j I).residual i) v‖≤(1-Q)*(Cr*g*s) := by
    rw [norm_smul (Q-1) (fderiv ℝ ((D j I).residual i) v),Real.norm_eq_abs,
      abs_of_nonpos (by linarith only [hQ.2])]
    convert mul_le_mul_of_nonneg_left hr (show 0≤1-Q by linarith only [hQ.2]) using 1
    ring
  have h₂ : ‖payloadValue D d (j+1) (child I i.val) u • fderiv ℝ ((D j I).selector i) v‖≤Cs*δ*g*s := by
    rw [norm_smul (payloadValue D d (j+1) (child I i.val) u) (fderiv ℝ ((D j I).selector i) v),Real.norm_eq_abs]
    calc
      _ ≤ (δ*((D j I).ell*(D j I).width^2))*((Cs/(D j I).width)*s) :=
        mul_le_mul hW hs (norm_nonneg _) (by positivity)
      _ = _ := by dsimp only [g];field_simp;ring
  have hn := norm_add_le ((Q-1) • fderiv ℝ ((D j I).residual i) v)
    (payloadValue D d (j+1) (child I i.val) u • fderiv ℝ ((D j I).selector i) v)
  change ‖(Q-1) • fderiv ℝ ((D j I).residual i) v+
    payloadValue D d (j+1) (child I i.val) u • fderiv ℝ ((D j I).selector i) v‖≤(Cr+Cs)*g*((1-Q)+δ)*s
  have hextra : 0≤Cr*δ*g*s+Cs*(1-Q)*g*s := by positivity
  nlinarith only [hn,h₁,h₂,hextra]

def descentThreshold (C : ℝ) : ℝ := (1/(8*(C+1)))^2
def releaseTolerance (C : ℝ) : ℝ := 1/(16*(C+1))

theorem descentThreshold_range {C : ℝ} (hC : 0≤C) :
    0<descentThreshold C ∧ descentThreshold C<1 ∧ 0<releaseTolerance C := by
  have hc : 0<C+1 := by linarith
  have ht : 0<1/(8*(C+1)) := by positivity
  have ht1 : 1/(8*(C+1))<1 := (div_lt_one (by positivity)).mpr (by linarith)
  unfold descentThreshold releaseTolerance
  exact ⟨by positivity,by nlinarith,by positivity⟩

/-- The same fixed selector threshold and release tolerance work at all depths. -/
theorem small_perturbation_factor {C δ Q ψ : ℝ} (hC : 0≤C) (hδ : 0≤δ)
    (hδsmall : δ≤releaseTolerance C) (hQ0 : 0≤Q) (hQ1 : Q≤1) (_hψ0 : 0≤ψ) (hψ1 : ψ≤1)
    (hstop : ψ≤descentThreshold C ∨ 1-releaseTolerance C≤Q) :
    C*((1-Q)+δ)*Real.sqrt ψ≤1/4 := by
  have hc : 0<C+1 := by linarith
  have hdpos : 0<16*(C+1) := by positivity
  have hδ1 : δ≤1 := hδsmall.trans ((div_le_one hdpos).mpr (by linarith))
  have hs0 := Real.sqrt_nonneg ψ
  have hs1 : Real.sqrt ψ≤1 := (Real.sqrt_le_iff).mpr ⟨by norm_num,by simpa using hψ1⟩
  have hfac : 0≤(1-Q)+δ := by linarith
  rcases hstop with hstop|hstop
  · have hs : Real.sqrt ψ≤1/(8*(C+1)) := by
      have hh := Real.sqrt_le_sqrt hstop
      simpa only [descentThreshold,Real.sqrt_sq (show 0≤1/(8*(C+1)) by positivity)] using hh
    have hfac2 : (1-Q)+δ≤2 := by linarith
    have hh : C*((1-Q)+δ)*Real.sqrt ψ≤2*C*(1/(8*(C+1))) := by
      have hh' := mul_le_mul (mul_le_mul_of_nonneg_left hfac2 hC) hs hs0 (show 0≤C*2 by positivity)
      nlinarith only [hh']
    apply hh.trans
    rw [mul_one_div]
    apply (div_le_iff₀ (show 0<8*(C+1) by positivity)).mpr
    linarith
  · have hsmall : (1-Q)+δ≤2*releaseTolerance C := by linarith
    have ht : 0≤releaseTolerance C := by unfold releaseTolerance;positivity
    have hh : C*((1-Q)+δ)*Real.sqrt ψ≤C*(2*releaseTolerance C)*1 :=
      mul_le_mul (mul_le_mul_of_nonneg_left hsmall hC) hs1 hs0 (by positivity)
    apply hh.trans
    unfold releaseTolerance
    rw [mul_one]
    calc
      _ = (2*C)/(16*(C+1)) := by ring
      _ ≤ 1/4 := (div_le_iff₀ hdpos).mpr (by linarith)

end Bilevel.ChiRecursive
