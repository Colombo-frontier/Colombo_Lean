import Bilevel.ChiRecursivePayload

/-! Dimension- and depth-independent bounds for the actual recursive payload.
The hypotheses concern the local constructed nodes, never the recursively
defined payload being bounded. -/
noncomputable section
open scoped BigOperators
namespace Bilevel.ChiRecursive
open ChiBoundedChain

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem Node.release_range (D : Node E) (u : E) : 0≤D.release u ∧ D.release u≤1 :=
  ⟨Real.smoothTransition.nonneg _,Real.smoothTransition.le_one _⟩

theorem Node.sum_abs_residual_bound (D : Node E) (hD : 0≤D.ell) (u : E) :
    ∑ i : Fin (D.n+1),|D.residual i u|≤gaussianBound*(D.ell*D.width^2) := by
  have he : (∑ i : Fin (D.n+1),|D.residual i u|)=
      D.ell*D.width^2*|ChiBoundedChain.residual D.n (D.width⁻¹ • D.coordinates u)| := by
    have hs : (∑ i : Fin (D.n+1),|D.residual i u|)=-(∑ i : Fin (D.n+1),D.residual i u) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i _
      exact abs_of_nonpos (D.residual_nonpos hD i u)
    rw [hs]
    simp only [Node.residual,← R_eq_sum,R,ZeroChainResidualScaled.scaled,
      abs_of_nonpos (ChiBoundedChain.residual_nonpos _ _)]
    ring
  rw [he]
  have hh := mul_le_mul_of_nonneg_left (residual_abs_bound D.n (D.width⁻¹ • D.coordinates u))
    (show 0≤D.ell*D.width^2 by positivity)
  simpa only [gaussianBound,mul_comm] using hh

theorem payloadValue_succ_rewrite (D : Geometry E) (d j : ℕ) (I : List ℕ) (u : ℕ → E) :
    payloadValue D (d+1) j I u=(D j I).H (u j)+
      (∑ i : Fin ((D j I).n+1),(D j I).residual i (u j)*
        ((D (j+1) (child I i.val)).release (u (j+1))-1))+
      ∑ i : Fin ((D j I).n+1),(D j I).selector i (u j)*
        payloadValue D d (j+1) (child I i.val) u := by
  simp only [payloadValue,mul_sub,mul_one,Finset.sum_sub_distrib]
  ring

theorem release_correction_abs_bound (D : Geometry E) (j : ℕ) (I : List ℕ) (u : ℕ → E) :
    |∑ i : Fin ((D j I).n+1),(D j I).residual i (u j)*
      ((D (j+1) (child I i.val)).release (u (j+1))-1)|≤
      ∑ i : Fin ((D j I).n+1),|(D j I).residual i (u j)| := by
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro i _
  rw [abs_mul]
  have hq := (D (j+1) (child I i.val)).release_range (u (j+1))
  have ha : |(D (j+1) (child I i.val)).release (u (j+1))-1|≤1 := by
    apply abs_le.mpr
    constructor <;> linarith only [hq.1,hq.2]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left ha (abs_nonneg ((D j I).residual i (u j)))

theorem selected_payload_abs_bound (D : Geometry E) (d j : ℕ) (I : List ℕ) (u : ℕ → E)
    {M : ℝ} (hM : 0≤M)
    (hb : ∀ i : Fin ((D j I).n+1),|payloadValue D d (j+1) (child I i.val) u|≤M) :
    |∑ i : Fin ((D j I).n+1),(D j I).selector i (u j)*
      payloadValue D d (j+1) (child I i.val) u|≤M := by
  calc
    _ ≤ ∑ i : Fin ((D j I).n+1),|(D j I).selector i (u j)*payloadValue D d (j+1) (child I i.val) u| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin ((D j I).n+1),(D j I).selector i (u j)*M := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul,abs_of_nonneg ((D j I).selector_range i (u j)).1]
      exact mul_le_mul_of_nonneg_left (hb i) ((D j I).selector_range i (u j)).1
    _ = (∑ i : Fin ((D j I).n+1),(D j I).selector i (u j))*M := (Finset.sum_mul ..).symm
    _ ≤ M := by nlinarith [(D j I).selector_sum_le_one (u j)]

/-- The small payload constant does not shrink with depth. The leaf is
centered and every internal release correction is bounded using the actual
nonpositive residual and actual unit-range release gates. -/
theorem payloadValue_uniform_bound (D : Geometry E) (energy : ℕ → ℝ)
    {δ δ₀ C : ℝ} (hδ : 0≤δ) (_hδ₀ : 0≤δ₀) (hleaf : 2*δ₀≤δ)
    (he : ∀ j,0≤energy j) (hell : ∀ j I,0≤(D j I).ell)
    (hH : ∀ j I u,|(D j I).H u|≤δ₀*energy j)
    (hR : ∀ j I,gaussianBound*((D j I).ell*(D j I).width^2)≤C*energy (j+1))
    (hscale : ∀ j,δ₀*energy j+(C+δ)*energy (j+1)≤δ*energy j)
    (d j : ℕ) (I : List ℕ) (u : ℕ → E) :
    |payloadValue D d j I u|≤δ*energy j := by
  induction d generalizing j I with
  | zero =>
    have ha : |(D j I).H (u j)-(D j I).H 0|≤|(D j I).H (u j)|+|(D j I).H 0| := by
      simpa only [sub_zero,zero_sub,abs_neg] using abs_sub_le ((D j I).H (u j)) 0 ((D j I).H 0)
    exact ha.trans ((add_le_add (hH j I (u j)) (hH j I 0)).trans (by
      nlinarith only [mul_le_mul_of_nonneg_right hleaf (he j)]))
  | succ d ih =>
    rw [payloadValue_succ_rewrite]
    have hcor := (release_correction_abs_bound D j I u).trans
      (((D j I).sum_abs_residual_bound (hell j I) (u j)).trans (hR j I))
    have hsel := selected_payload_abs_bound D d j I u (mul_nonneg hδ (he (j+1)))
      (fun i => ih (j+1) (child I i.val))
    have ha := abs_add ((D j I).H (u j))
      (∑ i : Fin ((D j I).n+1),(D j I).residual i (u j)*
        ((D (j+1) (child I i.val)).release (u (j+1))-1))
    have hb := abs_add ((D j I).H (u j)+
      ∑ i : Fin ((D j I).n+1),(D j I).residual i (u j)*
        ((D (j+1) (child I i.val)).release (u (j+1))-1))
      (∑ i : Fin ((D j I).n+1),(D j I).selector i (u j)*payloadValue D d (j+1) (child I i.val) u)
    nlinarith only [ha,hb,hcor,hsel,hH j I (u j),hscale j]

end Bilevel.ChiRecursive
