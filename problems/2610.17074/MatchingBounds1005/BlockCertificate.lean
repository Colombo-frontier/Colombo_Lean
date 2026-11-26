import MatchingBounds1005.ScalarTransition
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Block residual identities and completion of squares

These are actual inner-product identities for the block quadratic and its
explicit gradient formula.  The inverse, self-adjointness and positivity of
the block operator are hypotheses, as in `ana:prop:block`. Identification of
the explicit formula with the derivative of the complete objective, and the
quantitative spectral estimates on the contraction vectors, are separate.
-/

noncomputable section
open scoped InnerProductSpace BigOperators

namespace MatchingBounds1005

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]

structure BlockGeometry where
  H : E →ₗ[ℝ] E
  Hinv : E →ₗ[ℝ] E
  inverse : ∀ x, H (Hinv x) = x
  symmetric : ∀ x y, ⟪x, H y⟫_ℝ = ⟪H x, y⟫_ℝ
  positive : ∀ x, 0 ≤ ⟪x, H x⟫_ℝ
  a : E
  e : E
  alpha_pos : 0 < ⟪a, Hinv e⟫_ℝ
  beta_pos : 0 < ⟪a, Hinv a⟫_ℝ

namespace BlockGeometry

variable {E} (G : BlockGeometry E)

def alpha : ℝ := ⟪G.a, G.Hinv G.e⟫_ℝ
def beta : ℝ := ⟪G.a, G.Hinv G.a⟫_ℝ
def rho : ℝ := ⟪G.e, G.Hinv G.e⟫_ℝ
def lam : ℝ := G.alpha⁻¹
def tau : ℝ := G.beta⁻¹
def kappa : ℝ := G.rho / G.alpha ^ 2
def wOut : E := G.beta⁻¹ • G.Hinv G.a
def wIn : E := G.Hinv G.e - (G.alpha / G.beta) • G.Hinv G.a

theorem alpha_ne : G.alpha ≠ 0 := ne_of_gt G.alpha_pos
theorem beta_ne : G.beta ≠ 0 := ne_of_gt G.beta_pos

theorem lam_mul_alpha : G.lam * G.alpha = 1 := inv_mul_cancel₀ G.alpha_ne

theorem lam_alpha_div_beta : G.lam * (G.alpha / G.beta) = G.tau := by
  rw [div_eq_mul_inv, ← mul_assoc, G.lam_mul_alpha, one_mul]
  rfl

theorem lam_sq_rho : G.lam ^ 2 * G.rho = G.kappa := by
  simp [lam, kappa, div_eq_mul_inv, inv_pow, mul_comm]

theorem normalization_cancellation :
    G.lam * (G.lam * (G.rho - G.alpha ^ 2 / G.beta)) = G.kappa - G.tau := by
  calc
    _ = G.lam ^ 2 * G.rho - (G.lam * G.alpha) ^ 2 / G.beta := by ring
    _ = G.kappa - G.tau := by rw [G.lam_sq_rho, G.lam_mul_alpha]; simp [tau]

theorem inv_inner_H (x y : E) : ⟪G.Hinv x, G.H y⟫_ℝ = ⟪x, y⟫_ℝ := by
  rw [G.symmetric, G.inverse]

theorem inv_symmetric (x y : E) : ⟪G.Hinv x, y⟫_ℝ = ⟪x, G.Hinv y⟫_ℝ := by
  conv_lhs => rw [← G.inverse y]
  rw [G.inv_inner_H]

theorem wOut_inner_H (z : E) : ⟪G.wOut, G.H z⟫_ℝ = G.tau * ⟪G.a, z⟫_ℝ := by
  simp [wOut, tau, real_inner_smul_left, G.inv_inner_H]

theorem wOut_inner_a : ⟪G.wOut, G.a⟫_ℝ = 1 := by
  rw [wOut, real_inner_smul_left, G.inv_symmetric]
  change G.beta⁻¹ * G.beta = 1
  exact inv_mul_cancel₀ G.beta_ne

theorem wOut_inner_e : ⟪G.wOut, G.e⟫_ℝ = G.alpha / G.beta := by
  rw [wOut, real_inner_smul_left, G.inv_symmetric]
  change G.beta⁻¹ * G.alpha = G.alpha / G.beta
  ring

theorem wIn_inner_H (z : E) :
    ⟪G.wIn, G.H z⟫_ℝ = ⟪G.e, z⟫_ℝ - G.alpha / G.beta * ⟪G.a, z⟫_ℝ := by
  simp [wIn, inner_sub_left, real_inner_smul_left, G.inv_inner_H]

theorem wIn_inner_a : ⟪G.wIn, G.a⟫_ℝ = 0 := by
  simp only [wIn, inner_sub_left, real_inner_smul_left, G.inv_symmetric]
  rw [real_inner_comm (G.Hinv G.a) G.e, G.inv_symmetric]
  change G.alpha - G.alpha / G.beta * G.beta = 0
  field_simp [G.beta_ne]

theorem wIn_inner_e : ⟪G.wIn, G.e⟫_ℝ = G.rho - G.alpha ^ 2 / G.beta := by
  simp only [wIn, inner_sub_left, real_inner_smul_left, G.inv_symmetric]
  change G.rho - G.alpha / G.beta * G.alpha = G.rho - G.alpha ^ 2 / G.beta
  ring

/-- `vNext` is the scalar entry readout of the next block; use zero at the end. -/
def gradientBlock (ψ : ℝ → ℝ) (uPrev : ℝ) (z : E) (vNext : ℝ) : E :=
  G.H z - (G.lam * uPrev) • G.e +
    (G.kappa * ⟪G.a, z⟫_ℝ + G.tau * ψ ⟪G.a, z⟫_ℝ - G.lam * vNext) • G.a

theorem residual_identity (ψ : ℝ → ℝ) (uPrev : ℝ) (z zNext : E) (vNextNext : ℝ) :
    ⟪G.wOut, G.gradientBlock ψ uPrev z ⟪G.e, zNext⟫_ℝ⟫_ℝ +
      G.lam * ⟪G.wIn, G.gradientBlock ψ ⟪G.a, z⟫_ℝ zNext vNextNext⟫_ℝ =
    G.tau * (2 * ⟪G.a, z⟫_ℝ - uPrev - ⟪G.a, zNext⟫_ℝ + ψ ⟪G.a, z⟫_ℝ) := by
  simp only [gradientBlock, inner_add_right, inner_sub_right, real_inner_smul_right,
    G.wOut_inner_H, G.wOut_inner_e, G.wOut_inner_a,
    G.wIn_inner_H, G.wIn_inner_e, G.wIn_inner_a]
  linear_combination -uPrev * G.lam_alpha_div_beta -
    ⟪G.a, zNext⟫_ℝ * G.lam_alpha_div_beta -
    ⟪G.a, z⟫_ℝ * G.normalization_cancellation

/-- The boundary correction in the manuscript is retained exactly. -/
theorem terminal_residual_identity (ψ : ℝ → ℝ) (uPrev : ℝ) (z : E) :
    ⟪G.wOut, G.gradientBlock ψ uPrev z 0⟫_ℝ =
    G.tau * (2 * ⟪G.a, z⟫_ℝ - uPrev + ψ ⟪G.a, z⟫_ℝ) +
      (G.kappa - G.tau) * ⟪G.a, z⟫_ℝ := by
  simp only [gradientBlock, inner_add_right, inner_sub_right, real_inner_smul_right,
    G.wOut_inner_H, G.wOut_inner_e, G.wOut_inner_a]
  linear_combination -uPrev * G.lam_alpha_div_beta

theorem terminal_zero_readout (ψ : ℝ → ℝ) (uPrev : ℝ) (z : E)
    (hz : ⟪G.a, z⟫_ℝ = 0) :
    ⟪G.wOut, G.gradientBlock ψ uPrev z 0⟫_ℝ = G.tau * (-uPrev + ψ 0) := by
  rw [G.terminal_residual_identity, hz]
  ring

def quadraticBlock (uPrev : ℝ) (z : E) : ℝ :=
  (1 / 2 : ℝ) * ⟪z, G.H z⟫_ℝ - G.lam * uPrev * ⟪G.e, z⟫_ℝ +
    (G.kappa / 2) * ⟪G.a, z⟫_ℝ ^ 2

theorem completing_square (uPrev : ℝ) (z : E) :
    G.quadraticBlock uPrev z =
      (1 / 2 : ℝ) * ⟪z - (G.lam * uPrev) • G.Hinv G.e,
        G.H (z - (G.lam * uPrev) • G.Hinv G.e)⟫_ℝ +
      G.kappa / 2 * (⟪G.a, z⟫_ℝ ^ 2 - uPrev ^ 2) := by
  simp only [quadraticBlock, map_sub, map_smul, G.inverse,
    inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
    G.inv_inner_H, G.inv_symmetric]
  rw [real_inner_comm z G.e]
  rw [← G.lam_sq_rho]
  simp only [rho]
  ring

theorem quadraticBlock_lower (uPrev : ℝ) (z : E) :
    G.kappa / 2 * (⟪G.a, z⟫_ℝ ^ 2 - uPrev ^ 2) ≤ G.quadraticBlock uPrev z := by
  rw [G.completing_square]
  have h := G.positive (z - (G.lam * uPrev) • G.Hinv G.e)
  linarith

theorem rho_nonneg : 0 ≤ G.rho := by
  have h := G.positive (G.Hinv G.e)
  rw [G.inverse, G.inv_symmetric] at h
  exact h

theorem kappa_nonneg : 0 ≤ G.kappa :=
  div_nonneg G.rho_nonneg (sq_nonneg _)

theorem tau_nonneg : 0 ≤ G.tau := inv_nonneg.mpr G.beta_pos.le

theorem lam_nonneg : 0 ≤ G.lam := inv_nonneg.mpr G.alpha_pos.le

def quadraticChain (N : ℕ) (u : ℕ → ℝ) (z : ℕ → E) : ℝ :=
  ∑ i ∈ Finset.range N, G.quadraticBlock (u i) (z (i + 1))

/-- Completing squares telescopes; the terminal readout square is preserved. -/
theorem quadraticChain_lower (N : ℕ) (u : ℕ → ℝ) (z : ℕ → E)
    (hread : ∀ i < N, u (i + 1) = ⟪G.a, z (i + 1)⟫_ℝ) :
    G.kappa / 2 * ((u N) ^ 2 - (u 0) ^ 2) ≤ G.quadraticChain N u z := by
  calc
    _ = ∑ i ∈ Finset.range N, G.kappa / 2 * ((u (i + 1)) ^ 2 - (u i) ^ 2) := by
      rw [← Finset.mul_sum, Finset.sum_range_sub (fun i => u i ^ 2)]
    _ ≤ G.quadraticChain N u z := by
      apply Finset.sum_le_sum
      intro i hi
      rw [hread i (Finset.mem_range.mp hi)]
      exact G.quadraticBlock_lower (u i) (z (i + 1))

theorem quadraticChain_lower_boundary (N : ℕ) (u : ℕ → ℝ) (z : ℕ → E)
    (hread : ∀ i < N, u (i + 1) = ⟪G.a, z (i + 1)⟫_ℝ) (hu0 : u 0 = 1) :
    -G.kappa / 2 ≤ G.quadraticChain N u z := by
  have h := G.quadraticChain_lower N u z hread
  rw [hu0] at h
  have hpos := mul_nonneg G.kappa_nonneg (sq_nonneg (u N))
  nlinarith

def chainEnergy (φ : ℝ → ℝ) (N : ℕ) (u : ℕ → ℝ) (z : ℕ → E) : ℝ :=
  G.quadraticChain N u z + G.tau * ∑ i ∈ Finset.range N, φ ⟪G.a, z (i + 1)⟫_ℝ

theorem chainEnergy_lower (φ : ℝ → ℝ) (hφ : ∀ t, 0 ≤ φ t)
    (N : ℕ) (u : ℕ → ℝ) (z : ℕ → E)
    (hread : ∀ i < N, u (i + 1) = ⟪G.a, z (i + 1)⟫_ℝ) (hu0 : u 0 = 1) :
    -G.kappa / 2 ≤ G.chainEnergy φ N u z := by
  have hquad := G.quadraticChain_lower_boundary N u z hread hu0
  have hsum : 0 ≤ ∑ i ∈ Finset.range N, φ ⟪G.a, z (i + 1)⟫_ℝ :=
    Finset.sum_nonneg (fun _ _ => hφ _)
  have hnoise := mul_nonneg G.tau_nonneg hsum
  unfold chainEnergy
  linarith

theorem chainEnergy_zero (φ : ℝ → ℝ) (N : ℕ) (u : ℕ → ℝ) :
    G.chainEnergy φ N u (fun _ => 0) = N * G.tau * φ 0 := by
  simp [chainEnergy, quadraticChain, quadraticBlock]
  ring

/-- Pairwise gap bound, prior to converting the infimum formulation. -/
theorem chainEnergy_gap (φ : ℝ → ℝ) (hφ : ∀ t, 0 ≤ φ t)
    (hφ0 : φ 0 = 10) (N : ℕ) (u : ℕ → ℝ) (z : ℕ → E)
    (hread : ∀ i < N, u (i + 1) = ⟪G.a, z (i + 1)⟫_ℝ) (hu0 : u 0 = 1) :
    G.chainEnergy φ N u (fun _ => 0) - G.chainEnergy φ N u z ≤
      10 * N * G.tau + G.kappa / 2 := by
  rw [G.chainEnergy_zero, hφ0]
  have h := G.chainEnergy_lower φ hφ N u z hread hu0
  linarith

theorem contraction_bound (g h : E) (B : ℝ) (hg : ‖g‖ ≤ B) (hh : ‖h‖ ≤ B) :
    |⟪G.wOut, g⟫_ℝ + G.lam * ⟪G.wIn, h⟫_ℝ| ≤
      (‖G.wOut‖ + G.lam * ‖G.wIn‖) * B := by
  calc
    _ ≤ |⟪G.wOut, g⟫_ℝ| + |G.lam * ⟪G.wIn, h⟫_ℝ| := abs_add _ _
    _ = |⟪G.wOut, g⟫_ℝ| + G.lam * |⟪G.wIn, h⟫_ℝ| := by
      rw [abs_mul, abs_of_nonneg G.lam_nonneg]
    _ ≤ ‖G.wOut‖ * ‖g‖ + G.lam * (‖G.wIn‖ * ‖h‖) :=
      add_le_add (abs_real_inner_le_norm _ _)
        (mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) G.lam_nonneg)
    _ ≤ ‖G.wOut‖ * B + G.lam * (‖G.wIn‖ * B) :=
      add_le_add (mul_le_mul_of_nonneg_left hg (norm_nonneg _))
        (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hh (norm_nonneg _)) G.lam_nonneg)
    _ = _ := by ring

theorem residual_bound (ψ : ℝ → ℝ) (uPrev : ℝ) (z zNext : E) (vNextNext B : ℝ)
    (hg : ‖G.gradientBlock ψ uPrev z ⟪G.e, zNext⟫_ℝ‖ ≤ B)
    (hh : ‖G.gradientBlock ψ ⟪G.a, z⟫_ℝ zNext vNextNext‖ ≤ B) :
    G.tau * |2 * ⟪G.a, z⟫_ℝ - uPrev - ⟪G.a, zNext⟫_ℝ + ψ ⟪G.a, z⟫_ℝ| ≤
      (‖G.wOut‖ + G.lam * ‖G.wIn‖) * B := by
  have h := G.contraction_bound _ _ B hg hh
  rw [G.residual_identity, abs_mul, abs_of_nonneg G.tau_nonneg] at h
  exact h

/-- The output contraction vector estimate, before taking square roots. -/
theorem wOut_coercive_bound (γ : ℝ)
    (hcoercive : ∀ x, γ * ‖x‖ ^ 2 ≤ ⟪x, G.H x⟫_ℝ) :
    γ * ‖G.wOut‖ ^ 2 ≤ G.tau := by
  have h := hcoercive G.wOut
  have hH : G.H G.wOut = G.beta⁻¹ • G.a := by
    simp only [wOut, map_smul, G.inverse]
  rw [hH, real_inner_smul_right, G.wOut_inner_a, mul_one] at h
  exact h

/-- The input contraction vector estimate, before taking square roots. -/
theorem wIn_coercive_bound (γ : ℝ)
    (hcoercive : ∀ x, γ * ‖x‖ ^ 2 ≤ ⟪x, G.H x⟫_ℝ) :
    γ * ‖G.wIn‖ ^ 2 ≤ G.rho := by
  have h := hcoercive G.wIn
  have hH : G.H G.wIn = G.e - (G.alpha / G.beta) • G.a := by
    simp only [wIn, map_sub, map_smul, G.inverse]
  rw [hH, inner_sub_right, real_inner_smul_right,
    G.wIn_inner_a, G.wIn_inner_e, mul_zero, sub_zero] at h
  have hnonneg : 0 ≤ G.alpha ^ 2 / G.beta :=
    div_nonneg (sq_nonneg _) G.beta_pos.le
  linarith

end BlockGeometry
end MatchingBounds1005
