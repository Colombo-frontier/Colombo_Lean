import Mathlib.Analysis.NormedSpace.OperatorNorm.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic

/-!
# Deterministic refinement and inexact power iteration

These are the deterministic estimates underlying `lem:refinement` and
`lem:inverse-power` in `matvec.tex`. Successful correction/application bounds
are explicit hypotheses. No probabilistic success guarantee is asserted here.
-/

namespace Matvec

section Refinement

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Residual consistency is preserved by the actual refinement updates. -/
theorem refinement_residual_identity (H : E →L[ℝ] E) (b : E)
    (x r correction : ℕ → E) (hx0 : x 0 = 0) (hr0 : r 0 = b)
    (hx : ∀ n, x (n + 1) = x n + correction n)
    (hr : ∀ n, r (n + 1) = r n - H (correction n)) :
    ∀ n, r n = b - H (x n) := by
  intro n
  induction n with
  | zero => simp [hx0, hr0]
  | succ n ih => rw [hr, hx, map_add, ih]; abel

omit [NormedSpace ℝ E] in
/-- A successful correction contracts the residual, so repeated successful
corrections have a geometric residual bound. -/
theorem residual_geometric_bound (r : ℕ → E) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (hstep : ∀ n, ‖r (n + 1)‖ ≤ ρ * ‖r n‖) :
    ∀ n, ‖r n‖ ≤ ρ ^ n * ‖r 0‖ := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      ‖r (n + 1)‖ ≤ ρ * ‖r n‖ := hstep n
      _ ≤ ρ * (ρ ^ n * ‖r 0‖) := mul_le_mul_of_nonneg_left ih hρ
      _ = ρ ^ (n + 1) * ‖r 0‖ := by ring

omit [NormedSpace ℝ E] in
/-- Finite-horizon form: only the corrections actually used must succeed. -/
theorem residual_geometric_bound_at (r : ℕ → E) (ρ : ℝ) (hρ : 0 ≤ ρ)
    (J : ℕ) (hstep : ∀ n < J, ‖r (n + 1)‖ ≤ ρ * ‖r n‖) :
    ‖r J‖ ≤ ρ ^ J * ‖r 0‖ := by
  have aux : ∀ n ≤ J, ‖r n‖ ≤ ρ ^ n * ‖r 0‖ := by
    intro n
    induction n with
    | zero => intro _; simp
    | succ n ih =>
      intro hn
      calc
        ‖r (n + 1)‖ ≤ ρ * ‖r n‖ := hstep n (by omega)
        _ ≤ ρ * (ρ ^ n * ‖r 0‖) :=
          mul_le_mul_of_nonneg_left (ih (by omega)) hρ
        _ = ρ ^ (n + 1) * ‖r 0‖ := by ring
  exact aux J le_rfl

/-- Exact error identity for an inverse and a consistent residual. -/
theorem refinement_inverse_error_identity (H M : E →L[ℝ] E)
    (hinverse : ∀ x, M (H x) = x) (b x r : E)
    (hresidual : r = b - H x) : x - M b = -M r := by
  rw [hresidual, map_sub, hinverse]
  abel

/-- Refinement converts the residual bound into the relative inverse-application
error used in the manuscript. `hJ` records the required number of corrections. -/
theorem refinement_inverse_error_bound (H M : E →L[ℝ] E)
    (hinverse : ∀ x, M (H x) = x) (b : E)
    (x r correction : ℕ → E) (hx0 : x 0 = 0) (hr0 : r 0 = b)
    (hx : ∀ n, x (n + 1) = x n + correction n)
    (hr : ∀ n, r (n + 1) = r n - H (correction n))
    (J : ℕ)
    (hsuccess : ∀ n < J, ‖H (correction n) - r n‖ ≤ (1 / 2 : ℝ) * ‖r n‖)
    (η : ℝ) (hJ : (1 / 2 : ℝ) ^ J ≤ η) :
    ‖x J - M b‖ ≤ η * ‖M‖ * ‖b‖ := by
  have hres := refinement_residual_identity H b x r correction hx0 hr0 hx hr J
  have hstep : ∀ n < J, ‖r (n + 1)‖ ≤ (1 / 2 : ℝ) * ‖r n‖ := by
    intro n hn
    rw [hr, norm_sub_rev]
    exact hsuccess n hn
  have hgeom := residual_geometric_bound_at r (1 / 2) (by norm_num) J hstep
  rw [hr0] at hgeom
  rw [refinement_inverse_error_identity H M hinverse b (x J) (r J) hres,
    norm_neg]
  calc
    ‖M (r J)‖ ≤ ‖M‖ * ‖r J‖ := M.le_opNorm _
    _ ≤ ‖M‖ * ((1 / 2 : ℝ) ^ J * ‖b‖) :=
      mul_le_mul_of_nonneg_left hgeom (norm_nonneg _)
    _ ≤ ‖M‖ * (η * ‖b‖) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hJ (norm_nonneg _)) (norm_nonneg _)
    _ = η * ‖M‖ * ‖b‖ := by ring

end Refinement

section Power

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Exact, unnormalized power iteration. -/
def exactPower (M : E →L[ℝ] E) (g : E) : ℕ → E
  | 0 => g
  | n + 1 => M (exactPower M g n)

theorem exactPower_norm_le (M : E →L[ℝ] E) (g : E) (L : ℝ)
    (hL : 0 ≤ L) (hM : ‖M‖ ≤ L) (hg : ‖g‖ ≤ 1) :
    ∀ n, ‖exactPower M g n‖ ≤ L ^ n := by
  intro n
  induction n with
  | zero => simpa [exactPower] using hg
  | succ n ih =>
    calc
      ‖exactPower M g (n + 1)‖ ≤ ‖M‖ * ‖exactPower M g n‖ := M.le_opNorm _
      _ ≤ L * ‖exactPower M g n‖ :=
        mul_le_mul_of_nonneg_right hM (norm_nonneg _)
      _ ≤ L * L ^ n := mul_le_mul_of_nonneg_left ih hL
      _ = L ^ (n + 1) := by ring

/-- The scalar recurrence controlling inexact power iteration. -/
theorem power_error_recurrence_bound (e : ℕ → ℝ) (L η : ℝ)
    (hL : 0 ≤ L) (hη : 0 ≤ η) (hzero : e 0 ≤ 0)
    (hstep : ∀ n, e (n + 1) ≤ η * L ^ (n + 1) + (1 + η) * L * e n) :
    ∀ n, e n ≤ ((1 + η) ^ n - 1) * L ^ n := by
  intro n
  induction n with
  | zero => simpa using hzero
  | succ n ih =>
    calc
      e (n + 1) ≤ η * L ^ (n + 1) + (1 + η) * L * e n := hstep n
      _ ≤ η * L ^ (n + 1) + (1 + η) * L * (((1 + η) ^ n - 1) * L ^ n) :=
        add_le_add_left (mul_le_mul_of_nonneg_left ih (by positivity)) _
      _ = ((1 + η) ^ (n + 1) - 1) * L ^ (n + 1) := by ring

/-- Elementary rational upper bound for the multiplicative error growth. -/
theorem power_error_denominator_bound (η : ℝ) (hη : 0 ≤ η) :
    ∀ n : ℕ, (1 + η) ^ n * (1 - (n : ℝ) * η) ≤ 1 := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      (1 + η) ^ (n + 1) * (1 - ((n + 1 : ℕ) : ℝ) * η)
          = (1 + η) ^ n * (1 - (n : ℝ) * η) -
            (1 + η) ^ n * ((n : ℝ) + 1) * η ^ 2 := by
              simp only [Nat.cast_add, Nat.cast_one, pow_succ]
              ring
      _ ≤ (1 + η) ^ n * (1 - (n : ℝ) * η) := sub_le_self _ (by positivity)
      _ ≤ 1 := ih

/-- The manuscript can choose its universal error constant so that `q * η ≤ 1/2`.
Under this explicit condition the error growth is at most `2 * q * η`. -/
theorem power_error_growth_le (η : ℝ) (hη : 0 ≤ η) (q : ℕ)
    (hsmall : (q : ℝ) * η ≤ 1 / 2) :
    (1 + η) ^ q - 1 ≤ 2 * (q : ℝ) * η := by
  have hden := power_error_denominator_bound η hη q
  have hpow : 1 ≤ (1 + η) ^ q := one_le_pow₀ (by linarith)
  have hprod := mul_nonneg (sub_nonneg.mpr hpow)
    (show 0 ≤ 1 / 2 - (q : ℝ) * η by linarith)
  nlinarith

/-- Actual approximate inverse applications satisfy the manuscript's error
bound, without spectral or probabilistic assumptions. -/
theorem inexactPower_error_bound (M : E →L[ℝ] E) (g : E) (z : ℕ → E)
    (L η : ℝ) (hL : 0 ≤ L) (hη : 0 ≤ η) (hM : ‖M‖ ≤ L)
    (hg : ‖g‖ ≤ 1) (hz0 : z 0 = g)
    (happly : ∀ n, ‖z (n + 1) - M (z n)‖ ≤ η * L * ‖z n‖) :
    ∀ n, ‖z n - exactPower M g n‖ ≤ ((1 + η) ^ n - 1) * L ^ n := by
  apply power_error_recurrence_bound _ L η hL hη
  · simp [exactPower, hz0]
  · intro n
    have hp := exactPower_norm_le M g L hL hM hg n
    have hz : ‖z n‖ ≤ L ^ n + ‖z n - exactPower M g n‖ := by
      have ht := norm_le_norm_add_norm_sub (exactPower M g n) (z n)
      rw [norm_sub_rev] at ht
      linarith
    calc
      ‖z (n + 1) - exactPower M g (n + 1)‖
          ≤ ‖z (n + 1) - M (z n)‖ + ‖M (z n) - M (exactPower M g n)‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ η * L * ‖z n‖ + L * ‖z n - exactPower M g n‖ := by
        apply add_le_add (happly n)
        rw [← map_sub]
        exact (M.le_opNorm _).trans
          (mul_le_mul_of_nonneg_right hM (norm_nonneg _))
      _ ≤ η * L * (L ^ n + ‖z n - exactPower M g n‖) +
            L * ‖z n - exactPower M g n‖ := by
        exact add_le_add_right (mul_le_mul_of_nonneg_left hz (by positivity)) _
      _ = η * L ^ (n + 1) + (1 + η) * L * ‖z n - exactPower M g n‖ := by ring

/-- A good exact-power lower bound survives the bounded perturbation. -/
theorem inexactPower_norm_lower (M : E →L[ℝ] E) (g : E) (z : ℕ → E)
    (L η a : ℝ) (hL : 0 ≤ L) (hη : 0 ≤ η) (hM : ‖M‖ ≤ L)
    (hg : ‖g‖ ≤ 1) (hz0 : z 0 = g)
    (happly : ∀ n, ‖z (n + 1) - M (z n)‖ ≤ η * L * ‖z n‖)
    (q : ℕ) (hgood : a * L ^ q ≤ ‖exactPower M g q‖) :
    (a - ((1 + η) ^ q - 1)) * L ^ q ≤ ‖z q‖ := by
  have he := inexactPower_error_bound M g z L η hL hη hM hg hz0 happly q
  have ht := norm_le_norm_add_norm_sub (z q) (exactPower M g q)
  nlinarith

/-- The upper norm estimate holds for every start and every successful
inexact application sequence. -/
theorem inexactPower_norm_upper (M : E →L[ℝ] E) (g : E) (z : ℕ → E)
    (L η : ℝ) (hL : 0 ≤ L) (hη : 0 ≤ η) (hM : ‖M‖ ≤ L)
    (hg : ‖g‖ ≤ 1) (hz0 : z 0 = g)
    (happly : ∀ n, ‖z (n + 1) - M (z n)‖ ≤ η * L * ‖z n‖) (q : ℕ) :
    ‖z q‖ ≤ (1 + η) ^ q * L ^ q := by
  have he := inexactPower_error_bound M g z L η hL hη hM hg hz0 happly q
  have hp := exactPower_norm_le M g L hL hM hg q
  have ht := norm_le_norm_add_norm_sub (exactPower M g q) (z q)
  rw [norm_sub_rev] at ht
  nlinarith

end Power

section Eigenvector

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- For a self-adjoint operator, power iteration preserves the component along
an eigenvector, including negative eigenvalues. -/
theorem exactPower_eigencomponent (M : E →L[ℝ] E) (g v : E) (μ : ℝ)
    (hsymm : ∀ x y, @inner ℝ E _ (M x) y = @inner ℝ E _ x (M y))
    (heigen : M v = μ • v) :
    ∀ n, @inner ℝ E _ v (exactPower M g n) = μ ^ n * @inner ℝ E _ v g := by
  intro n
  induction n with
  | zero => simp [exactPower]
  | succ n ih =>
    change @inner ℝ E _ v (M (exactPower M g n)) = _
    rw [← hsymm, heigen, real_inner_smul_left, ih]
    ring

/-- A good start gives a deterministic exact-power norm lower bound. Existence
of the eigenvector and the probability of a good start are separate obligations. -/
theorem exactPower_norm_lower_of_eigenvector (M : E →L[ℝ] E) (g v : E) (μ : ℝ)
    (hsymm : ∀ x y, @inner ℝ E _ (M x) y = @inner ℝ E _ x (M y))
    (heigen : M v = μ • v) (hv : ‖v‖ = 1) (n : ℕ) :
    |@inner ℝ E _ v g| * |μ| ^ n ≤ ‖exactPower M g n‖ := by
  have h := abs_real_inner_le_norm v (exactPower M g n)
  rw [exactPower_eigencomponent M g v μ hsymm heigen n,
    abs_mul, abs_pow, hv, one_mul] at h
  simpa [mul_comm] using h

/-- The manuscript's `3/4` margin survives inexact iteration whenever its total
relative error is at most one quarter of the start's eigenvector component. -/
theorem inexactPower_good_start_lower (M : E →L[ℝ] E) (g v : E) (z : ℕ → E)
    (μ η a : ℝ)
    (hsymm : ∀ x y, @inner ℝ E _ (M x) y = @inner ℝ E _ x (M y))
    (heigen : M v = μ • v) (hv : ‖v‖ = 1) (hM : ‖M‖ ≤ |μ|)
    (hη : 0 ≤ η) (hg : ‖g‖ ≤ 1) (hz0 : z 0 = g)
    (happly : ∀ n, ‖z (n + 1) - M (z n)‖ ≤ η * |μ| * ‖z n‖)
    (hstart : a ≤ |@inner ℝ E _ v g|) (q : ℕ)
    (hsmall : (1 + η) ^ q - 1 ≤ a / 4) :
    (3 * a / 4) * |μ| ^ q ≤ ‖z q‖ := by
  have hp := exactPower_norm_lower_of_eigenvector M g v μ hsymm heigen hv q
  have hgrowth : a * |μ| ^ q ≤ ‖exactPower M g q‖ :=
    (mul_le_mul_of_nonneg_right hstart (pow_nonneg (abs_nonneg _) _)).trans hp
  have hlo := inexactPower_norm_lower M g z |μ| η a (abs_nonneg _) hη hM
    hg hz0 happly q hgrowth
  have hscale := mul_le_mul_of_nonneg_right hsmall (pow_nonneg (abs_nonneg μ) q)
  nlinarith

end Eigenvector

end Matvec
