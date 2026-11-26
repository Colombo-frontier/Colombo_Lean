import Matvec.GameAlgebra
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Signed-dictionary witnesses and full-gap implications

The `FullGapAtMost` predicate is the pairwise form of the finite simplex
full gap: every row response minus every column response is at most ε.
It keeps the formal statement independent of conventions for empty extrema.
-/

namespace Matvec

noncomputable section
open Matrix
open scoped Matrix

variable {d n m : Type*} [Fintype d] [DecidableEq d]
  [Fintype n] [Fintype m]

def InSimplex {ι : Type*} [Fintype ι] (x : ι → ℝ) : Prop :=
  (∀ i, 0 ≤ x i) ∧ ∑ i, x i = 1

def FullGapAtMost (A : Matrix m n ℝ) (x : n → ℝ) (y : m → ℝ) (ε : ℝ) : Prop :=
  ∀ i j, (A *ᵥ x) i - (A.transpose *ᵥ y) j ≤ ε

/-- The usual max-minus-min full simplex gap from equation `l11-gap`. -/
def simplexGap [Nonempty m] [Nonempty n]
    (A : Matrix m n ℝ) (x : n → ℝ) (y : m → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (A *ᵥ x) -
    Finset.univ.inf' Finset.univ_nonempty (A.transpose *ᵥ y)

theorem fullGapAtMost_iff [Nonempty m] [Nonempty n]
    (A : Matrix m n ℝ) (x : n → ℝ) (y : m → ℝ) (ε : ℝ) :
    FullGapAtMost A x y ε ↔ simplexGap A x y ≤ ε := by
  constructor
  · intro h
    apply (sub_le_iff_le_add).mpr
    apply Finset.sup'_le
    intro i hi
    have hinf : (A *ᵥ x) i - ε ≤
        Finset.univ.inf' Finset.univ_nonempty (A.transpose *ᵥ y) := by
      apply Finset.le_inf'
      intro j hj
      have := h i j
      linarith
    linarith
  · intro h i j
    have hmax := Finset.le_sup' (A *ᵥ x) (Finset.mem_univ i)
    have hmin := Finset.inf'_le (A.transpose *ᵥ y) (Finset.mem_univ j)
    dsimp [simplexGap] at h
    linarith

/-- The signed coordinate dictionary `a [I,-I]`. -/
def signedDictionary (a : ℝ) : Matrix d (d ⊕ d) ℝ :=
  fun i => Sum.elim (fun j => if i = j then a else 0)
    (fun j => if i = j then -a else 0)

theorem signedDictionary_mulVec (a : ℝ) (xp xm : d → ℝ) :
    signedDictionary a *ᵥ Sum.elim xp xm = a • (xp - xm) := by
  ext i
  simp [signedDictionary, Matrix.mulVec, dotProduct, Fintype.sum_sum_type]
  ring

/-- Explicit convex representation in the signed dictionary. The mass not
used by the positive/negative parts is split equally between opposite atoms. -/
theorem signedDictionary_witness (a : ℝ) (ha : 0 < a) (z : d → ℝ)
    (i₀ : d) (hz : ∑ i, |z i| ≤ a) :
    ∃ x : d ⊕ d → ℝ, InSimplex x ∧ signedDictionary a *ᵥ x = z := by
  let t : ℝ := (1 - (∑ i, |z i|) / a) / 2
  have ht : 0 ≤ t := by
    dsimp [t]
    have := (div_le_one ha).mpr hz
    linarith
  let xp : d → ℝ := fun i => max (z i) 0 / a + if i = i₀ then t else 0
  let xm : d → ℝ := fun i => max (-z i) 0 / a + if i = i₀ then t else 0
  have hparts (i : d) : max (z i) 0 + max (-z i) 0 = |z i| := by
    by_cases h : 0 ≤ z i
    · rw [max_eq_left h, max_eq_right (by linarith), abs_of_nonneg h]
      ring
    · rw [max_eq_right (le_of_not_ge h), max_eq_left (by linarith),
        abs_of_nonpos (le_of_not_ge h)]
      ring
  refine ⟨Sum.elim xp xm, ⟨?_, ?_⟩, ?_⟩
  · intro i
    cases i with
    | inl i =>
      dsimp [xp]
      exact add_nonneg (div_nonneg (le_max_right _ _) ha.le) (by split <;> positivity)
    | inr i =>
      dsimp [xm]
      exact add_nonneg (div_nonneg (le_max_right _ _) ha.le) (by split <;> positivity)
  · simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, xp, xm,
      Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [← Finset.sum_div, ← Finset.sum_div]
    have hsum : (∑ i, max (z i) 0) + (∑ i, max (-z i) 0) = ∑ i, |z i| := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun i _ => hparts i)
    dsimp [t]
    have heq : (∑ i, max (z i) 0) / a + (∑ i, max (-z i) 0) / a =
        (∑ i, |z i|) / a := by rw [← add_div, hsum]
    linarith
  · rw [signedDictionary_mulVec]
    ext i
    change a * (xp i - xm i) = z i
    dsimp [xp, xm]
    have hdiff : max (z i) 0 - max (-z i) 0 = z i := by
      by_cases h : 0 ≤ z i
      · rw [max_eq_left h, max_eq_right (by linarith)]
        ring
      · rw [max_eq_right (le_of_not_ge h), max_eq_left (by linarith)]
        ring
    have heq : max (z i) 0 / a - max (-z i) 0 / a = z i / a := by
      rw [← sub_div, hdiff]
    calc
      _ = a * (max (z i) 0 / a - max (-z i) 0 / a) := by ring
      _ = a * (z i / a) := by rw [heq]
      _ = z i := by field_simp

/-- A feasible zero witness forces the dual term to be nonpositive and hence
each primal row response is bounded by the full gap. -/
theorem row_le_of_zero_witness (A : Matrix m n ℝ) (x xstar : n → ℝ)
    (y : m → ℝ) (ε : ℝ) (hstar : InSimplex xstar)
    (hzero : A *ᵥ xstar = 0) (hgap : FullGapAtMost A x y ε) :
    ∀ i, (A *ᵥ x) i ≤ ε := by
  intro i
  have hsum := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) =>
    mul_le_mul_of_nonneg_left (hgap i j) (hstar.1 j))
  have hz : ∑ j, xstar j * (A.transpose *ᵥ y) j = 0 := by
    have hid : ∑ j, xstar j * (A.transpose *ᵥ y) j = dotProduct y (A *ᵥ xstar) := by
      simp only [Matrix.mulVec, Matrix.transpose_apply, dotProduct, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro k hk
      ring
    rw [hid, hzero]
    simp [dotProduct]
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hstar.2,
    one_mul, hz, sub_zero] at hsum
  exact hsum

omit [DecidableEq d] in
/-- The unit Euclidean ball is contained in the l1 ball of radius sqrt(card d),
using its exact sum-of-squares characterization. -/
theorem sum_abs_le_sqrt_card (z : d → ℝ) (hz : ∑ i, z i ^ 2 ≤ 1) :
    ∑ i, |z i| ≤ Real.sqrt (Fintype.card d) := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun i : d => |z i|) (fun _ : d => (1 : ℝ))
  simp only [mul_one, sq_abs, one_pow, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one] at hcs
  have hcard : (0 : ℝ) ≤ Fintype.card d := Nat.cast_nonneg _
  have hsqrt := Real.sq_sqrt hcard
  have hbound : (∑ i, z i ^ 2) * (Fintype.card d : ℝ) ≤ (Fintype.card d : ℝ) :=
    mul_le_of_le_one_left hcard hz
  have habs : 0 ≤ ∑ i, |z i| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hroot := Real.sqrt_nonneg (Fintype.card d : ℝ)
  nlinarith

/-- The simplex witness of `lem:l11-simplex-witness`, with the solution
specified by its defining equation and Euclidean norm bound. -/
theorem simplex_zero_witness (H : Matrix d d ℝ) (b z : d → ℝ)
    (R : Matrix d m ℝ) (Λ : ℝ) (i₀ : d)
    (hsolve : H *ᵥ z = b) (hz : ∑ i, z i ^ 2 ≤ 1) :
    ∃ x : d ⊕ d → ℝ, InSimplex x ∧
      signedDictionary (Real.sqrt (Fintype.card d)) *ᵥ x = z ∧
      simplexMatrix H b R (signedDictionary (Real.sqrt (Fintype.card d))) Λ *ᵥ x = 0 := by
  have hcard : 0 < Fintype.card d := Fintype.card_pos_iff.mpr ⟨i₀⟩
  have ha : 0 < Real.sqrt (Fintype.card d : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hcard)
  obtain ⟨x, hx, hv⟩ := signedDictionary_witness (Real.sqrt (Fintype.card d)) ha
    z i₀ (sum_abs_le_sqrt_card z hz)
  refine ⟨x, hx, hv, ?_⟩
  apply simplexMatrix_zero_witness H b R _ Λ x hx.2
  rw [hv, hsolve]

/-- Left orthogonality preserves the squared Euclidean norm of transpose
multiplication. This is the exact coordinate identity behind the detector. -/
theorem orthogonal_sum_sq (Q : Matrix d d ℝ) (hQ : Q * Q.transpose = 1)
    (r : d → ℝ) : ∑ i, (Q.transpose *ᵥ r) i ^ 2 = ∑ i, r i ^ 2 := by
  have hdot : dotProduct (Q.transpose *ᵥ r) (Q.transpose *ᵥ r) = dotProduct r r := by
    rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, Matrix.mulVec_mulVec,
      hQ, Matrix.one_mulVec]
  simpa only [dotProduct, pow_two] using hdot

/-- The two signed atoms expose both signs of each rotated residual
coordinate. -/
theorem detector_transpose_mulVec (Q : Matrix d d ℝ) (a : ℝ) (r : d → ℝ) :
    (Q * signedDictionary a).transpose *ᵥ r =
      Sum.elim (a • (Q.transpose *ᵥ r)) ((-a) • (Q.transpose *ᵥ r)) := by
  rw [Matrix.transpose_mul, ← Matrix.mulVec_mulVec]
  ext i
  cases i with
  | inl i => simp [signedDictionary, Matrix.mulVec, dotProduct]
  | inr i => simp [signedDictionary, Matrix.mulVec, dotProduct]

/-- The signed orthogonal dictionary detects the entire Euclidean residual.
This deterministic statement holds for every orthogonal Q, without any
probabilistic entry-normalization assumption. -/
theorem detector_residual_bound (Q : Matrix d d ℝ) (hQ : Q * Q.transpose = 1)
    (r : d → ℝ) (i₀ : d) (Λ ε : ℝ) (hΛ : 0 < Λ)
    (hrows : ∀ i, Λ⁻¹ *
      ((Q * signedDictionary (Real.sqrt (Fintype.card d))).transpose *ᵥ r) i ≤ ε) :
    Real.sqrt (∑ i, r i ^ 2) ≤ Λ * ε := by
  let a : ℝ := Real.sqrt (Fintype.card d)
  let c : d → ℝ := Q.transpose *ᵥ r
  have hcardnat : 0 < Fintype.card d := Fintype.card_pos_iff.mpr ⟨i₀⟩
  have hcard : (0 : ℝ) < Fintype.card d := by exact_mod_cast hcardnat
  have ha : a ^ 2 = Fintype.card d := Real.sq_sqrt hcard.le
  have hb (i : d) : -(Λ * ε) ≤ a * c i ∧ a * c i ≤ Λ * ε := by
    have hp := hrows (Sum.inl i)
    have hm := hrows (Sum.inr i)
    rw [detector_transpose_mulVec] at hp hm
    simp only [Sum.elim_inl, Sum.elim_inr, Pi.smul_apply, smul_eq_mul] at hp hm
    have hp' := mul_le_mul_of_nonneg_left hp hΛ.le
    have hm' := mul_le_mul_of_nonneg_left hm hΛ.le
    rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hΛ), one_mul] at hp' hm'
    dsimp [a, c]
    constructor <;> nlinarith
  have he : 0 ≤ Λ * ε := by have := hb i₀; linarith
  have hs (i : d) : a ^ 2 * c i ^ 2 ≤ (Λ * ε) ^ 2 := by
    have := (abs_le.mpr (hb i))
    have hsq := mul_self_le_mul_self (abs_nonneg (a * c i)) this
    simpa only [← sq, sq_abs, mul_pow] using hsq
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hs i)
  simp only [← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, ha] at hsum
  have hc : ∑ i, c i ^ 2 ≤ (Λ * ε) ^ 2 := (mul_le_mul_left hcard).mp hsum
  have heq := orthogonal_sum_sq Q hQ r
  change (∑ i, c i ^ 2) = _ at heq
  rw [heq] at hc
  exact (Real.sqrt_le_left he).mpr hc

/-- `lem:l11-residual-gap`: a full simplex gap at most ε gives residual at
most Λε. Here the source solution is provided through its exact equation and
unit-ball bound, both consequences of the source spectral promise. -/
theorem simplex_full_gap_residual (H Q : Matrix d d ℝ) (b z : d → ℝ)
    (hQ : Q * Q.transpose = 1) (i₀ : d)
    (hsolve : H *ᵥ z = b) (hz : ∑ i, z i ^ 2 ≤ 1)
    (Λ ε : ℝ) (hΛ : 0 < Λ) (x y : d ⊕ d → ℝ)
    (hx : InSimplex x)
    (hgap : FullGapAtMost
      (simplexMatrix H b (Q * signedDictionary (Real.sqrt (Fintype.card d)))
        (signedDictionary (Real.sqrt (Fintype.card d))) Λ) x y ε) :
    Real.sqrt (∑ i,
      ((H *ᵥ (signedDictionary (Real.sqrt (Fintype.card d)) *ᵥ x)) i - b i) ^ 2)
      ≤ Λ * ε := by
  let V : Matrix d (d ⊕ d) ℝ := signedDictionary (Real.sqrt (Fintype.card d))
  let R := Q * V
  obtain ⟨xstar, hstar, _, hzero⟩ := simplex_zero_witness H b z R Λ i₀ hsolve hz
  have hrows := row_le_of_zero_witness (simplexMatrix H b R V Λ) x xstar y ε
    hstar hzero hgap
  apply detector_residual_bound Q hQ (H *ᵥ (V *ᵥ x) - b) i₀ Λ ε hΛ
  intro i
  have h := hrows i
  rw [simplexMatrix_mulVec, hx.2, one_smul] at h
  exact h

/-- A matrix with smallest singular value at least one has a unit-ball
solution for every unit-ball right-hand side. The spectral promise is stated
in its equivalent coordinate form, so no spectral theorem is assumed. -/
theorem expanding_source_solution (H : Matrix d d ℝ)
    (hH : ∀ v : d → ℝ, ∑ i, v i ^ 2 ≤ ∑ i, (H *ᵥ v) i ^ 2)
    (b : d → ℝ) (hb : ∑ i, b i ^ 2 ≤ 1) :
    ∃ z : d → ℝ, H *ᵥ z = b ∧ ∑ i, z i ^ 2 ≤ 1 := by
  have hinj : Function.Injective H.mulVec := by
    intro x y hxy
    have h := hH (x - y)
    rw [Matrix.mulVec_sub, hxy, sub_self] at h
    simp only [Pi.zero_apply, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, Finset.sum_const_zero] at h
    have hz : ∑ i, (x i - y i) ^ 2 = 0 :=
      le_antisymm h (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    have hcoord := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i (_ : i ∈ Finset.univ) => sq_nonneg (x i - y i))).mp hz
    ext i
    have hi := hcoord i (Finset.mem_univ i)
    nlinarith
  have hsurj : Function.Surjective H.mulVec :=
    Matrix.mulVec_surjective_iff_isUnit.mpr (Matrix.mulVec_injective_iff_isUnit.mp hinj)
  obtain ⟨z, hsolve⟩ := hsurj b
  refine ⟨z, hsolve, ?_⟩
  have h := hH z
  rw [hsolve] at h
  exact h.trans hb

/-- Complete deterministic simplex reduction from the source spectral
promise and a small full gap to a Euclidean residual bound. -/
theorem simplex_source_residual (H Q : Matrix d d ℝ)
    (hH : ∀ v : d → ℝ, ∑ i, v i ^ 2 ≤ ∑ i, (H *ᵥ v) i ^ 2)
    (hQ : Q * Q.transpose = 1) (b : d → ℝ) (hb : ∑ i, b i ^ 2 ≤ 1)
    (i₀ : d) (Λ ε : ℝ) (hΛ : 0 < Λ) (x y : d ⊕ d → ℝ)
    (hx : InSimplex x)
    (hgap : FullGapAtMost
      (simplexMatrix H b (Q * signedDictionary (Real.sqrt (Fintype.card d)))
        (signedDictionary (Real.sqrt (Fintype.card d))) Λ) x y ε) :
    Real.sqrt (∑ i,
      ((H *ᵥ (signedDictionary (Real.sqrt (Fintype.card d)) *ᵥ x)) i - b i) ^ 2)
      ≤ Λ * ε := by
  obtain ⟨z, hsolve, hz⟩ := expanding_source_solution H hH b hb
  exact simplex_full_gap_residual H Q b z hQ i₀ hsolve hz Λ ε hΛ x y hx hgap

/-- The exact constant-residual threshold used in the proof of the simplex
part of `thm:main-sequences`, with the usual max-minus-min full gap. -/
theorem simplex_small_gap_solves [Nonempty d] (H Q : Matrix d d ℝ)
    (hH : ∀ v : d → ℝ, ∑ i, v i ^ 2 ≤ ∑ i, (H *ᵥ v) i ^ 2)
    (hQ : Q * Q.transpose = 1) (b : d → ℝ) (hb : ∑ i, b i ^ 2 ≤ 1)
    (Λ : ℝ) (hΛ : 0 < Λ) (x y : d ⊕ d → ℝ) (hx : InSimplex x)
    (hgap : simplexGap
      (simplexMatrix H b (Q * signedDictionary (Real.sqrt (Fintype.card d)))
        (signedDictionary (Real.sqrt (Fintype.card d))) Λ) x y ≤ 1 / (2 * Λ)) :
    Real.sqrt (∑ i,
      ((H *ᵥ (signedDictionary (Real.sqrt (Fintype.card d)) *ᵥ x)) i - b i) ^ 2)
      ≤ 1 / 2 := by
  have h := simplex_source_residual H Q hH hQ b hb (Classical.choice inferInstance)
    Λ (1 / (2 * Λ)) hΛ x y hx ((fullGapAtMost_iff _ _ _ _).mpr hgap)
  have hscale : Λ * (1 / (2 * Λ)) = 1 / 2 := by field_simp; ring
  rwa [hscale] at h

end
end Matvec
