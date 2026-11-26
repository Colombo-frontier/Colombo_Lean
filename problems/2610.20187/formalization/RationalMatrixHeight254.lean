import EfficientInverseStructure254
import Mathlib.Data.Nat.Size

open Matrix
open scoped BigOperators
namespace Paper254

/-- A shared-denominator integer encoding with an explicit binary magnitude bound. -/
def MatrixHeight {m n : Type*} (A : Matrix m n ℚ) (b : ℕ) : Prop :=
  ∃ Z : Matrix m n ℤ,∃ q : ℤ,q≠0 ∧ |q|≤(2:ℤ)^b ∧
    (∀ i j,|Z i j|≤(2:ℤ)^b) ∧ ∀ i j,A i j=(Z i j:ℚ)/(q:ℚ)

theorem MatrixHeight.mono {m n : Type*} {b c : ℕ} {A : Matrix m n ℚ}
    (hA : MatrixHeight A b) (hbc : b≤c) : MatrixHeight A c := by
  obtain ⟨Z,q,hq,hqb,hZ,hr⟩ := hA
  have hp : (2:ℤ)^b≤2^c := pow_le_pow_right₀ (by norm_num) hbc
  exact ⟨Z,q,hq,hqb.trans hp,fun i j=>(hZ i j).trans hp,hr⟩

theorem MatrixHeight.submatrix {m n k l : Type*} {b : ℕ} {A : Matrix m n ℚ}
    (hA : MatrixHeight A b) (e : k→m) (f : l→n) :
    MatrixHeight (A.submatrix e f) b := by
  obtain ⟨Z,q,hq,hqb,hZ,hr⟩ := hA
  exact ⟨Z.submatrix e f,q,hq,hqb,fun i j=>hZ (e i) (f j),fun i j=>hr (e i) (f j)⟩

theorem MatrixHeight.transpose {m n : Type*} {b : ℕ} {A : Matrix m n ℚ}
    (hA : MatrixHeight A b) : MatrixHeight Aᵀ b := by
  obtain ⟨Z,q,hq,hqb,hZ,hr⟩ := hA
  exact ⟨Zᵀ,q,hq,hqb,fun i j=>hZ j i,fun i j=>hr j i⟩

theorem MatrixHeight.neg {m n : Type*} {b : ℕ} {A : Matrix m n ℚ}
    (hA : MatrixHeight A b) : MatrixHeight (-A) b := by
  obtain ⟨Z,q,hq,hqb,hZ,hr⟩ := hA
  refine ⟨-Z,q,hq,hqb,?_,?_⟩
  · intro i j
    simpa only [Matrix.neg_apply,abs_neg] using hZ i j
  · intro i j
    simp only [Matrix.neg_apply,Int.cast_neg,neg_div,hr]

theorem MatrixHeight.add {m n : Type*} {b c : ℕ} {A B : Matrix m n ℚ}
    (hA : MatrixHeight A b) (hB : MatrixHeight B c) : MatrixHeight (A+B) (b+c+1) := by
  obtain ⟨Z,q,hq,hqb,hZ,hr⟩ := hA
  obtain ⟨W,r,hr0,hrb,hW,hs⟩ := hB
  refine ⟨fun i j=>Z i j*r+W i j*q,q*r,mul_ne_zero hq hr0,?_,?_,?_⟩
  · rw [abs_mul,pow_succ,pow_add]
    have hh := mul_le_mul hqb hrb (abs_nonneg r) (by positivity : (0:ℤ)≤2^b)
    nlinarith [show (0:ℤ)≤2^b*2^c by positivity]
  · intro i j
    calc
      _ ≤ |Z i j*r|+|W i j*q| := abs_add_le _ _
      _ ≤ (2:ℤ)^b*2^c+2^c*2^b := by
        rw [abs_mul,abs_mul]
        exact add_le_add (mul_le_mul (hZ i j) hrb (abs_nonneg _) (by positivity))
          (mul_le_mul (hW i j) hqb (abs_nonneg _) (by positivity))
      _ = _ := by rw [pow_succ,pow_add]; ring
  · intro i j
    change A i j+B i j=_
    rw [hr,hs]
    push_cast
    have hq' : (q:ℚ)≠0 := by exact_mod_cast hq
    have hr' : (r:ℚ)≠0 := by exact_mod_cast hr0
    field_simp

theorem MatrixHeight.sub {m n : Type*} {b c : ℕ} {A B : Matrix m n ℚ}
    (hA : MatrixHeight A b) (hB : MatrixHeight B c) : MatrixHeight (A-B) (b+c+1) := by
  simpa only [sub_eq_add_neg] using hA.add hB.neg

theorem int_dim_le_pow (n : ℕ) : (n:ℤ)≤(2:ℤ)^n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [pow_succ]
    push_cast
    have hp : (1:ℤ)≤2^n := one_le_pow₀ (by norm_num)
    omega

theorem MatrixHeight.mul {m k : Type*} {n b c : ℕ}
    {A : Matrix m (Fin n) ℚ} {B : Matrix (Fin n) k ℚ}
    (hA : MatrixHeight A b) (hB : MatrixHeight B c) : MatrixHeight (A*B) (b+c+n) := by
  obtain ⟨Z,q,hq,hqb,hZ,hr⟩ := hA
  obtain ⟨W,r,hr0,hrb,hW,hs⟩ := hB
  refine ⟨Z*W,q*r,mul_ne_zero hq hr0,?_,?_,?_⟩
  · rw [abs_mul,pow_add,pow_add]
    have hh := mul_le_mul hqb hrb (abs_nonneg r) (by positivity : (0:ℤ)≤2^b)
    exact hh.trans (le_mul_of_one_le_right (by positivity) (one_le_pow₀ (by norm_num)))
  · intro i j
    rw [Matrix.mul_apply]
    calc
      _ ≤ ∑ t,|Z i t*W t j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _t : Fin n,(2:ℤ)^b*2^c := Finset.sum_le_sum (fun t _=>by
        rw [abs_mul]
        exact mul_le_mul (hZ i t) (hW t j) (abs_nonneg _) (by positivity))
      _ = (n:ℤ)*((2:ℤ)^b*2^c) := by simp
      _ ≤ (2:ℤ)^n*((2:ℤ)^b*2^c) :=
        mul_le_mul_of_nonneg_right (int_dim_le_pow n) (by positivity)
      _ = _ := by simp only [pow_add]; ring
  · intro i j
    simp only [Matrix.mul_apply,hr,hs,div_mul_div_comm]
    rw [←Finset.sum_div]
    norm_cast

theorem MatrixHeight.pivot_inverse {b : ℕ} {A : Matrix (Fin 1) (Fin 1) ℚ}
    (hA : MatrixHeight A b) (ha : A 0 0≠0) : MatrixHeight (scalarPivotInverse A) b := by
  obtain ⟨Z,q,hq,hqb,hZ,hr⟩ := hA
  have hZ0 : Z 0 0≠0 := by
    intro hz
    apply ha
    rw [hr,hz]
    simp
  refine ⟨fun _ _=>q,Z 0 0,hZ0,hZ 0 0,fun _ _=>hqb,?_⟩
  intro i j
  simp only [scalarPivotInverse,hr,inv_div]

theorem MatrixHeight.mask {m n : Type*} {b : ℕ} {A : Matrix m n ℚ}
    (hA : MatrixHeight A b) (P : m→n→Prop) [∀ i j,Decidable (P i j)] :
    MatrixHeight (fun i j=>if P i j then A i j else 0) b := by
  obtain ⟨Z,q,hq,hqb,hZ,hr⟩ := hA
  refine ⟨fun i j=>if P i j then Z i j else 0,q,hq,hqb,?_,?_⟩
  · intro i j
    dsimp only
    split_ifs
    · exact hZ i j
    · simp
  · intro i j
    dsimp only
    split_ifs
    · exact hr i j
    · simp

/-- The witness bounds also bound Lean's reduced rational representation;
they are not merely bounds on a hypothetical larger fraction. -/
theorem MatrixHeight.reduced_bounds {m n : Type*} {b : ℕ} {A : Matrix m n ℚ}
    (hA : MatrixHeight A b) (i : m) (j : n) :
    |(A i j).num|≤(2:ℤ)^b ∧ ((A i j).den:ℤ)≤(2:ℤ)^b := by
  obtain ⟨Z,q,hq,hqb,hZ,hr⟩ := hA
  obtain ⟨c,hnum,hden⟩ := Rat.exists_eq_mul_div_num_and_eq_mul_div_den (Z i j) hq
  rw [←hr] at hnum hden
  have hc : c≠0 := by intro hz; rw [hz,zero_mul] at hden; exact hq hden
  have hc1 : (1:ℤ)≤|c| := by have hp := abs_pos.mpr hc; omega
  constructor
  · calc
      _ ≤ |c| * |(A i j).num| := le_mul_of_one_le_left (abs_nonneg _) hc1
      _ = |Z i j| := by rw [hnum,abs_mul]
      _ ≤ _ := hZ i j
  · calc
      _ ≤ |c| * ((A i j).den:ℤ) := le_mul_of_one_le_left (by positivity) hc1
      _ = |q| := by rw [hden,abs_mul,abs_of_nonneg (by positivity : (0:ℤ)≤(A i j).den)]
      _ ≤ _ := hqb

theorem MatrixHeight.reduced_bits {m n : Type*} {b : ℕ} {A : Matrix m n ℚ}
    (hA : MatrixHeight A b) (i : m) (j : n) :
    (A i j).num.natAbs.size≤b+1 ∧ (A i j).den.size≤b+1 := by
  obtain ⟨hn,hd⟩ := hA.reduced_bounds i j
  have hcast : ((A i j).num.natAbs:ℤ)≤(2:ℤ)^b := by
    simpa only [Int.natCast_natAbs] using hn
  have hn' : (A i j).num.natAbs≤2^b := by exact_mod_cast hcast
  have hd' : (A i j).den≤2^b := by exact_mod_cast hd
  constructor
  · simpa only [Nat.size_pow] using Nat.size_le_size hn'
  · simpa only [Nat.size_pow] using Nat.size_le_size hd'

/-- This bounds every subset sum, including all prefix and suffix
accumulators evaluated by a matrix-multiplication dot product. -/
theorem matrix_mul_partial_bits {m k : Type*} {n b c : ℕ}
    {A : Matrix m (Fin n) ℚ} {B : Matrix (Fin n) k ℚ}
    (hA : MatrixHeight A b) (hB : MatrixHeight B c)
    (P : Fin n→Prop) [DecidablePred P] (i : m) (j : k) :
    (∑ t : Fin n,if P t then A i t*B t j else 0).num.natAbs.size≤b+c+n+1 ∧
    (∑ t : Fin n,if P t then A i t*B t j else 0).den.size≤b+c+n+1 := by
  have hh := ((hA.mask (fun _ t=>P t)).mul hB).reduced_bits i j
  simpa only [Matrix.mul_apply,ite_mul,zero_mul] using hh

end Paper254
#print axioms Paper254.MatrixHeight.mul
