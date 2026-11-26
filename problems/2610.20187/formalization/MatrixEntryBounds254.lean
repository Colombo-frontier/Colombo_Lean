import RationalMatrixNewton254

open scoped Matrix.Norms.Operator BigOperators NNReal
open Matrix
namespace Paper254

theorem matrix_entry_le_operator_norm {d : ℕ} (A : Precision d) (i j : Fin d) :
    |A i j|≤‖A‖ := by
  have hrow : ‖A i j‖₊≤∑ k,‖A i k‖₊ :=
    Finset.single_le_sum (fun k _ => zero_le (‖A i k‖₊)) (Finset.mem_univ j)
  have hsup : (∑ k,‖A i k‖₊)≤Finset.univ.sup (fun l=>∑ k,‖A l k‖₊) :=
    Finset.le_sup (f := fun l=>∑ k,‖A l k‖₊) (Finset.mem_univ i)
  rw [← Matrix.linfty_opNNNorm_def] at hsup
  exact hrow.trans hsup

def rationalSymmetrize {d : ℕ} (A : Matrix (Fin d) (Fin d) ℚ) :=
  (1/2:ℚ) • (A+A.transpose)

theorem rationalSymmetrize_symmetric {d : ℕ} (A : Matrix (Fin d) (Fin d) ℚ) :
    ∀ i j,rationalSymmetrize A i j=rationalSymmetrize A j i := by
  intro i j
  change (1/2:ℚ)*(A i j+A j i)=(1/2:ℚ)*(A j i+A i j)
  ring

theorem rationalSymmetrize_error {d : ℕ} (A : Matrix (Fin d) (Fin d) ℚ)
    (B : Precision d) (hB : ∀ i j,B i j=B j i) (e : ℝ)
    (herror : ‖realMatrix A-B‖≤e) :
    ∀ i j,|realMatrix (rationalSymmetrize A) i j-B i j|≤e := by
  intro i j
  have hij := (matrix_entry_le_operator_norm (realMatrix A-B) i j).trans herror
  have hji := (matrix_entry_le_operator_norm (realMatrix A-B) j i).trans herror
  change |(A i j:ℝ)-B i j|≤e at hij
  change |(A j i:ℝ)-B j i|≤e at hji
  rw [← hB i j] at hji
  change |(((1/2:ℚ)*(A i j+A j i):ℚ):ℝ)-B i j|≤e
  push_cast
  obtain ⟨hij0,hij1⟩ := abs_le.mp hij
  obtain ⟨hji0,hji1⟩ := abs_le.mp hji
  exact abs_le.mpr ⟨by linarith,by linarith⟩

theorem rationalMatrixNewton_numerator_bound {d : ℕ} (p n : ℕ)
    (A X : Matrix (Fin d) (Fin d) ℚ) (B : ℝ) (hB : 0≤B)
    (hbound : ‖realMatrix (rationalMatrixNewton p A X (n+1))‖≤B) :
    ∀ i j,∃ z : ℤ, rationalMatrixNewton p A X (n+1) i j=(z:ℚ)/(2:ℚ)^p ∧
      |(z:ℝ)|≤B*(2:ℝ)^p := by
  intro i j
  obtain ⟨z,hz⟩ := rationalMatrixNewton_encoding p n A X i j
  refine ⟨z,hz,?_⟩
  have he := (matrix_entry_le_operator_norm
    (realMatrix (rationalMatrixNewton p A X (n+1))) i j).trans hbound
  change |(rationalMatrixNewton p A X (n+1) i j:ℝ)|≤B at he
  rw [hz] at he
  push_cast at he
  rw [abs_div,abs_of_pos (by positivity : (0:ℝ)<2^p)] at he
  exact (div_le_iff₀ (by positivity)).mp he

end Paper254
#print axioms Paper254.rationalSymmetrize_error
#print axioms Paper254.rationalMatrixNewton_numerator_bound
