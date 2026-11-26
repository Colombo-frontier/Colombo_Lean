import SpectralNewton254

noncomputable section
open scoped Matrix.Norms.Operator BigOperators
open Matrix
namespace Paper254

theorem rotatedPrecision_const {d : ℕ} (U : Matrix.unitaryGroup (Fin d) ℝ) (x : ℝ) :
    rotatedPrecision U (fun _=>x)=x • (1:Precision d) := by
  have he : (fun _ : Fin d=>x)=x • (fun _=>1:Coordinates d) := by ext j; simp
  rw [he]
  simp only [rotatedPrecision, Matrix.diagonal_smul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.diagonal_one, mul_one, ← star_eq_conjTranspose, unitary.coe_star_mul_self]

theorem realMatrix_scalar {d : ℕ} (x : ℚ) :
    realMatrix (x • (1:Matrix (Fin d) (Fin d) ℚ))=(x:ℝ) • (1:Precision d) := by
  ext i j
  by_cases hij : i=j <;>
    simp [realMatrix, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.one_apply,hij]

/-- The actual rational matrix iteration approximates the positive square
root. Its rounded iterates may be nonsymmetric; invertibility and all
intermediate rounding errors are controlled by the perturbation proof. -/
theorem rationalMatrixNewton_sqrt_error {d : ℕ} (hd : 0<d)
    (A : Matrix (Fin d) (Fin d) ℚ) (U : Matrix.unitaryGroup (Fin d) ℝ)
    (a : Coordinates d) (ha : ∀ j,0<a j) (hA : realMatrix A=rotatedPrecision U a)
    (x : ℚ) (r M K : ℝ) (hr : 0<r) (hM : 0<M) (hK : 1≤K)
    (hlower : ∀ j,r≤Real.sqrt (a j)) (hupper : ∀ j,Real.sqrt (a j)≤(x:ℝ))
    (hMinv : (d:ℝ)^2/r≤M) (hlip : (1+2*M^2*‖realMatrix A‖)/2≤K)
    (p N : ℕ) (hguard : (d:ℝ)*((2:ℝ)^p)⁻¹*(2*K)^N*M≤1/2) :
    (∀ k≤N,IsUnit (realMatrix (rationalMatrixNewton p A (x • 1) k))) ∧
    ‖realMatrix (rationalMatrixNewton p A (x • 1) N)-
      rotatedPrecision U (fun j=>Real.sqrt (a j))‖ ≤
      (d:ℝ)*((2:ℝ)^p)⁻¹*(2*K)^N+(d:ℝ)^2*(x:ℝ)*(1/2:ℝ)^N := by
  letI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  let c : ℕ → Coordinates d := fun n j=>scalarExactNewton (a j) (x:ℝ) n
  have hc : ∀ n j,0<c n j := by
    intro n j
    exact (Real.sqrt_pos.mpr (ha j)).trans_le (scalarExactNewton_bounds _ _ (ha j) (hupper j) n).1
  let X : ℕ → (Precision d)ˣ := fun n=>(rotatedPrecision_posDef U (c n) (hc n)).isUnit.unit
  have hX : ∀ n,(X n:Precision d)=rotatedPrecision U (c n) := by
    intro n
    exact (rotatedPrecision_posDef U (c n) (hc n)).isUnit.unit_spec
  let Y : ℕ → Precision d := fun n=>realMatrix (rationalMatrixNewton p A (x • 1) n)
  have hstart : Y 0=(X 0:Precision d) := by
    rw [hX]
    dsimp only [Y]
    rw [rationalMatrixNewton_zero]
    change realMatrix (x • (1:Matrix (Fin d) (Fin d) ℚ))=rotatedPrecision U (fun _=>(x:ℝ))
    rw [realMatrix_scalar,rotatedPrecision_const]
  have hnext : ∀ k<N,(X (k+1):Precision d)=algebraNewtonStep (realMatrix A) (X k:Precision d) := by
    intro k _
    rw [hX,hX,hA,rotatedNewton_step U a (c k) (fun j=>(hc k j).ne')]
    rfl
  have hinv : ∀ k≤N,‖(↑(X k)⁻¹:Precision d)‖≤M := by
    intro k _
    rw [← Ring.inverse_unit (X k),hX,rotatedPrecision_inverse U (c k) (fun j=>(hc k j).ne')]
    apply (rotatedPrecision_norm_bound U ((c k)⁻¹) (1/r) (by positivity) ?_).trans
      (by simpa only [div_eq_mul_inv,one_mul] using hMinv)
    intro j
    have hlow : r≤c k j := (hlower j).trans (scalarExactNewton_bounds _ _ (ha j) (hupper j) k).1
    change |(c k j)⁻¹|≤1/r
    rw [abs_of_pos (inv_pos.mpr (hc k j)),one_div]
    exact inv_le_inv₀ (hc k j) hr |>.mpr hlow
  have hround : ∀ k<N,‖Y (k+1)-algebraNewtonStep (realMatrix A) (Y k)‖≤d*((2:ℝ)^p)⁻¹ := by
    intro k _
    dsimp only [Y]
    rw [rationalMatrixNewton_succ]
    exact rationalMatrixNewtonStep_error p A (rationalMatrixNewton p A (x • 1) k)
  have ht := rounded_newton_trajectory (realMatrix A) X Y N M K (d*((2:ℝ)^p)⁻¹)
    hM hK (by positivity) hstart hnext hinv hlip hround hguard
  refine ⟨fun k hk=>(ht k hk).2,?_⟩
  have hdiag : ∀ j,|c N j-Real.sqrt (a j)|≤(x:ℝ)*(1/2:ℝ)^N := by
    intro j
    have hs := scalarExactNewton_bounds _ _ (ha j) (hupper j) N
    rw [abs_of_nonneg (sub_nonneg.mpr hs.1)]
    apply hs.2.trans
    gcongr
    exact sub_le_self _ (Real.sqrt_nonneg _)
  have hx0 : 0≤(x:ℝ) := (Real.sqrt_nonneg (a (Classical.choice inferInstance))).trans
    (hupper (Classical.choice inferInstance))
  have hn := rotatedPrecision_norm_bound U (c N-(fun j=>Real.sqrt (a j)))
    ((x:ℝ)*(1/2:ℝ)^N) (by positivity) hdiag
  rw [← rotatedPrecision_sub,← hX] at hn
  have htri := norm_sub_le_norm_sub_add_norm_sub (Y N) (X N:Precision d)
    (rotatedPrecision U (fun j=>Real.sqrt (a j)))
  have he := (ht N le_rfl).1
  change ‖Y N-rotatedPrecision U (fun j=>Real.sqrt (a j))‖≤_
  nlinarith

end Paper254
#print axioms Paper254.rationalMatrixNewton_sqrt_error
