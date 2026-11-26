import RationalMatrixHeight254
import RationalInverseEncoding254

open Matrix
namespace Paper254

def inverseHeight (d b : ℕ) := (d+1)*(b+d+1)

theorem MatrixHeight.inv {d b : ℕ} {A : Matrix (Fin d) (Fin d) ℚ}
    (hA : MatrixHeight A b) (hu : IsUnit A) : MatrixHeight A⁻¹ (inverseHeight d b) := by
  obtain ⟨Z,q,hq,hqb,hZ,hr⟩ := hA
  exact rational_inverse_encoding A Z q b hq hqb hZ hr (A.isUnit_iff_isUnit_det.mp hu)

/-- One inverse-height bound covers every inverse returned by the recursion;
two applications cover every recursive input, uniformly in recursion depth. -/
theorem SchurDescendant.height {d b : ℕ} {A : Matrix (Fin d) (Fin d) ℚ}
    (hA : A.PosDef) (hheight : MatrixHeight A b) {n : ℕ}
    {B : Matrix (Fin n) (Fin n) ℚ} (hB : SchurDescendant A B) :
    MatrixHeight B⁻¹ (inverseHeight d b) ∧
    MatrixHeight B (inverseHeight d (inverseHeight d b)) := by
  have hroot := hheight.inv hA.isUnit
  obtain ⟨e,he,hinv⟩ := hB.inverse_submatrix hA
  have hb : MatrixHeight B⁻¹ (inverseHeight d b) := by rw [hinv]; exact hroot.submatrix e e
  refine ⟨hb,?_⟩
  have hh := hb.inv (hB.posDef hA).inv.isUnit
  letI := (hB.posDef hA).isUnit.invertible
  rw [Matrix.inv_inv_of_invertible] at hh
  apply hh.mono
  have hn := hB.dimension_le hA
  change (n+1)*(inverseHeight d b+n+1)≤(d+1)*(inverseHeight d b+d+1)
  exact Nat.mul_le_mul (by omega) (by omega)

/-- The matrix values evaluated by a Schur step, including the intermediate
products in both the complement and inverse assembly. -/
def SchurStageHeight {n : ℕ} (A : Matrix (Fin (n+1)) (Fin (n+1)) ℚ)
    (J : Matrix (Fin n) (Fin n) ℚ) (b : ℕ) : Prop :=
  let B := inverseBlocks A
  let I := scalarPivotInverse B.toBlocks₁₁
  let R := I*B.toBlocks₁₂*J
  let C := J*B.toBlocks₂₁*I
  MatrixHeight A b ∧ MatrixHeight J b ∧ MatrixHeight I b ∧
  MatrixHeight (B.toBlocks₂₁*I) b ∧
  MatrixHeight (B.toBlocks₂₁*I*B.toBlocks₁₂) b ∧ MatrixHeight (inverseSchur A) b ∧
  MatrixHeight (I*B.toBlocks₁₂) b ∧ MatrixHeight R b ∧
  MatrixHeight (J*B.toBlocks₂₁) b ∧ MatrixHeight C b ∧
  MatrixHeight (R*B.toBlocks₂₁) b ∧ MatrixHeight (R*B.toBlocks₂₁*I) b ∧
  MatrixHeight (I+R*B.toBlocks₂₁*I) b ∧ MatrixHeight (-R) b ∧ MatrixHeight (-C) b

theorem SchurStageHeight.mono {n b c : ℕ} {A : Matrix (Fin (n+1)) (Fin (n+1)) ℚ}
    {J : Matrix (Fin n) (Fin n) ℚ} (h : SchurStageHeight A J b) (hbc : b≤c) :
    SchurStageHeight A J c := by
  rcases h with ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15⟩
  exact ⟨h1.mono hbc,h2.mono hbc,h3.mono hbc,h4.mono hbc,h5.mono hbc,
    h6.mono hbc,h7.mono hbc,h8.mono hbc,h9.mono hbc,h10.mono hbc,
    h11.mono hbc,h12.mono hbc,h13.mono hbc,h14.mono hbc,h15.mono hbc⟩

theorem schur_stage_height {n e f : ℕ} (A : Matrix (Fin (n+1)) (Fin (n+1)) ℚ)
    (hA : A.PosDef) (J : Matrix (Fin n) (Fin n) ℚ)
    (hinput : MatrixHeight A e) (hout : MatrixHeight J f) :
    SchurStageHeight A J (f+5*e+2*n+3) := by
  let B := inverseBlocks A
  have hB : MatrixHeight B e := hinput.submatrix (inverseSplit n) (inverseSplit n)
  have h11 := hB.submatrix Sum.inl Sum.inl
  have h12 := hB.submatrix Sum.inl Sum.inr
  have h21 := hB.submatrix Sum.inr Sum.inl
  have h22 := hB.submatrix Sum.inr Sum.inr
  have hf := (positive_first_block B (positive_submatrix_equiv A hA (inverseSplit n))).isUnit
  have hp : B.toBlocks₁₁ 0 0≠0 := by
    simpa using (B.toBlocks₁₁.isUnit_iff_isUnit_det.mp hf).ne_zero
  have hI := h11.pivot_inverse hp
  have hs1 := h21.mul hI
  have hs2 := hs1.mul h12
  have hs := h22.sub hs2
  have hr1 := hI.mul h12
  have hr := hr1.mul hout
  have hc1 := hout.mul h21
  have hc := hc1.mul hI
  have ht1 := hr.mul h21
  have ht2 := ht1.mul hI
  have ht := hI.add ht2
  refine ⟨hinput.mono (by omega),hout.mono (by omega),hI.mono (by omega),
    hs1.mono (by omega),hs2.mono (by omega),hs.mono (by omega),
    hr1.mono (by omega),hr.mono (by omega),hc1.mono (by omega),hc.mono (by omega),
    ht1.mono (by omega),ht2.mono (by omega),ht.mono (by omega),
    hr.neg.mono (by omega),hc.neg.mono (by omega)⟩

/-- A depth-independent polynomial bound for all matrices evaluated during
the entire recursive inversion. No bound on intermediate values is assumed. -/
theorem efficientInverse_all_stages_height {d b : ℕ} (A : Matrix (Fin d) (Fin d) ℚ)
    (hA : A.PosDef) (hheight : MatrixHeight A b) {n : ℕ}
    (B : Matrix (Fin (n+1)) (Fin (n+1)) ℚ) (hB : SchurDescendant A B) :
    SchurStageHeight B (efficientInverse (inverseSchur B))
      (inverseHeight d b+5*inverseHeight d (inverseHeight d b)+2*n+3) := by
  have hin := (hB.height hA hheight).2
  have htail := (SchurDescendant.tail hB).height hA hheight
  have hout : MatrixHeight (efficientInverse (inverseSchur B)) (inverseHeight d b) := by
    rw [efficientInverse_correct _ _ (inverseSchur_pos B (hB.posDef hA))]
    exact htail.1
  exact schur_stage_height B (hB.posDef hA) _ hin hout

/-- The normal-equations extension has polynomial encoding bounds even for
nonsymmetric input matrices. -/
theorem efficientGeneralInverse_outer_height {d b : ℕ}
    (A : Matrix (Fin d) (Fin d) ℚ) (hu : IsUnit A) (hheight : MatrixHeight A b) :
    MatrixHeight (Aᵀ*A) (2*b+d) ∧
    MatrixHeight (efficientInverse (Aᵀ*A)) (inverseHeight d (2*b+d)) ∧
    MatrixHeight (efficientGeneralInverse A) (inverseHeight d (2*b+d)+b+d) := by
  have hg : MatrixHeight (Aᵀ*A) (2*b+d) := by
    simpa only [two_mul] using hheight.transpose.mul hheight
  have hi : MatrixHeight (efficientInverse (Aᵀ*A)) (inverseHeight d (2*b+d)) := by
    rw [efficientInverse_correct _ _ (rational_normal_positive A hu)]
    exact hg.inv (rational_normal_positive A hu).isUnit
  refine ⟨hg,hi,?_⟩
  have hm := hi.mul hheight.transpose
  have hc (M : Matrix (Fin d) (Fin d) ℚ) :
      rationalMatrixOfRows (rationalMatrixRows M)=M := by
    ext i j
    simp [rationalMatrixOfRows,rationalMatrixRows,Vector.get]
  change MatrixHeight (rationalMatrixOfRows (rationalMatrixRows
    (efficientInverse (Aᵀ*A)*Aᵀ))) _
  rwa [hc]

theorem efficientGeneralInverse_all_stages_height {d b : ℕ}
    (A : Matrix (Fin d) (Fin d) ℚ) (hu : IsUnit A) (hheight : MatrixHeight A b)
    {n : ℕ} (B : Matrix (Fin (n+1)) (Fin (n+1)) ℚ)
    (hB : SchurDescendant (Aᵀ*A) B) :
    SchurStageHeight B (efficientInverse (inverseSchur B))
      (inverseHeight d (2*b+d)+5*inverseHeight d (inverseHeight d (2*b+d))+2*n+3) := by
  exact efficientInverse_all_stages_height _ (rational_normal_positive A hu)
    (efficientGeneralInverse_outer_height A hu hheight).1 B hB

end Paper254
#print axioms Paper254.efficientInverse_all_stages_height
