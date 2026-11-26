import Bilevel.TransportObserverGeometry
import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! Literal block disclosure geometry for polished `dt:lem:column`.
The bound is proved for every target vector orthogonal to the disclosed block,
then summed over arbitrary finite target columns. -/
noncomputable section
open scoped RealInnerProductSpace BigOperators
namespace Bilevel.PolishedBlockProjection
open ProjectionGeometry TransportObserver
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {ι : Type*} [Fintype ι]

def columnSpace (C : ι → E) : Submodule ℝ E := Submodule.span ℝ (Set.range C)

def blockEnergy (W : Submodule ℝ E) (C : ι → E) : ℝ := ∑ i, energy W (C i)


omit [FiniteDimensional ℝ E] [Fintype ι] in
theorem column_mem (C : ι → E) (i : ι) : C i ∈ columnSpace C :=
  Submodule.subset_span (Set.mem_range_self i)

omit [FiniteDimensional ℝ E] in
theorem inner_zero_columnSpace (C : ι → E) (z : E)
    (hz : ∀ i, ⟪z,C i⟫ = 0) (v : E) (hv : v ∈ columnSpace C) :
    ⟪z,v⟫ = 0 := by
  obtain ⟨a,rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hv
  simp only [inner_sum, real_inner_smul_right, hz, mul_zero, Finset.sum_const_zero]

theorem project_columnSpace (C : ι → E) (hC : Orthonormal ℝ C) (w : E) :
    project (columnSpace C) w = ∑ i, ⟪C i,w⟫ • C i := by
  classical
  apply Submodule.eq_orthogonalProjection_of_mem_of_inner_eq_zero
  · exact (Submodule.mem_span_range_iff_exists_fun ℝ).mpr ⟨_,rfl⟩
  · intro v hv
    apply inner_zero_columnSpace C (w-∑ i,⟪C i,w⟫ • C i) _ v hv
    intro i
    rw [inner_sub_left,hC.inner_left_fintype]
    simp [real_inner_comm]

theorem energy_columnSpace (C : ι → E) (hC : Orthonormal ℝ C) (w : E) :
    energy (columnSpace C) w = ∑ i, ⟪C i,w⟫^2 := by
  classical
  rw [energy,project_columnSpace C hC]
  rw [←real_inner_self_eq_norm_sq]
  simpa [pow_two] using hC.inner_sum (fun i => ⟪C i,w⟫) (fun i => ⟪C i,w⟫) Finset.univ

/-- The Frobenius projection energy bounds every reverse-angle coefficient. -/
theorem columnSpace_energy_of_mem (W : Submodule ℝ E) (C : ι → E)
    (hC : Orthonormal ℝ C) (w : E) (hw : w ∈ W) :
    energy (columnSpace C) w ≤ blockEnergy W C * ‖w‖^2 := by
  classical
  rw [energy_columnSpace C hC,blockEnergy,Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i _
  rw [inner_project_mem W (C i) w hw]
  have hc := pow_le_pow_left₀ (abs_nonneg ⟪project W (C i),w⟫)
    (abs_real_inner_le_norm (project W (C i)) w) 2
  simpa only [sq_abs,mul_pow,energy] using hc

/-- Exact block-revelation bound for a single target orthogonal to the block.
Here `blockEnergy` is precisely the squared Frobenius norm of `P_W C`. -/
theorem projection_block_bound (W : Submodule ℝ E) (C : ι → E)
    (hC : Orthonormal ℝ C) (he : blockEnergy W C < 1) (z : E)
    (hz : ∀ i, ⟪z,C i⟫ = 0) :
    energy (W ⊔ columnSpace C) z ≤ energy W z / (1-blockEnergy W C) := by
  let R := columnSpace C
  let T := W ⊔ R
  let p := project T z
  have hpT : p ∈ T := project_mem T z
  have hpinner (v : E) (hv : v ∈ R) : ⟪p,v⟫ = 0 := by
    have hvT : v ∈ T := (show R ≤ T from le_sup_right) hv
    have hzv : ⟪z,v⟫ = 0 := inner_zero_columnSpace C z hz v hv
    exact (inner_project_mem T z v hvT).symm.trans hzv
  have hpR : project R p = 0 := by
    apply Submodule.eq_orthogonalProjection_of_mem_of_inner_eq_zero R.zero_mem
    intro v hv
    simpa using hpinner v hv
  obtain ⟨w,hw,c,hc,heq⟩ := Submodule.mem_sup.mp hpT
  have hpres : p = residual R w := by
    have hh := congrArg (project R) heq
    rw [project_add,project_self R hc,hpR] at hh
    have hc' : c = -project R w := eq_neg_of_add_eq_zero_right hh
    rw [←heq,hc']
    simp only [ProjectionGeometry.residual,sub_eq_add_neg]
  have hwangle : (1-blockEnergy W C)*‖w‖^2 ≤ ‖p‖^2 := by
    have hb := columnSpace_energy_of_mem W C hC w hw
    have hr := residual_norm_square R w
    rw [←hpres] at hr
    change ‖p‖^2=‖w‖^2-energy (columnSpace C) w at hr
    nlinarith
  have hzinner : ⟪z,p⟫ = ‖p‖^2 := by
    simpa only [p,real_inner_self_eq_norm_sq] using inner_project T z z
  have hidentity : ‖p‖^2 = ⟪project W z,w⟫ := by
    rw [←hzinner,←heq,inner_add_right,inner_zero_columnSpace C z hz c hc,add_zero]
    exact inner_project_mem W z w hw
  have hcauchy : (‖p‖^2)^2 ≤ energy W z * ‖w‖^2 := by
    have hh := pow_le_pow_left₀ (abs_nonneg ⟪project W z,w⟫)
      (abs_real_inner_le_norm (project W z) w) 2
    rw [sq_abs,←hidentity] at hh
    simpa only [mul_pow,energy] using hh
  have hd : 0 < 1-blockEnergy W C := by linarith
  change ‖p‖^2 ≤ energy W z / (1-blockEnergy W C)
  apply (le_div_iff₀ hd).mpr
  by_cases hp0 : ‖p‖^2 = 0
  · rw [hp0,zero_mul]
    exact sq_nonneg _
  · have hpp : 0 < ‖p‖^2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm hp0)
    have hc1 := mul_le_mul_of_nonneg_left hcauchy hd.le
    have hc2 := mul_le_mul_of_nonneg_left hwangle (sq_nonneg ‖project W z‖)
    have hprod : (‖p‖^2*(1-blockEnergy W C))*‖p‖^2 ≤ energy W z*‖p‖^2 := by
      calc
        _ = (1-blockEnergy W C)*(‖p‖^2)^2 := by ring
        _ ≤ (1-blockEnergy W C)*(energy W z*‖w‖^2) := hc1
        _ = energy W z*((1-blockEnergy W C)*‖w‖^2) := by ring
        _ ≤ energy W z*‖p‖^2 := hc2
    exact (mul_le_mul_right hpp).mp hprod

/-- The precise finite-column Frobenius energy estimate in `dt:eq:column-block`.
Target columns may be arbitrary; their orthonormality in the paper is not
needed for this inequality. -/
theorem frameEnergy_block_bound {κ : Type*} (W : Submodule ℝ E) (C : ι → E)
    (hC : Orthonormal ℝ C) (he : blockEnergy W C < 1) (F : κ → E)
    (I : Finset κ) (horth : ∀ i ∈ I, ∀ j, ⟪F i,C j⟫ = 0) :
    frameEnergy (W ⊔ columnSpace C) F I ≤
      frameEnergy W F I / (1-blockEnergy W C) := by
  have hh := Finset.sum_le_sum (s:=I) (fun i hi =>
    projection_block_bound W C hC he (F i) (horth i hi))
  simpa only [Finset.sum_div,frameEnergy] using hh

/-- A matrix is represented by its finite family of columns. The hypothesis
`C^T F=0` is the displayed pairwise inner-product condition. This wrapper
has precisely the hypotheses of the polished paper's named-column lemma. -/
theorem disclosing_orthogonal_named_columns {κ : Type*} [Fintype κ]
    (W : Submodule ℝ E) (C : ι → E) (F : κ → E)
    (hC : Orthonormal ℝ C) (_hF : Orthonormal ℝ F)
    (hCF : ∀ j i, ⟪C j,F i⟫ = 0) (he : blockEnergy W C < 1) :
    blockEnergy (W ⊔ columnSpace C) F ≤ blockEnergy W F/(1-blockEnergy W C) := by
  classical
  have h := frameEnergy_block_bound W C hC he F Finset.univ
    (fun i _ j => by rw [real_inner_comm];exact hCF j i)
  simpa only [frameEnergy,blockEnergy] using h

/-- The exact single-unit-column consequence stated after the block estimate.
Nonnegativity of `e` is derived from the projection energy assumption. -/
theorem single_column_factor {κ : Type*} (W : Submodule ℝ E) (F : κ → E)
    (I : Finset κ) (v : E) (hv : ‖v‖=1) {e : ℝ} (he : e<1/2)
    (hp : energy W v≤e) (horth : ∀ i∈I,⟪F i,v⟫=0) :
    frameEnergy (W ⊔ Submodule.span ℝ {v}) F I ≤ (1+2*e)*frameEnergy W F I := by
  exact named_column_energy W F I v hv ((sq_nonneg ‖project W v‖).trans hp) he hp horth

/-- The column family defines the ordinary matrix action by finite linear
combination, so its linear-map range is the column space used above. -/
def columnMap (C : ι → E) : (ι → ℝ) →ₗ[ℝ] E where
  toFun a := ∑ i,a i • C i
  map_add' a b := by simp [add_smul,Finset.sum_add_distrib]
  map_smul' a b := by simp [Finset.smul_sum,smul_smul]

omit [FiniteDimensional ℝ E] in
theorem range_columnMap (C : ι → E) : LinearMap.range (columnMap C)=columnSpace C := by
  ext v
  constructor
  · rintro ⟨a,rfl⟩
    exact (Submodule.mem_span_range_iff_exists_fun ℝ).mpr ⟨a,rfl⟩
  · intro hv
    obtain ⟨a,ha⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hv
    exact ⟨a,ha⟩

/-- Explicit squared Frobenius norm, written as the sum of squared entries.
This definition avoids selecting one of mathlib's competing matrix norms. -/
def frobeniusSq {d : ℕ} (A : Fin d → ι → ℝ) : ℝ := ∑ a,∑ i,(A a i)^2

/-- In Euclidean coordinates `blockEnergy W C` is literally
`||P_W C||_F^2`, with the Frobenius norm expanded entrywise. -/
theorem blockEnergy_eq_frobeniusSq {d : ℕ}
    (W : Submodule ℝ (EuclideanSpace ℝ (Fin d))) (C : ι → EuclideanSpace ℝ (Fin d)) :
    blockEnergy W C = frobeniusSq (fun a i => (project W (C i)) a) := by
  classical
  simp only [blockEnergy,energy,PiLp.norm_sq_eq_of_L2,Real.norm_eq_abs,sq_abs,frobeniusSq]
  exact Finset.sum_comm

/-- Source-facing range-of-matrix form of the named-column theorem. -/
theorem matrix_range_disclosure {κ : Type*} [Fintype κ]
    (W : Submodule ℝ E) (C : ι → E) (F : κ → E)
    (hC : Orthonormal ℝ C) (hF : Orthonormal ℝ F)
    (hCF : ∀ j i,⟪C j,F i⟫=0) (he : blockEnergy W C<1) :
    blockEnergy (W ⊔ LinearMap.range (columnMap C)) F ≤
      blockEnergy W F/(1-blockEnergy W C) := by
  rw [range_columnMap]
  exact disclosing_orthogonal_named_columns W C F hC hF hCF he

end Bilevel.PolishedBlockProjection
