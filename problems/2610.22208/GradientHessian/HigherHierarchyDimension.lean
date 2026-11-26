import GradientHessian.HigherHierarchySpace
import GradientHessian.PhysicalDimension

/-! Finite dimension of the actual shared physical hierarchy. The count
contains one lower space and eight parent vectors at each height. -/

noncomputable section
namespace GradientHessian.HigherHierarchy
universe u
open EuclideanRegisters

section Finrank
variable {F E : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ F] [FiniteDimensional ℝ E]

theorem registers_finrank (n : ℕ) :
    Module.finrank ℝ (Registers E n) = n*Module.finrank ℝ E := by
  change Module.finrank ℝ (Fin n → E) = _
  rw [Module.finrank_pi_fintype]
  simp

theorem innerSpace_finrank (m k : ℕ) :
    Module.finrank ℝ (InnerCoordinates.Space F E m k) =
      Module.finrank ℝ F + m*k*Module.finrank ℝ E := by
  change Module.finrank ℝ (F × Registers (Registers E k) m) = _
  rw [Module.finrank_prod, registers_finrank, registers_finrank]
  ring

theorem layer_finrank : Module.finrank ℝ (Layer F E) =
    Module.finrank ℝ F + 8*Module.finrank ℝ E := by
  change Module.finrank ℝ (F × Registers E 8) = _
  rw [Module.finrank_prod, registers_finrank]

theorem firstSpace_finrank (m : ℕ) : Module.finrank ℝ (FirstHeight.SourceSpace F E m) =
    Module.finrank ℝ F + (m+1)*(Inner.absoluteDepth+2)*Module.finrank ℝ E +
      8*(FirstHeight.depth (m+1)+2)*Module.finrank ℝ E := by
  change Module.finrank ℝ (InnerCoordinates.Space (Leaf.Space F E (m+1)) E 8 (FirstHeight.depth (m+1)+2)) = _
  rw [innerSpace_finrank]
  change Module.finrank ℝ (InnerCoordinates.Space F E (m+1) (Inner.absoluteDepth+2)) + _ = _
  rw [innerSpace_finrank]
end Finrank

variable (Y E : Type u) (H : ℕ → Type u) (m : ℕ)
variable [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [∀ t, NormedAddCommGroup (H t)] [∀ t, InnerProductSpace ℝ (H t)]
  [FiniteDimensional ℝ Y] [FiniteDimensional ℝ E] [∀ t, FiniteDimensional ℝ (H t)]

def spaceFiniteDimensional : (t : ℕ) → FiniteDimensional ℝ (Space Y E H m t)
  | 0 => inferInstanceAs (FiniteDimensional ℝ (FirstHeight.SourceSpace Y E m))
  | t+1 => by
    letI := spaceFiniteDimensional t
    exact inferInstanceAs (FiniteDimensional ℝ (Layer (Space Y E H m t) (H t)))
attribute [instance] spaceFiniteDimensional

theorem space_finrank (t : ℕ) : Module.finrank ℝ (Space Y E H m t) =
    Module.finrank ℝ Y + (m+1)*(Inner.absoluteDepth+2)*Module.finrank ℝ E +
      8*(FirstHeight.depth (m+1)+2)*Module.finrank ℝ E +
      8*∑ j ∈ Finset.range t, Module.finrank ℝ (H j) := by
  induction t with
  | zero => simpa using (firstSpace_finrank (F := Y) (E := E) m)
  | succ t ih =>
    change Module.finrank ℝ (Layer (Space Y E H m t) (H t)) = _
    rw [layer_finrank, ih, Finset.sum_range_succ]
    ring

/-- The low registers all have p_low dimensions; height j+2 has exactly
the allocated p_(j+2) dimensions, independently of the number of nodes. -/
abbrev AllocatedSpace (Cp : ℝ) (D m t : ℕ) :=
  Space (EuclideanSpace ℝ (Fin D))
    (EuclideanSpace ℝ (Fin (AllocationParameters.lowDimension Cp (m+1))))
    (fun j => EuclideanSpace ℝ (Fin (Allocation.levelDimension
      (AllocationParameters.lowDimension Cp (m+1)) (AllocationParameters.cutoff (m+1)) (j+2)))) m t

theorem allocated_finrank (Cp : ℝ) (D m t : ℕ) :
    Module.finrank ℝ (AllocatedSpace Cp D m t) = PhysicalDimension.count Cp D (m+1) (t+1) := by
  rw [space_finrank]
  simp only [finrank_euclideanSpace_fin]
  unfold PhysicalDimension.count
  congr 1
  congr 1
  rw [← Nat.Ico_succ_right, Finset.sum_Ico_eq_sum_range]
  simp only [show t+1+1-2=t by omega, Nat.add_comm 2]

/-- An actual Euclidean realization with the displayed count, preserving
the physical norm exactly. -/
def allocatedEuclideanEquiv (Cp : ℝ) (D m t : ℕ) :
    AllocatedSpace Cp D m t ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (PhysicalDimension.count Cp D (m+1) (t+1))) :=
  ((stdOrthonormalBasis ℝ (AllocatedSpace Cp D m t)).reindex
    (finCongr (allocated_finrank Cp D m t))).repr

theorem allocatedEuclideanEquiv_norm (Cp : ℝ) (D m t : ℕ) (Z : AllocatedSpace Cp D m t) :
    ‖allocatedEuclideanEquiv Cp D m t Z‖ = ‖Z‖ :=
  (allocatedEuclideanEquiv Cp D m t).norm_map Z

theorem allocated_dimension_bound {Cp Cnum : ℝ} (hCp : 0≤Cp) (hnum : 0≤Cnum)
    (D m t : ℕ) (hD : (D:ℝ)≤Cnum*(m+1)*Real.sqrt (m+1)) :
    (Module.finrank ℝ (AllocatedSpace Cp D m t):ℝ) ≤ PhysicalDimension.finalCoefficient Cp Cnum *
      ((m+1:ℝ)^(3/2:ℝ)+Real.log (2+(8:ℝ)^(t+1))) := by
  rw [allocated_finrank]
  simpa only [Nat.cast_add, Nat.cast_one] using
    PhysicalDimension.source_dimension_bound hCp hnum (M := m+1) (D := D) (by omega)
      (by simpa only [Nat.cast_add, Nat.cast_one] using hD) (t+1)

abbrev ConstructionSpace (Cp : ℝ) (κ : ℕ) (KA : ℝ) (J t : ℕ) :=
  AllocatedSpace Cp (PhysicalDimension.numericalCount κ KA J (1+4096*J^2)) (4096*J^2) t

theorem construction_finrank (Cp : ℝ) (κ : ℕ) (KA : ℝ) (J t : ℕ) :
    Module.finrank ℝ (ConstructionSpace Cp κ KA J t) =
      PhysicalDimension.count Cp (PhysicalDimension.numericalCount κ KA J (1+4096*J^2)) (1+4096*J^2) (t+1) := by
  rw [allocated_finrank, Nat.add_comm (4096*J^2) 1]

theorem construction_dimension_bound {Cp KA : ℝ} (hCp : 0≤Cp) (hKA : 0≤KA) (κ J t : ℕ) :
    (Module.finrank ℝ (ConstructionSpace Cp κ KA J t):ℝ) ≤
      PhysicalDimension.finalCoefficient Cp ((κ:ℝ)*(KA+1)) *
        ((1+4096*(J:ℝ)^2)^(3/2:ℝ)+Real.log (2+(8:ℝ)^(t+1))) := by
  rw [construction_finrank]
  exact PhysicalDimension.source_construction_dimension hCp hKA κ J (t+1)

end GradientHessian.HigherHierarchy
