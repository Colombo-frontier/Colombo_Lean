import GradientHessian.CanonicalSource
import GradientHessian.RawHierarchy
import GradientHessian.HigherHierarchyDimension
import GradientHessian.HigherHierarchyActivation
import GradientHessian.HigherHierarchyGap

/-! A concrete presampled hierarchy with canonical marked subspace and the
source's heterogeneous dimension allocation. Its probability and analytic
validity are proved from numerical parameter inequalities. -/

noncomputable section
namespace GradientHessian.PresampledConstruction
open MeasureTheory Matrix LowRank

structure Settings where
  J : ℕ
  r : ℕ
  κ : ℕ
  hJ : 4≤J
  hr : 1+4096*J^2≤r
  hκ : 18874368≤κ

def Settings.M (s : Settings) : ℕ := 4096*s.J^2+1
def Settings.D (s : Settings) : ℕ := (s.κ*s.r)*s.J
def Settings.columnsCount (s : Settings) : ℕ := s.D-s.κ*s.r

theorem Settings.marked_le (s : Settings) : s.r≤s.D :=
  CanonicalSource.marked_dimension_le (by have h := s.hJ; omega) (by have h := s.hκ; omega)

def Settings.P (s : Settings) : Matrix (Fin s.D) (Fin s.D) ℝ := CanonicalSource.projector s.marked_le
def Settings.B (s : Settings) : Matrix (Fin s.D) (Fin s.r) ℝ := CanonicalSource.columns s.marked_le

instance Settings.marked_nonzero (s : Settings) : NeZero s.r := ⟨by have h := s.hr; omega⟩

abbrev LowSpace (Cp : ℝ) (s : Settings) :=
  EuclideanSpace ℝ (Fin (AllocationParameters.lowDimension Cp s.M))

abbrev HighSpace (Cp : ℝ) (s : Settings) (j : ℕ) :=
  EuclideanSpace ℝ (Fin (Allocation.levelDimension (AllocationParameters.lowDimension Cp s.M)
    (AllocationParameters.cutoff s.M) (j+2)))

instance lowDimension_nonzero (Cp : ℝ) (s : Settings) :
    NeZero (AllocationParameters.lowDimension Cp s.M) :=
  ⟨by have h := AllocationParameters.lowDimension_ge_eight Cp s.M; omega⟩

instance highDimension_nonzero (Cp : ℝ) (s : Settings) (j : ℕ) :
    NeZero (Allocation.levelDimension (AllocationParameters.lowDimension Cp s.M)
      (AllocationParameters.cutoff s.M) (j+2)) := by
  constructor
  unfold Allocation.levelDimension
  split_ifs
  · exact NeZero.ne _
  · norm_num

abbrev Sample (Cp : ℝ) (s : Settings) (t : ℕ) :=
  RawHierarchy.Raw s.D s.columnsCount s.r s.J (LowSpace Cp s) (HighSpace Cp s) t

abbrev PhysicalSpace (Cp : ℝ) (s : Settings) (t : ℕ) :=
  HigherHierarchy.AllocatedSpace Cp s.D (4096*s.J^2) t

def law (Cp : ℝ) (s : Settings) (t : ℕ) : Measure (Sample Cp s t) :=
  RawHierarchy.law s.P t

instance matrixLaw_probability (s : Settings) :
    IsProbabilityMeasure (ConditionedSource.sourceLaw (n := s.columnsCount) s.P s.J) := by
  exact ConditionedSource.sourceLaw_probability s.hJ s.hr s.hκ rfl rfl _
    (CanonicalSource.projector_orthogonal _) (CanonicalSource.projector_rank _)

instance law_probability (Cp : ℝ) (s : Settings) (t : ℕ) : IsProbabilityMeasure (law Cp s t) :=
  RawHierarchy.law_probability s.P t

def coefficients (Cp : ℝ) (s : Settings) (t : ℕ) (x : Sample Cp s t) :
    HigherHierarchy.Data (EuclideanSpace ℝ (Fin s.D)) (LowSpace Cp s) (HighSpace Cp s) (4096*s.J^2) t :=
  RawHierarchy.assemble s.P s.B 0 t x

theorem coefficients_valid (Cp : ℝ) (s : Settings) (t : ℕ) :
    ∀ᵐ x ∂law Cp s t, HigherHierarchy.Valid _ _ _ _ t (coefficients Cp s t x) :=
  RawHierarchy.law_assemble_valid s.hJ (CanonicalSource.projector_orthogonal _)
    (P := s.P) s.B (CanonicalSource.columns_orthonormal _) (CanonicalSource.projector_columns _) 0 t

def objective (Cp K : ℝ) (s : Settings) (t : ℕ) (x : Sample Cp s t) : PhysicalSpace Cp s t → ℝ :=
  HigherHierarchy.scalar K t (coefficients Cp s t x)

theorem objective_contDiff {K : ℝ} (hK : 0<K) (Cp : ℝ) (s : Settings) (t : ℕ) (x : Sample Cp s t) :
    ContDiff ℝ 3 (objective Cp K s t x) :=
  HigherHierarchy.scalar_contDiff hK t _

theorem objective_gap {K : ℝ} (hK : 16≤K) (Cp : ℝ) (s : Settings) (t : ℕ) :
    ∀ᵐ x ∂law Cp s t, objective Cp K s t x 0 - sInf (Set.range (objective Cp K s t x)) ≤
      HigherHierarchy.gapConstant K * 8^(t+1) * s.M := by
  filter_upwards [coefficients_valid Cp s t] with x hx
  simpa only [objective, Settings.M, Nat.cast_add, Nat.cast_one] using
    HigherHierarchy.scalar_gap_source_height hK t _ hx

theorem source_allocation (Cp : ℝ) (s : Settings) (t : ℕ) :
    Module.finrank ℝ (PhysicalSpace Cp s t) = PhysicalDimension.count Cp s.D s.M (t+1) :=
  HigherHierarchy.allocated_finrank Cp s.D (4096*s.J^2) t

def Settings.ofScale (J κ : ℕ) (KA : ℝ) (hJ : 4≤J) (hκ : 18874368≤κ) (hKA : 1≤KA) : Settings where
  J := J
  r := ⌈KA*(1+4096*(J:ℝ)^2)⌉₊
  κ := κ
  hJ := hJ
  hκ := hκ
  hr := by
    have h := Nat.le_ceil (KA*(1+4096*(J:ℝ)^2))
    have hm : 0≤1+4096*(J:ℝ)^2 := by positivity
    have hc : (1+4096*(J:ℝ)^2)≤KA*(1+4096*(J:ℝ)^2) := by nlinarith
    exact_mod_cast hc.trans h

theorem ofScale_dimension {Cp KA : ℝ} (hCp : 0≤Cp) (hKA : 1≤KA)
    (J κ : ℕ) (hJ : 4≤J) (hκ : 18874368≤κ) (t : ℕ) :
    (Module.finrank ℝ (PhysicalSpace Cp (Settings.ofScale J κ KA hJ hκ hKA) t):ℝ) ≤
      PhysicalDimension.finalCoefficient Cp ((κ:ℝ)*(KA+1)) *
        ((1+4096*(J:ℝ)^2)^(3/2:ℝ)+Real.log (2+(8:ℝ)^(t+1))) := by
  have h := HigherHierarchy.construction_dimension_bound hCp (show 0≤KA by linarith) κ J t
  have hc : ((1+4096*J^2:ℕ):ℝ)=1+4096*(J:ℝ)^2 := by push_cast; rfl
  have hd : (Settings.ofScale J κ KA hJ hκ hKA).D =
      PhysicalDimension.numericalCount κ KA J (1+4096*J^2) := by
    dsimp [Settings.ofScale, Settings.D, PhysicalDimension.numericalCount]
    rw [hc]
  change (Module.finrank ℝ (HigherHierarchy.AllocatedSpace Cp
    (Settings.ofScale J κ KA hJ hκ hKA).D (4096*J^2) t):ℝ) ≤ _
  rw [hd]
  exact h

end GradientHessian.PresampledConstruction
