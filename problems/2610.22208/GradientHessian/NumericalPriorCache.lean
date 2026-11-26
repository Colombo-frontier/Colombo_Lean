import GradientHessian.NumericalPreprocessor
import GradientHessian.RawFactorCoefficients

/-! Exact values of a synthesized prior-readout table. These are deterministic
identities for the original raw factor; the table is not independent advice. -/

noncomputable section
namespace GradientHessian.NumericalPriorCache
open Classical Matrix HigherHierarchy NumericalCoefficientPatch NumericalPreprocessor

variable {d n r J : ℕ} {E : Type} {H : ℕ → Type} {Seed : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [∀ h,NormedAddCommGroup (H h)] [∀ h,InnerProductSpace ℝ (H h)]
  [MeasurableSpace E] [∀ h,MeasurableSpace (H h)] [MeasurableSpace Seed]

theorem marks_target (j : Fin (4096*J^2+1)) (w : Fin (4096*J^2) → EuclideanSpace ℝ (Fin r)) :
    marks j w j=0 :=
  congrArg Prod.fst ((ProductRearrangement.split j).apply_symm_apply (0,w))

theorem marks_succAbove (j : Fin (4096*J^2+1))
    (w : Fin (4096*J^2) → EuclideanSpace ℝ (Fin r)) (k : Fin (4096*J^2)) :
    marks j w (j.succAbove k)=w k :=
  congrArg (fun q : EuclideanSpace ℝ (Fin r) × (Fin (4096*J^2) → EuclideanSpace ℝ (Fin r)) => q.2 k)
    ((ProductRearrangement.split j).apply_symm_apply (0,w))

theorem marks_factor_other (t : ℕ) (i : LeafSlot t) (j k : Fin (4096*J^2+1))
    (x : RawHierarchy.Raw d n r J E H t × Seed) (hk : k≠j) :
    marks j (RawNumericalExperiment.factor t i j x).1.2.1 k=
      (RawLeafFactor.leafNumerical t x.1 i).2 k := by
  obtain ⟨q,rfl⟩ := Fin.exists_succAbove_eq hk
  rw [marks_succAbove,RawNumericalExperiment.factor_other_mark]

theorem coefficient_A (P : Matrix (Fin d) (Fin d) ℝ) (B : Matrix (Fin d) (Fin r) ℝ)
    (fallback : Fin d → ℝ) : ∀ t (i : LeafSlot t) (x : RawHierarchy.Raw d n r J E H t),
    (atLeaf t i (RawHierarchy.coefficients P B fallback t x)).1=
      LowRank.matrixEuclideanMap (MatrixGoodSpectrum.sourceMatrix P J (RawLeafFactor.leafNumerical t x i).1)
  | 0,_,_ => rfl
  | t+1,i,x => coefficient_A P B fallback t i.2 (x.1 i.1)

theorem coefficient_b (P : Matrix (Fin d) (Fin d) ℝ) (B : Matrix (Fin d) (Fin r) ℝ)
    (fallback : Fin d → ℝ) : ∀ t (i : LeafSlot t) (x : RawHierarchy.Raw d n r J E H t) (k : Fin (4096*J^2+1)),
    (atLeaf t i (RawHierarchy.coefficients P B fallback t x)).2.1 k=
      InverseGate.H₀ • LowRank.matrixEuclideanMap B ((RawLeafFactor.leafNumerical t x i).2 k)
  | 0,_,_,_ => rfl
  | t+1,i,x,k => coefficient_b P B fallback t i.2 (x.1 i.1) k

theorem coefficient_a (P : Matrix (Fin d) (Fin d) ℝ) (B : Matrix (Fin d) (Fin r) ℝ)
    (fallback : Fin d → ℝ) : ∀ t (i : LeafSlot t) (x : RawHierarchy.Raw d n r J E H t) (k : Fin (4096*J^2+1)),
    (atLeaf t i (RawHierarchy.coefficients P B fallback t x)).2.2.1 k=
      SourceOperator.readoutVector J P (RawLeafFactor.leafNumerical t x i).1 fallback
        (LowRank.matrixEuclideanMap B ((RawLeafFactor.leafNumerical t x i).2 k))
  | 0,_,_,_ => rfl
  | t+1,i,x,k => coefficient_a P B fallback t i.2 (x.1 i.1) k

def value (B : Matrix (Fin d) (Fin r) ℝ) (j : Fin (4096*J^2+1))
    (readout : (Fin d → ℝ) → Fin d → ℝ)
    (w : Fin (4096*J^2) → EuclideanSpace ℝ (Fin r)) (k : Fin (4096*J^2+1)) : EuclideanSpace ℝ (Fin d) :=
  (NumericalOrdinaryProcedure.coordinates d).symm
    (readout (NumericalOrdinaryProcedure.coordinates d (LowRank.matrixEuclideanMap B (marks j w k))))

def store (B : Matrix (Fin d) (Fin r) ℝ) (j : Fin (4096*J^2+1))
    (readout : (Fin d → ℝ) → Fin d → ℝ)
    (w : Fin (4096*J^2) → EuclideanSpace ℝ (Fin r)) : Store d J :=
  (fun k => decide (k<j),fun k => if k<j then value B j readout w k else 0)

theorem forcing_exact (P : Matrix (Fin d) (Fin d) ℝ) (B : Matrix (Fin d) (Fin r) ℝ)
    (fallback : Fin d → ℝ) (t : ℕ) (i : LeafSlot t) (j k : Fin (4096*J^2+1))
    (x : RawHierarchy.Raw d n r J E H t × Seed) (hk : k≠j) :
    forcing B j (RawNumericalExperiment.factor t i j x).1.2.1 k=
      (atLeaf t i (RawHierarchy.coefficients P B fallback t x.1)).2.1 k := by
  rw [forcing,marks_factor_other t i j k x hk,coefficient_b]

theorem prior_value_exact (P : Matrix (Fin d) (Fin d) ℝ) (B : Matrix (Fin d) (Fin r) ℝ)
    (fallback : Fin d → ℝ) (t : ℕ) (i : LeafSlot t) (j k : Fin (4096*J^2+1))
    (x : RawHierarchy.Raw d n r J E H t × Seed) (hk : k<j) :
    (store B j (ReadoutOracle.readout (ReadoutFilter.matrixUpper J) P
      (MatrixGoodSpectrum.sourceMatrix P J (RawLeafFactor.leafNumerical t x.1 i).1) fallback)
        (RawNumericalExperiment.factor t i j x).1.2.1).2 k=
      (atLeaf t i (RawHierarchy.coefficients P B fallback t x.1)).2.2.1 k := by
  simp only [store,if_pos hk,value,marks_factor_other t i j k x (ne_of_lt hk),coefficient_a]
  rfl

theorem store_target_zero (B : Matrix (Fin d) (Fin r) ℝ) (j : Fin (4096*J^2+1))
    (readout : (Fin d → ℝ) → Fin d → ℝ)
    (w : Fin (4096*J^2) → EuclideanSpace ℝ (Fin r)) : (store B j readout w).2 j=0 := by
  simp only [store,lt_self_iff_false,if_false]

theorem supplied_forcing_exact (P : Matrix (Fin d) (Fin d) ℝ) (B : Matrix (Fin d) (Fin r) ℝ)
    (fallback : Fin d → ℝ) (t : ℕ) (i : LeafSlot t) (j : Fin (4096*J^2+1))
    (x : RawHierarchy.Raw d n r J E H t × Seed) :
    Function.update (forcing B j (RawNumericalExperiment.factor t i j x).1.2.1) j
      (InverseGate.H₀ • LowRank.matrixEuclideanMap B (RawNumericalExperiment.factor t i j x).2.1)=
        (atLeaf t i (RawHierarchy.coefficients P B fallback t x.1)).2.1 := by
  funext k
  by_cases hk : k=j
  · subst k
    rw [Function.update_self,RawNumericalExperiment.factor_mark,coefficient_b]
  · rw [Function.update_of_ne hk]
    exact forcing_exact.{_,0} (E := E) (H := H) (Seed := Seed) P B fallback t i j k x hk

end GradientHessian.NumericalPriorCache
