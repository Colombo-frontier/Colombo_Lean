import GradientHessian.NalenOrdinaryUpper

/-! Zero-dimensional objectives need no queries. This removes any implicit
positive-dimension convention from the source ordinary-only upper bound. -/

noncomputable section
namespace GradientHessian.NalenPolicy
open Model MeasureTheory
open scoped ENNReal

def zeroProgram : ClockedOracle.Program (PUnit : Type) (PUnit : Type)
    (Point 0) (OrdinaryReply 0) (RichReply 0) where
  length := 0
  kind := fun _ => 0
  initial := fun _ => PUnit.unit
  point := fun _ _ => 0
  output := fun _ => 0
  think := fun _ => id
  ordinaryNext := fun _ => Prod.fst
  richNext := fun _ => Prod.fst
  initial_measurable := measurable_const
  point_measurable := fun _ => measurable_const
  output_measurable := measurable_const
  think_measurable := fun _ => measurable_id
  ordinaryNext_measurable := fun _ => measurable_fst
  richNext_measurable := fun _ => measurable_fst

def zeroAlgorithm : Algorithm 0 where
  Seed := PUnit
  State := ℕ × PUnit
  seedSpace := inferInstance
  stateSpace := inferInstance
  seedLaw := Measure.dirac PUnit.unit
  probability := inferInstance
  policy := zeroProgram.policy

theorem zeroAlgorithm_guarantees (T : ℝ) : zeroAlgorithm.Guarantees T 0 0 := by
  intro f hf
  refine ⟨?_,?_,?_⟩
  · exact zeroProgram.policy.terminatesAlmostSurely_of_terminates _ _ (Measure.dirac PUnit.unit)
      (zeroProgram.terminates _ _)
  · have h := zeroProgram.hasCaps (ordinaryOracle f) (richOracle f)
    simpa only [ClockedOracle.Program.count,zeroProgram,Finset.sum_range_zero] using h
  · have hs : zeroProgram.policy.success (ordinaryOracle f) (richOracle f) (stationary f)=Set.univ := by
      apply Set.eq_univ_of_forall
      intro seed
      refine ⟨0,zeroProgram.halt _ _ seed,?_⟩
      apply (stationary_iff_gradient f _).2
      have hz : gradient f (zeroProgram.policy.output
          (zeroProgram.policy.run (ordinaryOracle f) (richOracle f) 0 seed))=0 := Subsingleton.elim _ _
      rw [hz,norm_zero]
      norm_num
    change (2/3:ℝ≥0∞)≤(Measure.dirac PUnit.unit)
      (zeroProgram.policy.success (ordinaryOracle f) (richOracle f) (stationary f))
    rw [hs]
    simp only [MeasureTheory.measure_univ]
    exact (ENNReal.div_le_iff (by norm_num) (by norm_num)).2 (by norm_num)

theorem source_ordinary_upper_all_dimensions (d : ℕ) {T : ℝ} (hT : 1≤T) :
    ∃ (A : Algorithm d) (G : ℕ), A.Guarantees T G 0 ∧
      (G:ℝ)≤4096*((d:ℝ)+T*(d:ℝ)^((1:ℝ)/3)) := by
  cases d with
  | zero =>
    refine ⟨zeroAlgorithm,0,zeroAlgorithm_guarantees T,?_⟩
    norm_num
  | succ d => exact source_ordinary_upper hT (by omega)

theorem source_ordinary_complexity_upper_all_dimensions (d : ℕ) {T : ℝ} (hT : 1≤T) :
    complexity 0 d T≤ENNReal.ofReal (4096*((d:ℝ)+T*(d:ℝ)^((1:ℝ)/3))) := by
  obtain ⟨A,G,hA,hG⟩ := source_ordinary_upper_all_dimensions d hT
  exact (complexity_le A hA).trans
    (by simpa only [ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal hG)

end GradientHessian.NalenPolicy
