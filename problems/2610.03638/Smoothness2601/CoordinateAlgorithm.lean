import Smoothness2601.CoordinateOracle

/-! Exact conjugacy of arbitrary adaptive algorithms under a lower-coordinate
isometry. Public memory, number of calls and output point are unchanged. -/
noncomputable section
open MeasureTheory ProbabilityTheory Bilevel.PrimitiveGeometry Bilevel.Stateful
namespace Smoothness2601.CoordinateAlgorithm
open CoordinateGeometry

variable {X Y Z : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]
  [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X]
  [MeasurableSpace Y] [BorelSpace Y] [SecondCountableTopology Y]
  [MeasurableSpace Z] [BorelSpace Z] [SecondCountableTopology Z]
  (A : Adaptive.Algorithm X Z) (e : Z ≃ₗᵢ[ℝ] Y)

def pull : Adaptive.Algorithm X Y where
  Memory := A.Memory
  memoryMeasurable := inferInstance
  initialLaw := A.initialLaw.comap (fun p => (p.1,e.symm p.2))
    (measurable_fst.prodMk (e.symm.continuous.measurable.comp measurable_snd))
  initialMarkov := inferInstance
  query k m := CoordinateOracle.query e (A.query k m)
  query_measurable k := (CoordinateOracle.query_measurable e).comp (A.query_measurable k)
  update k z := A.update k (z.1,(joint e).symm z.2)
  update_measurable k := (A.update_measurable k).comp
    (measurable_fst.prodMk ((joint e).symm.continuous.measurable.comp measurable_snd))
  output := A.output
  output_measurable := A.output_measurable

variable {b : Budgets} (P : Population (X := X) (Y := Y) b)
  {H : Type} [MeasurableSpace H] (O : Adaptive.Oracle P H)

omit [BorelSpace X] [SecondCountableTopology Y] in
theorem step (k : ℕ) :
    Adaptive.step (pull A e) O k = Adaptive.step A (CoordinateOracle.transport P e O) k := by
  ext1 s
  rw [Adaptive.step,Adaptive.step]
  erw [
    KernelMap.dependent_apply _ _ (Adaptive.finishAt_measurable (pull A e) (H := H) k) s,
    KernelMap.dependent_apply _ _ (Adaptive.finishAt_measurable A (H := H) k) (show A.Memory × H from s)]
  simp only [Kernel.comap_apply,Adaptive.inputAt]
  change (O.law (CoordinateOracle.query e (A.query k s.1),s.2)).map
      (fun z => Adaptive.finishAt (pull A e) k (s,z)) =
    (CoordinateOracle.law P e O (A.query k s.1,s.2)).map (fun z => Adaptive.finishAt A k (s,z))
  have hfinish : Measurable (fun z : Joint X Z × H => Adaptive.finishAt A k (s,z)) :=
    (Adaptive.finishAt_measurable A k).comp (measurable_const.prodMk measurable_id)
  rw [CoordinateOracle.law_apply,Measure.map_map hfinish (CoordinateOracle.reply_measurable e)]
  rfl

omit [BorelSpace X] [SecondCountableTopology Y] in
theorem execution (n : ℕ) :
    Adaptive.execution (pull A e) O n = Adaptive.execution A (CoordinateOracle.transport P e O) n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Adaptive.execution,Adaptive.execution,step,ih]

omit [CompleteSpace X] [CompleteSpace Y] [CompleteSpace Z]
  [BorelSpace X] [SecondCountableTopology X] [SecondCountableTopology Y] [SecondCountableTopology Z] in
theorem initialState (h : H) (x : X) (y : Y) :
    Adaptive.initialState (pull A e) h (x,y) = Adaptive.initialState A h (x,e.symm y) := by
  have hm : Measurable (fun m : A.Memory => (m,h)) := measurable_id.prodMk measurable_const
  have hmp : Measurable (fun m : (pull A e).Memory => (m,h)) := measurable_id.prodMk measurable_const
  rw [Adaptive.initialState,Adaptive.initialState,
    Kernel.map_apply _ hmp,Kernel.map_apply _ hm]
  rfl

omit [BorelSpace X] [SecondCountableTopology Y] in
theorem outputKernel (n : ℕ) (h : H) (x : X) (y : Y) :
    Adaptive.outputKernel (pull A e) O n h (x,y) =
      Adaptive.outputKernel A (CoordinateOracle.transport P e O) n h (x,e.symm y) := by
  have hm : Measurable (fun s : A.Memory × H => A.output s.1) :=
    A.output_measurable.comp measurable_fst
  have hmp : Measurable (fun s : (pull A e).Memory × H => (pull A e).output s.1) :=
    (pull A e).output_measurable.comp measurable_fst
  rw [Adaptive.outputKernel,Adaptive.outputKernel,
    Kernel.map_apply _ hmp,Kernel.map_apply _ hm,execution]
  congr 1
  rw [Kernel.comp_apply,Kernel.comp_apply,initialState]
  rfl

variable [FiniteDimensional ℝ Y] [FiniteDimensional ℝ Z]

omit [BorelSpace X] [SecondCountableTopology Y] in
theorem expectedNorm (n : ℕ) (h : H) (x : X) (y : Y) :
    Adaptive.expectedNorm (pull A e) O n h x y =
      Adaptive.expectedNorm A (CoordinateOracle.transport P e O) n h x (e.symm y) := by
  unfold Adaptive.expectedNorm
  rw [outputKernel,CoordinatePopulation.objective]

omit [BorelSpace X] [SecondCountableTopology Y] in
theorem succeeds (n : ℕ) (ε : ℝ) (h : H) (x : X) (y : Y)
    (hs : Adaptive.Succeeds A (CoordinateOracle.transport P e O) n ε h x (e.symm y)) :
    Adaptive.Succeeds (pull A e) O n ε h x y := by
  unfold Adaptive.Succeeds at hs ⊢
  rwa [expectedNorm]

end Smoothness2601.CoordinateAlgorithm
