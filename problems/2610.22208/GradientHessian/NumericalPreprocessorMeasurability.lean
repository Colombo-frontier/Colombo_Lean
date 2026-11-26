import GradientHessian.NumericalPreprocessor

noncomputable section
namespace GradientHessian.NumericalPreprocessor
open Classical HigherHierarchy HierarchyAddresses CensoredHierarchy FrontierState TaskState
  ComparisonController ComparisonControllerReplay ControllerMeasurable ControllerPolicyDriver
  GeometricRepair NumericalCachedOracle

variable {d n r J ell : ℕ} {E : Type} {H : ℕ → Type}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [∀ h,NormedAddCommGroup (H h)] [∀ h,InnerProductSpace ℝ (H h)]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  [∀ h,MeasurableSpace (H h)] [∀ h,BorelSpace (H h)] [∀ h,FiniteDimensional ℝ (H h)]
variable (P : Matrix (Fin d) (Fin d) ℝ) (B : Matrix (Fin d) (Fin r) ℝ) (fallback : Fin d → ℝ)
  (t : ℕ) (leaf : Leaf (t+1))
variable [MeasurableSpace (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t)]
  [BorelSpace (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t)]
  [MeasurableSpace (ℝ × (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t →L[ℝ] ℝ))]
  [BorelSpace (ℝ × (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t →L[ℝ] ℝ))]
  [MeasurableSpace (ℝ × (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t →L[ℝ] ℝ) ×
    (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t →L[ℝ]
      Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t →L[ℝ] ℝ))]
  [BorelSpace (ℝ × (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t →L[ℝ] ℝ) ×
    (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t →L[ℝ]
      Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t →L[ℝ] ℝ))]
variable {Seed S : Type*} [MeasurableSpace Seed] [MeasurableSpace S]
variable (policy : Machine.Policy Seed S (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t)
  (ℝ × (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t →L[ℝ] ℝ))
  (ℝ × (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t →L[ℝ] ℝ) ×
    (Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t →L[ℝ]
      Space (EuclideanSpace ℝ (Fin d)) E H (4096*J^2) t →L[ℝ] ℝ)))

theorem marks_measurable (j : Fin (4096*J^2+1)) : Measurable (marks (r := r) j) :=
  (ProductRearrangement.split j).symm.measurable.comp (measurable_const.prodMk measurable_id)

theorem forcing_measurable (j : Fin (4096*J^2+1)) : Measurable (forcing B j) := by
  apply measurable_pi_lambda
  intro k
  exact measurable_const.smul ((LowRank.matrixEuclideanMap B).continuous.measurable.comp
    ((measurable_pi_apply k).comp (marks_measurable j)))

theorem cache_measurable (j : Fin (4096*J^2+1)) :
    Measurable (cache (n := n) (ell := ell) (E := E) (H := H) (Seed := Seed) (S := S) B t j) :=
  ((forcing_measurable B j).comp (measurable_fst.comp measurable_fst)).prodMk
    (measurable_snd.comp (measurable_fst.comp measurable_snd))

theorem index_measurable (j : Fin (4096*J^2+1)) :
    Measurable (index (d := d) (n := n) (r := r) (ell := ell) (E := E) (H := H) (Seed := Seed) (S := S) t leaf j) := by
  have hm : Measurable (fun s : RuntimeState (d := d) (n := n) (r := r) (J := J)
      (ell := ell) (E := E) (H := H) (Seed := Seed) (S := S) t =>
      (s.2.1.1,ControllerDriverMonotonicity.stateOf s.2.2)) :=
    (measurable_fst.comp (measurable_fst.comp measurable_snd)).prodMk
      (NumericalDriverInstructions.stateOf_measurable.comp (measurable_snd.comp measurable_snd))
  have hh := (measurable_of_countable (fun q : (Fin (4096*J^2+1) → Bool) × State (t+1) (4096*J^2+1) ell =>
    NumericalDriverInstructions.readoutIndex leaf j q.1 q.2)).comp hm
  simpa only [Function.comp_def,index] using hh

theorem halt_measurable (j : Fin (4096*J^2+1)) :
    Measurable (halt (d := d) (n := n) (r := r) (ell := ell) (E := E) (H := H) (Seed := Seed) (S := S) t leaf j) :=
  (measurable_of_countable (fun q : Bool × Bool => q.1 || q.2)).comp
    ((NumericalDriverInstructions.finished_measurable.comp (measurable_snd.comp measurable_snd)).prodMk
      ((measurable_of_countable (markSupplied leaf j)).comp
        (NumericalDriverInstructions.stateOf_measurable.comp (measurable_snd.comp measurable_snd))))

theorem mode_measurable (j : Fin (4096*J^2+1)) :
    Measurable (mode (d := d) (n := n) (r := r) (ell := ell) (E := E) (H := H) (Seed := Seed) (S := S) t leaf j) :=
  (measurable_of_countable (fun q : Bool × Option (Fin (4096*J^2+1)) × Bool =>
    if q.1 then (0 : Fin 4) else if q.2.1.isSome then 3 else if q.2.2 then 2 else 1)).comp
    ((halt_measurable (d := d) (n := n) (r := r) (ell := ell) (E := E) (H := H) (Seed := Seed) (S := S) t leaf j).prodMk
      ((index_measurable t leaf j).prodMk
        ((NumericalDriverInstructions.product_measurable leaf (markSupplied leaf j)).comp (measurable_snd.comp measurable_snd))))

theorem query_measurable :
    Measurable (query (d := d) (n := n) (r := r) (J := J) (ell := ell) (E := E) (H := H) (Seed := Seed) (S := S) t) :=
  (NumericalOrdinaryProcedure.coordinates d).continuous.measurable.comp
    ((CensoredOracle.numericalMap (Y := EuclideanSpace ℝ (Fin d)) (E := E) (H := H) (m := 4096*J^2) t).continuous.measurable.comp
      (NumericalDriverInstructions.point_measurable.comp (measurable_snd.comp measurable_snd)))

theorem stepReply_measurable {K : ℝ} (hK : 0<K) (j : Fin (4096*J^2+1)) :
    Measurable (fun q : RuntimeState (d := d) (n := n) (r := r) (J := J) (ell := ell) (E := E) (H := H) (Seed := Seed) (S := S) t × (Fin d → ℝ) =>
      stepReply P B fallback t leaf policy K j q.1 q.2) := by
  have hm : Measurable (fun q : RuntimeState (d := d) (n := n) (r := r) (J := J) (ell := ell) (E := E) (H := H) (Seed := Seed) (S := S) t × (Fin d → ℝ) =>
      (((q.1.1.2.1,cache B t j q.1),(NumericalOrdinaryProcedure.coordinates d).symm q.2),q.1.2.2)) := by
    apply Measurable.prodMk
    · apply Measurable.prodMk
      · apply Measurable.prodMk
        · fun_prop
        · exact (cache_measurable (n := n) (ell := ell) (E := E) (H := H) (Seed := Seed) (S := S) B t j).comp measurable_fst
      · exact (NumericalOrdinaryProcedure.coordinates d).symm.continuous.measurable.comp measurable_snd
    · fun_prop
  have hr := (NumericalRuntime.advance_measurable (n := n) P B fallback t leaf policy hK (markSupplied leaf j)).comp hm
  exact (measurable_fst.comp measurable_fst).prodMk
    ((measurable_fst.comp (measurable_snd.comp measurable_fst)).prodMk hr)

theorem requestedMark_measurable (j : Fin (4096*J^2+1)) :
    Measurable (requestedMark (n := n) (ell := ell) (E := E) (H := H) (Seed := Seed) (S := S) B t leaf j) := by
  let f : (Fin (4096*J^2) → EuclideanSpace ℝ (Fin r)) × Option (Fin (4096*J^2+1)) → (Fin d → ℝ) :=
    fun q => match q.2 with
      | none => 0
      | some k => NumericalOrdinaryProcedure.coordinates d (LowRank.matrixEuclideanMap B (marks j q.1 k))
  have hf : Measurable f := by
    apply measurable_from_prod_countable
    intro k
    cases k with
    | none => exact measurable_const
    | some k =>
      exact (NumericalOrdinaryProcedure.coordinates d).continuous.measurable.comp
        ((LowRank.matrixEuclideanMap B).continuous.measurable.comp ((measurable_pi_apply k).comp (marks_measurable j)))
  exact hf.comp ((measurable_fst.comp measurable_fst).prodMk (index_measurable t leaf j))

theorem accept_measurable (j : Fin (4096*J^2+1)) :
    Measurable (fun q : RuntimeState (d := d) (n := n) (r := r) (J := J) (ell := ell) (E := E) (H := H) (Seed := Seed) (S := S) t × (Fin d → ℝ) =>
      accept t leaf j q.1 q.2) := by
  let f : (RuntimeState (d := d) (n := n) (r := r) (J := J) (ell := ell) (E := E) (H := H) (Seed := Seed) (S := S) t × (Fin d → ℝ)) ×
      Option (Fin (4096*J^2+1)) → RuntimeState (d := d) (n := n) (r := r) (J := J) (ell := ell) (E := E) (H := H) (Seed := Seed) (S := S) t :=
    fun q => match q.2 with
      | none => q.1.1
      | some k => (q.1.1.1,(Function.update q.1.1.2.1.1 k true,
          Function.update q.1.1.2.1.2 k ((NumericalOrdinaryProcedure.coordinates d).symm q.1.2)),q.1.1.2.2)
  have hf : Measurable f := by
    apply measurable_from_prod_countable
    intro k
    cases k with
    | none => exact measurable_fst
    | some k =>
      apply Measurable.prodMk
      · fun_prop
      · apply Measurable.prodMk
        · apply Measurable.prodMk
          · have hm : Measurable (fun q : RuntimeState (d := d) (n := n) (r := r) (J := J)
                (ell := ell) (E := E) (H := H) (Seed := Seed) (S := S) t × (Fin d → ℝ) =>
                (q.1.2.1.1,true)) := by fun_prop
            have hh := (measurable_update' (a := k)).comp hm
            simpa only [Function.comp_def] using hh
          · have hm : Measurable (fun q : RuntimeState (d := d) (n := n) (r := r) (J := J)
                (ell := ell) (E := E) (H := H) (Seed := Seed) (S := S) t × (Fin d → ℝ) =>
                (q.1.2.1.2,(NumericalOrdinaryProcedure.coordinates d).symm q.2)) := by
              apply Measurable.prodMk
              · fun_prop
              · exact (NumericalOrdinaryProcedure.coordinates d).symm.continuous.measurable.comp measurable_snd
            have hh := (measurable_update' (a := k)).comp hm
            simpa only [Function.comp_def] using hh
        · fun_prop
  exact hf.comp (measurable_id.prodMk ((index_measurable t leaf j).comp measurable_fst))

theorem initial_measurable (N : ℕ) :
    Measurable (initial (n := n) (r := r) (ell := ell) (E := E) (H := H) t policy N) :=
  measurable_id.prodMk ((measurable_const.prodMk measurable_const).prodMk
    ((ControllerPolicyDriver.initial_measurable (A := Action t (4096*J^2)) policy N TaskState.initial).comp
      (measurable_snd.comp measurable_snd)))

end GradientHessian.NumericalPreprocessor
