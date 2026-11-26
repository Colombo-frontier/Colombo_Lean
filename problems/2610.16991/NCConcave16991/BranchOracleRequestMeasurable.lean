import NCConcave16991.BranchOracleRequest

/-! # Measurability of the finite mixed request interface -/

namespace NCConcave16991.BranchOracle
noncomputable section
open GlobalHard GlobalHardEuclidean

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000

theorem measurable_sigma_mk_const {I : Type*} {A : I → Type*} [∀ i, MeasurableSpace (A i)] (i : I) :
    Measurable (Sigma.mk i : A i → Sigma A) := by
  apply measurable_iff_le_map.mpr
  exact iInf_le (fun j ↦ (inferInstance : MeasurableSpace (A j)).map (Sigma.mk j)) i

theorem measurable_sigma_elim {I : Type*} {A : I → Type*} {X : Type*}
    [∀ i, MeasurableSpace (A i)] [MeasurableSpace X] (f : Sigma A → X)
    (hf : ∀ i, Measurable (fun a : A i ↦ f ⟨i, a⟩)) : Measurable f := by
  apply measurable_iff_comap_le.mpr
  apply le_iInf
  intro i
  apply MeasurableSpace.comap_le_iff_le_map.mp
  rw [MeasurableSpace.comap_comp]
  exact (hf i).comap_le

variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
variable (M m : ℕ)

theorem queryRequest_measurable [OpensMeasurableSpace (GlobalHard.Joint (MacroSpaces (ι := ι) E M m))]
    (t : Vertex M m) (slot : Fin 5) :
    Measurable (fun z : GlobalHard.Joint (MacroSpaces (ι := ι) E M m) ↦ queryRequest E M m z t slot) :=
  (measurable_sigma_mk_const t).comp (measurable_inr.comp (queryMark E M m t.val slot).continuous.measurable)

theorem forwardMatrixRequest_measurable (i : ι) (j : Fin M) (k : Fin (m + 1)) :
    Measurable (fun marks : InverseMarks (ι := ι) E M m ↦ forwardMatrixRequest E M m marks i j k) :=
  (measurable_sigma_mk_const (depthVertex M m j k.succ)).comp
    (measurable_inl.comp ((prependIsometry E _ i).continuous.measurable.comp
      ((measurable_pi_apply 3).comp (measurable_pi_apply (depthVertex M m j k.castSucc)))))

theorem transposeMatrixRequest_measurable (i : ι) (j : Fin M) (k : Fin (m + 1)) :
    Measurable (fun marks : InverseMarks (ι := ι) E M m ↦ transposeMatrixRequest E M m marks i j k) := by
  have hs : Continuous (slice E (j.val * (m + 1) + k.val) i) := by
    convert ((formalBranchFamily E (j.val * (m + 1) + k.val)).branch i).toContinuousLinearMap.adjoint.continuous using 1
    funext y
    exact (formalBranch_adjoint_apply E (j.val * (m + 1) + k.val) i y).symm
  exact (measurable_sigma_mk_const (depthVertex M m j k.castSucc)).comp
    (measurable_inl.comp (hs.measurable.comp
      ((measurable_pi_apply (if k.succ.val < m + 1 then 3 else 4)).comp
        (measurable_pi_apply (depthVertex M m j k.succ)))))

theorem sourceRequest_measurable (t : Vertex M m) :
    Measurable (sourceRequest (ι := ι) E M m t) := by
  have ht : Continuous (formalTarget (ι := ι) E t.val) := by
    exact (PiLp.continuous_toLp 2 _).comp (continuous_pi (fun _ ↦ continuous_const.smul continuous_id))
  exact (measurable_sigma_mk_const t).comp (measurable_inl.comp ht.measurable)

theorem outputRequest_measurable (t : Vertex M m) :
    Measurable (fun c : PrimalSpace (primalDimension (MacroSpaces (ι := ι) E M m)) ↦ outputRequest E M m c t) := by
  have hc : Continuous (fun c : PrimalSpace (primalDimension (MacroSpaces (ι := ι) E M m)) ↦ outputMark E M m t.val c) := by
    have hh : Continuous (fun c : PrimalSpace (primalDimension (MacroSpaces (ι := ι) E M m)) ↦
        queryMark E M m t.val 0 (atDual (MacroSpaces (ι := ι) E M m)
          ((primalCoordinates (MacroSpaces (ι := ι) E M m)).symm c) 0)) :=
      (queryMark E M m t.val 0).continuous.comp
      (((WithLp.prod_continuous_toLp 2 _ _).comp
        (((primalCoordinates (MacroSpaces (ι := ι) E M m)).symm.continuous).prodMk continuous_const)))
    exact (continuous_const (y := (1 / 20 : ℝ))).smul
      ((LocalizationRadial.radialCap_contDiff (by norm_num : (0 : ℝ) < 10)).continuous.comp hh)
  exact (measurable_sigma_mk_const t).comp (measurable_inr.comp hc.measurable)

end
end NCConcave16991.BranchOracle
