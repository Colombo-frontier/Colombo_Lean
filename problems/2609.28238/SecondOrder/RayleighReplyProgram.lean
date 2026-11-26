import SecondOrder.OjaTrajectoryProgram

open MeasureTheory
open scoped BigOperators InnerProductSpace Classical

namespace SecondOrder
noncomputable section

def rayleighReplyEstimate {d : ℕ} (P : Parameters) (ρ δ : ℝ) (v : Point d)
    (ys : RayleighSlot P ρ δ → Point d) : ℝ :=
  robustCenter (confidenceRepeats_pos δ)
    (fun j => (localBatchSize (P.hessianBound^2) ρ:ℝ)⁻¹ •
      ∑ i : Fin (localBatchSize (P.hessianBound^2) ρ), ⟪ys (j,i),v⟫_ℝ) (ρ/3)

theorem rayleighReplyEstimate_measurable {d : ℕ} (P : Parameters) (ρ δ : ℝ) :
    Measurable (fun w : Point d × (RayleighSlot P ρ δ → Point d) => rayleighReplyEstimate P ρ δ w.1 w.2) := by
  apply (robustCenter_measurable (confidenceRepeats_pos δ) (ρ/3)).comp
  apply measurable_pi_lambda
  intro j
  have hs : Measurable (fun w : Point d × (RayleighSlot P ρ δ → Point d) =>
      ∑ i : Fin (localBatchSize (P.hessianBound^2) ρ), ⟪w.2 (j,i),w.1⟫_ℝ) := by
    apply Finset.measurable_sum
    intro i hi
    have hi : Measurable (fun u : Point d × Point d => ⟪u.1,u.2⟫_ℝ) :=
      (continuous_fst.inner continuous_snd).measurable
    have hp : Measurable (fun w : Point d × (RayleighSlot P ρ δ → Point d) => (w.2 (j,i),w.1)) :=
      ((measurable_pi_apply (j,i)).comp measurable_snd).prodMk measurable_fst
    have hh := hi.comp hp
    exact hh
  exact hs.const_smul ((localBatchSize (P.hessianBound^2) ρ:ℝ)⁻¹)

theorem rayleighReplyEstimate_samples {Ω : Type} {d : ℕ} (P : Parameters)
    (f : Ω → Point d → ℝ) (x v : Point d) (ρ δ : ℝ) (w : LocalDraws Ω (P.hessianBound^2) ρ δ) :
    rayleighReplyEstimate P ρ δ v
      (fun i => hvpReply f (rayleighSampleCall P x v ρ δ w i).1 (.hvp x v))=
        rayleighEstimate P f x v ρ δ w :=
  (rayleighEstimate_eq_query_average P f x v ρ δ w).symm

def rayleighReplyFinish {d : ℕ} (P : Parameters) (γ δ : ℝ) (v : Point d)
    (ys : RayleighSlot P (γ/8) δ → Point d) : CurvatureReply d :=
  if ‖v‖=1 ∧ rayleighReplyEstimate P (γ/8) δ v ys≤-(5*γ/8) then .negative v else .certificate

theorem rayleighReplyFinish_measurable {d : ℕ} (P : Parameters) (γ δ : ℝ) :
    Measurable (fun w : Point d × (RayleighSlot P (γ/8) δ → Point d) => rayleighReplyFinish P γ δ w.1 w.2) := by
  apply Measurable.ite
  · exact (measurableSet_eq_fun measurable_fst.norm measurable_const).inter
      (measurableSet_le (rayleighReplyEstimate_measurable P (γ/8) δ) measurable_const)
  · exact curvatureNegative_measurable.comp measurable_fst
  · exact measurable_const

/-- The validator sees one Hessian-vector reply per slot and computes the
scalar Rayleigh robust estimate solely from those replies and its direction. -/
def rayleighValidationProgram {d : ℕ} (P : Parameters) (x v : Point d) (γ δ : ℝ) :
    OracleProgram (HvpQuery d) (Point d) (CurvatureReply d) :=
  OracleProgram.batch (Fintype.card (RayleighSlot P (γ/8) δ)) (fun _ => .hvp x v)
    (fun ys => rayleighReplyFinish P γ δ v (fun i => ys (Fintype.equivFin _ i)))

theorem rayleighValidationProgram_usesExactly {d : ℕ} (P : Parameters) (x v : Point d) (γ δ : ℝ) :
    OracleProgram.UsesExactly (localQueryCount (P.hessianBound^2) (γ/8) δ)
      (rayleighValidationProgram P x v γ δ) := by
  rw [←rayleighSampleCall_count]
  exact OracleProgram.batch_usesExactly _ _ _

theorem rayleighValidationProgram_measurable {d : ℕ} (P : Parameters) (γ δ : ℝ) :
    OracleProgram.MeasurableFamily (.grad 0) .certificate
      (fun w : Point d × Point d => rayleighValidationProgram P w.1 w.2 γ δ) := by
  apply OracleProgram.batch_measurable
  · intro i
    exact (hvpQueryMeasurableEquiv d).symm.measurable.comp
      (measurable_inr.comp (measurable_fst.prodMk measurable_snd))
  · have hm : Measurable (fun w : (Point d × Point d) ×
          (Fin (Fintype.card (RayleighSlot P (γ/8) δ)) → Point d) =>
          (w.1.2,fun i : RayleighSlot P (γ/8) δ => w.2 (Fintype.equivFin _ i))) := by
      apply measurable_fst.snd.prodMk
      apply measurable_pi_lambda
      intro i
      exact (measurable_pi_apply (Fintype.equivFin _ i)).comp measurable_snd
    have hh := (rayleighReplyFinish_measurable (d := d) P γ δ).comp hm
    exact hh

theorem rayleighValidationProgram_run {Ω : Type} {d : ℕ} (P : Parameters)
    (f : Ω → Point d → ℝ) (x v : Point d) (γ δ : ℝ)
    (w : LocalDraws Ω (P.hessianBound^2) (γ/8) δ) (zs : ℕ → Ω)
    (hz : ∀ i : RayleighSlot P (γ/8) δ,
      zs (Fintype.equivFin _ i)=(rayleighSampleCall P x v (γ/8) δ w i).1) :
    OracleProgram.run (.grad 0) (fun q z => hvpReply f z q) zs
      (rayleighValidationProgram P x v γ δ) (localQueryCount (P.hessianBound^2) (γ/8) δ)=
        .done (rayleighValidatedReply P f x v γ δ w) := by
  rw [←rayleighSampleCall_count]
  unfold rayleighValidationProgram
  rw [OracleProgram.batch_run]
  simp only [hz]
  rw [rayleighReplyFinish,rayleighReplyEstimate_samples]
  simp only [rayleighValidatedReply,RayleighAccept]
  split_ifs <;> rfl

end
end SecondOrder
