import SecondOrder.OracleBatchProgram
import SecondOrder.HvpAlgorithmSimulation
import SecondOrder.EpochAnchorCost

open MeasureTheory
open scoped BigOperators

namespace SecondOrder
noncomputable section

abbrev LocalReplySlot (V ρ δ : ℝ) := Fin (confidenceRepeats δ) × Fin (localBatchSize V ρ)

def localReplySample {Ω : Type} {V ρ δ : ℝ} (w : LocalDraws Ω V ρ δ)
    (i : LocalReplySlot V ρ δ) : Ω :=
  drawsVector id (localBatchSize V ρ) (drawsVector id (confidenceRepeats δ) w i.1) i.2

def localReplyCenter {d : ℕ} (V ρ δ : ℝ) (ys : LocalReplySlot V ρ δ → Point d) : Point d :=
  robustCenter (confidenceRepeats_pos δ)
    (fun j => (localBatchSize V ρ:ℝ)⁻¹ • ∑ i : Fin (localBatchSize V ρ), ys (j,i)) (ρ/3)

theorem localReplyCenter_measurable {d : ℕ} (V ρ δ : ℝ) :
    Measurable (@localReplyCenter d V ρ δ) := by
  apply (robustCenter_measurable (confidenceRepeats_pos δ) (ρ/3)).comp
  apply measurable_pi_lambda
  intro j
  have hm : Measurable (fun ys : LocalReplySlot V ρ δ → Point d =>
      ∑ i : Fin (localBatchSize V ρ), ys (j,i)) :=
    Finset.measurable_sum _ (fun i _ => measurable_pi_apply (j,i))
  exact hm.const_smul ((localBatchSize V ρ:ℝ)⁻¹)

theorem freshEstimate_eq_localReplyCenter {Ω : Type} {d : ℕ} (X : Ω → Point d)
    (V ρ δ : ℝ) (w : LocalDraws Ω V ρ δ) :
    freshEstimate X V ρ δ w=localReplyCenter V ρ δ (fun i => X (localReplySample w i)) :=
  robustBatch_eq_sample_average X (localBatchSize V ρ) (confidenceRepeats_pos δ) ρ w

def localReplyProgram {d : ℕ} (V ρ δ : ℝ) (qs : LocalReplySlot V ρ δ → HvpQuery d) :
    OracleProgram (HvpQuery d) (Point d) (Point d) :=
  OracleProgram.batch (Fintype.card (LocalReplySlot V ρ δ))
    (fun i => qs ((Fintype.equivFin (LocalReplySlot V ρ δ)).symm i))
    (fun ys => localReplyCenter V ρ δ (fun i => ys (Fintype.equivFin _ i)))

def localReplyAlgorithm {d : ℕ} (V ρ δ : ℝ) (qs : LocalReplySlot V ρ δ → HvpQuery d) :
    HvpAlgorithm d (ℕ → Point d) :=
  OracleProgram.algorithm (.grad 0) 0 0 (localReplyProgram V ρ δ qs)

theorem localReplySlot_count (V ρ δ : ℝ) :
    Fintype.card (LocalReplySlot V ρ δ)=localQueryCount V ρ δ := by
  simp only [LocalReplySlot,Fintype.card_prod,Fintype.card_fin,localQueryCount,Nat.mul_comm]

theorem localReplyProgram_usesAtMost {d : ℕ} (V ρ δ : ℝ) (qs : LocalReplySlot V ρ δ → HvpQuery d) :
    OracleProgram.UsesAtMost (localQueryCount V ρ δ) (localReplyProgram V ρ δ qs) := by
  rw [←localReplySlot_count]
  exact OracleProgram.batch_usesAtMost _ _ _

theorem localReplyAlgorithm_measurable {Ξ : Type} [MeasurableSpace Ξ] {d : ℕ}
    (V ρ δ : ℝ) (qs : Ξ → LocalReplySlot V ρ δ → HvpQuery d)
    (hq : ∀ i, Measurable (fun ξ => qs ξ i)) :
    MeasurableOracleAlgorithmFamily (fun ξ => localReplyAlgorithm V ρ δ (qs ξ)) := by
  apply OracleProgram.batch_algorithm_measurable
  · intro i
    exact hq _
  · apply (localReplyCenter_measurable V ρ δ).comp
    apply measurable_pi_lambda
    intro i
    exact (measurable_pi_apply (Fintype.equivFin _ i)).comp measurable_snd

theorem localReplyAlgorithm_output {Ω : Type} {d : ℕ} (V ρ δ : ℝ)
    (qs : LocalReplySlot V ρ δ → HvpQuery d) (reply : HvpQuery d → Ω → Point d) (zs : ℕ → Ω) :
    oracleAlgorithmOutput (localReplyAlgorithm V ρ δ qs) reply zs (localQueryCount V ρ δ)=
      localReplyCenter V ρ δ (fun i => reply (qs i) (zs (Fintype.equivFin _ i))) := by
  rw [←localReplySlot_count]
  unfold localReplyAlgorithm localReplyProgram
  rw [OracleProgram.batch_algorithm_output]
  simp only [Equiv.symm_apply_apply]

/-- A gradient anchor using the new reply-only algorithm interface. -/
def gradientAnchorAlgorithm {d : ℕ} (P : Parameters) (x : Point d) (ρ δ : ℝ) :
    HvpAlgorithm d (ℕ → Point d) :=
  localReplyAlgorithm (P.gradientNoise^2) ρ δ (fun _ => .grad x)

theorem gradientAnchorAlgorithm_measurable {d : ℕ} (P : Parameters) (ρ δ : ℝ) :
    MeasurableOracleAlgorithmFamily (fun x : Point d => gradientAnchorAlgorithm P x ρ δ) := by
  apply localReplyAlgorithm_measurable
  intro i
  exact (hvpQueryMeasurableEquiv d).symm.measurable.comp measurable_inl

theorem gradientAnchorAlgorithm_output {Ω : Type} {d : ℕ} (P : Parameters)
    (f : Ω → Point d → ℝ) (x : Point d) (ρ δ : ℝ)
    (w : LocalDraws Ω (P.gradientNoise^2) ρ δ) (zs : ℕ → Ω)
    (hz : ∀ i : LocalReplySlot (P.gradientNoise^2) ρ δ,
      zs (Fintype.equivFin _ i)=localReplySample w i) :
    oracleAlgorithmOutput (gradientAnchorAlgorithm P x ρ δ) (fun q z => hvpReply f z q)
      zs (localQueryCount (P.gradientNoise^2) ρ δ)=gradientAnchor P f x ρ δ w := by
  rw [gradientAnchorAlgorithm,localReplyAlgorithm_output,gradientAnchor,freshEstimate_eq_localReplyCenter]
  simp only [hz,hvpReply]

/-- Continuous line positions are private data; only Hessian-vector replies
are provided to the averaging and robust selection functions. -/
def freshChordAlgorithm {d : ℕ} (P : Parameters) (x y : Point d) (ρ δ : ℝ)
    (us : LocalReplySlot (chordVariance P x y) ρ δ → ℝ) : HvpAlgorithm d (ℕ → Point d) :=
  localReplyAlgorithm (chordVariance P x y) ρ δ (fun i => .hvp (x+us i•(y-x)) (y-x))

theorem freshChordAlgorithm_measurable {d : ℕ} (P : Parameters) (x y : Point d) (ρ δ : ℝ) :
    MeasurableOracleAlgorithmFamily (freshChordAlgorithm P x y ρ δ) := by
  apply localReplyAlgorithm_measurable
  intro i
  have hx : Measurable (fun us : LocalReplySlot (chordVariance P x y) ρ δ → ℝ => x+us i•(y-x)) :=
    measurable_const.add ((measurable_pi_apply i).smul_const (y-x))
  exact (hvpQueryMeasurableEquiv d).symm.measurable.comp
    (measurable_inr.comp (hx.prodMk measurable_const))

theorem freshChordAlgorithm_output {Ω : Type} {d : ℕ} (P : Parameters)
    (f : Ω → Point d → ℝ) (x y : Point d) (ρ δ : ℝ)
    (w : LocalDraws (ℝ × Ω) (chordVariance P x y) ρ δ) (zs : ℕ → Ω)
    (hz : ∀ i : LocalReplySlot (chordVariance P x y) ρ δ,
      zs (Fintype.equivFin _ i)=(localReplySample w i).2) :
    oracleAlgorithmOutput (freshChordAlgorithm P x y ρ δ (fun i => (localReplySample w i).1))
      (fun q z => hvpReply f z q) zs (localQueryCount (chordVariance P x y) ρ δ)=
        freshChord P f x y ρ δ w := by
  rw [freshChordAlgorithm,localReplyAlgorithm_output,freshChord,freshEstimate_eq_localReplyCenter]
  apply congrArg (localReplyCenter (chordVariance P x y) ρ δ)
  funext i
  rw [hz]
  rfl

end
end SecondOrder
