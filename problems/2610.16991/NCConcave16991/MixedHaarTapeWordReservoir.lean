import NCConcave16991.MixedHaarTapeMarginal
import NCConcave16991.MixedHaarWordDimension

/-! # The common Gaussian reservoir is the actual fresh-tape marginal -/

noncomputable section

open Set MeasureTheory ProbabilityTheory

namespace NCConcave16991.MixedHaar

set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false

abbrev GaussianVertexBlock (n H D : ℕ) :=
  ∀ d : Fin (H + 1), BranchOracle.FormalLayer (ι := Fin n) (Space D) d.val

def gaussianVertexLaw (n H D : ℕ) : Measure (GaussianVertexBlock n H D) :=
  Measure.pi (fun d ↦ stdGaussian (BranchOracle.FormalLayer (ι := Fin n) (Space D) d.val))

instance gaussianVertexLaw_probability (n H D : ℕ) : IsProbabilityMeasure (gaussianVertexLaw n H D) := by
  unfold gaussianVertexLaw
  infer_instance

variable {Y Z : Type} [MeasurableSpace Y] [MeasurableSpace Z]

def tapeWordReservoir {n H N D : ℕ}
    (p : RevealTape (GaussianVertexBlock n H D × Y) Z N) : WordReservoir n H N D :=
  fun a ↦ (tapeFresh N p a.1).1 a.2

theorem tapeWordReservoir_preserving (n H N D : ℕ) (η : Measure Y) (ν : Measure Z)
    [IsProbabilityMeasure η] [IsProbabilityMeasure ν] :
    MeasurePreserving (tapeWordReservoir (n := n) (H := H) (N := N) (D := D))
      (revealTapeLaw ((gaussianVertexLaw n H D).prod η) ν N) (wordReservoirLaw n H N D) := by
  have hFresh := tapeFresh_preserving ((gaussianVertexLaw n H D).prod η) ν N
  have hFirst : MeasurePreserving
      (fun f : Fin N → GaussianVertexBlock n H D × Y ↦ fun t ↦ (f t).1)
      (Measure.pi (fun _ : Fin N ↦ (gaussianVertexLaw n H D).prod η))
      (Measure.pi (fun _ : Fin N ↦ gaussianVertexLaw n H D)) :=
    measurePreserving_pi _ _ (fun _ ↦ measurePreserving_fst)
  have hFlat := gaussian_nested_product_preserving
    (I := Fin N) (J := fun _ ↦ Fin (H + 1))
    (A := fun _ d ↦ BranchOracle.FormalLayer (ι := Fin n) (Space D) d.val)
  let e : Sigma (fun _ : Fin N ↦ Fin (H + 1)) ≃ Fin N × Fin (H + 1) :=
    { toFun := fun p ↦ (p.1,p.2)
      invFun := fun p ↦ ⟨p.1,p.2⟩
      left_inv := fun p ↦ by cases p; rfl
      right_inv := fun p ↦ rfl }
  have hIndex := measurePreserving_piCongrLeft
    (fun a : Fin N × Fin (H + 1) ↦ stdGaussian (BranchOracle.FormalLayer (ι := Fin n) (Space D) a.2.val)) e
  have hh := hIndex.comp (hFlat.comp (hFirst.comp hFresh))
  convert hh using 1
  funext p a
  rcases a with ⟨t,d⟩
  symm
  change (MeasurableEquiv.piCongrLeft
    (fun a : Fin N × Fin (H + 1) ↦ BranchOracle.FormalLayer (ι := Fin n) (Space D) a.2.val) e)
      (fun ij ↦ (tapeFresh N p ij.1).1 ij.2) (e ⟨t,d⟩) = _
  rw [MeasurableEquiv.piCongrLeft_apply_apply]
  rfl
  all_goals rfl

theorem tape_word_projection_tail {n H N D : ℕ} (η : Measure Y) (ν : Measure Z)
    [IsProbabilityMeasure η] [IsProbabilityMeasure ν] (hD : 0 < D) (i : Fin D)
    {a : ℝ} (ha : 0 < a) :
    (revealTapeLaw ((gaussianVertexLaw n H D).prod η) ν N).real {p |
      a ≤ ‖(wordReservoirSpan (tapeWordReservoir p)).orthogonalProjectionOnto (Haar.basisVector i)‖ ^ 2} ≤
        (wordSliceCount n H N : ℝ) / ((D : ℝ) * a) := by
  let E : Set (WordReservoir n H N D) := {f |
    a ≤ ‖(wordReservoirSpan f).orthogonalProjectionOnto (Haar.basisVector i)‖ ^ 2}
  have hE : MeasurableSet E := by
    simp_rw [E,word_projection_score_eq]
    exact measurableSet_le measurable_const
      ((coordinateScore_measurable i).comp (wordReservoirFlatten_preserving n H N D).measurable)
  have hp := tapeWordReservoir_preserving n H N D η ν
  have he : (revealTapeLaw ((gaussianVertexLaw n H D).prod η) ν N).real
      (tapeWordReservoir ⁻¹' E) = (wordReservoirLaw n H N D).real E := by
    unfold Measure.real
    rw [← hp.map_eq,Measure.map_apply hp.measurable hE]
  exact he.trans_le (word_reservoir_projection_tail hD i ha)

theorem tape_word_projection_small (n H N U : ℕ) (η : Measure Y) (ν : Measure Z)
    [IsProbabilityMeasure η] [IsProbabilityMeasure ν] {a : ℝ} (ha : 0 < a)
    (i : Fin (wordAmbientDimension n H N U a)) :
    (revealTapeLaw ((gaussianVertexLaw n H (wordAmbientDimension n H N U a)).prod η) ν N).real {p |
      a ≤ ‖(wordReservoirSpan (tapeWordReservoir p)).orthogonalProjectionOnto (Haar.basisVector i)‖ ^ 2} ≤ 1 / 6 :=
  (tape_word_projection_tail η ν (wordAmbientDimension_pos _ _ _ _ _) i ha).trans
    (wordAmbientDimension_coefficient n H N U ha)

theorem gaussian_slot_array_preserving (n H N D : ℕ) :
    MeasurePreserving (fun f : Fin N → GaussianVertexBlock n H D ↦ fun a : Fin N × Fin (H + 1) ↦ f a.1 a.2)
      (Measure.pi (fun _ : Fin N ↦ gaussianVertexLaw n H D)) (wordReservoirLaw n H N D) := by
  have hFlat := gaussian_nested_product_preserving
    (I := Fin N) (J := fun _ ↦ Fin (H + 1))
    (A := fun _ d ↦ BranchOracle.FormalLayer (ι := Fin n) (Space D) d.val)
  let e : Sigma (fun _ : Fin N ↦ Fin (H + 1)) ≃ Fin N × Fin (H + 1) :=
    { toFun := fun p ↦ (p.1,p.2)
      invFun := fun p ↦ ⟨p.1,p.2⟩
      left_inv := fun p ↦ by cases p; rfl
      right_inv := fun p ↦ rfl }
  have hIndex := measurePreserving_piCongrLeft
    (fun a : Fin N × Fin (H + 1) ↦ stdGaussian (BranchOracle.FormalLayer (ι := Fin n) (Space D) a.2.val)) e
  have hh := hIndex.comp hFlat
  convert hh using 1
  funext f a
  rcases a with ⟨t,d⟩
  symm
  change (MeasurableEquiv.piCongrLeft
    (fun a : Fin N × Fin (H + 1) ↦ BranchOracle.FormalLayer (ι := Fin n) (Space D) a.2.val) e)
      (fun ij ↦ f ij.1 ij.2) (e ⟨t,d⟩) = _
  rw [MeasurableEquiv.piCongrLeft_apply_apply]
  rfl
  all_goals rfl

def pureTapeWordReservoir {n H N D : ℕ} (p : RevealTape (GaussianVertexBlock n H D) Z N) : WordReservoir n H N D :=
  fun a ↦ tapeFresh N p a.1 a.2

theorem pureTapeWordReservoir_preserving (n H N D : ℕ) (ν : Measure Z) [IsProbabilityMeasure ν] :
    MeasurePreserving (pureTapeWordReservoir (n := n) (H := H) (N := N) (D := D))
      (revealTapeLaw (gaussianVertexLaw n H D) ν N) (wordReservoirLaw n H N D) :=
  (gaussian_slot_array_preserving n H N D).comp (tapeFresh_preserving (gaussianVertexLaw n H D) ν N)

theorem pure_tape_word_projection_tail {n H N D : ℕ} (ν : Measure Z) [IsProbabilityMeasure ν]
    (hD : 0 < D) (i : Fin D) {a : ℝ} (ha : 0 < a) :
    (revealTapeLaw (gaussianVertexLaw n H D) ν N).real {p |
      a ≤ ‖(wordReservoirSpan (pureTapeWordReservoir p)).orthogonalProjectionOnto (Haar.basisVector i)‖ ^ 2} ≤
        (wordSliceCount n H N : ℝ) / ((D : ℝ) * a) := by
  let E : Set (WordReservoir n H N D) := {f |
    a ≤ ‖(wordReservoirSpan f).orthogonalProjectionOnto (Haar.basisVector i)‖ ^ 2}
  have hE : MeasurableSet E := by
    simp_rw [E,word_projection_score_eq]
    exact measurableSet_le measurable_const
      ((coordinateScore_measurable i).comp (wordReservoirFlatten_preserving n H N D).measurable)
  have hp := pureTapeWordReservoir_preserving n H N D ν
  have he : (revealTapeLaw (gaussianVertexLaw n H D) ν N).real
      (pureTapeWordReservoir ⁻¹' E) = (wordReservoirLaw n H N D).real E := by
    unfold Measure.real
    rw [← hp.map_eq,Measure.map_apply hp.measurable hE]
  exact he.trans_le (word_reservoir_projection_tail hD i ha)

theorem pure_tape_word_projection_small (n H N U : ℕ) (ν : Measure Z) [IsProbabilityMeasure ν]
    {a : ℝ} (ha : 0 < a) (i : Fin (wordAmbientDimension n H N U a)) :
    (revealTapeLaw (gaussianVertexLaw n H (wordAmbientDimension n H N U a)) ν N).real {p |
      a ≤ ‖(wordReservoirSpan (pureTapeWordReservoir p)).orthogonalProjectionOnto (Haar.basisVector i)‖ ^ 2} ≤ 1 / 6 :=
  (pure_tape_word_projection_tail ν (wordAmbientDimension_pos _ _ _ _ _) i ha).trans
    (wordAmbientDimension_coefficient n H N U ha)

end NCConcave16991.MixedHaar
