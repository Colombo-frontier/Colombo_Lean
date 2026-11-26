import GradientHessian.ChronologicalFork
import GradientHessian.ForkSourceExpectation

/-!
# Probability for the actual finite chronological fork

Independent marks and private branch seeds are bundled for the chronological
oracle procedure and explicitly regrouped for the sphere-column calculation.
-/

namespace GradientHessian.ForkChronologicalProbability

open Matrix MeasureTheory ProbabilityTheory LowRank
open GradientHessian.OracleComposition GradientHessian.ForkColumns
open GradientHessian.ForkProbability GradientHessian.ForkSourceExpectation
open GradientHessian.SphereColumnNorm GradientHessian.MatrixGoodSpectrum
open scoped InnerProductSpace ENNReal BigOperators
noncomputable section

section Rearrangement

variable {C M V : Type*} [MeasurableSpace C] [MeasurableSpace M] [MeasurableSpace V]

def regroup (r : ℕ) : (C × (Fin r → M × V)) ≃ᵐ ((C × (Fin r → V)) × (Fin r → M)) where
  toFun t := ((t.1, fun i => (t.2 i).2), fun i => (t.2 i).1)
  invFun t := (t.1.1, fun i => (t.2 i,t.1.2 i))
  left_inv t := by ext <;> rfl
  right_inv t := by ext <;> rfl
  measurable_toFun := by
    change Measurable (fun t : C × (Fin r → M × V) =>
      ((t.1, fun i => (t.2 i).2), fun i => (t.2 i).1))
    fun_prop
  measurable_invFun := by
    change Measurable (fun t : (C × (Fin r → V)) × (Fin r → M) =>
      (t.1.1, fun i => (t.2 i,t.1.2 i)))
    fun_prop

theorem regroup_preserving (μ : Measure C) [IsProbabilityMeasure μ]
    (ν : Measure M) [IsProbabilityMeasure ν] (π : Measure V) [IsProbabilityMeasure π] (r : ℕ) :
    MeasurePreserving (regroup (C := C) (M := M) (V := V) r)
      (μ.prod (Measure.pi (fun _ : Fin r => ν.prod π)))
      ((μ.prod (Measure.pi (fun _ : Fin r => π))).prod (Measure.pi (fun _ : Fin r => ν))) := by
  have hs := measurePreserving_arrowProdEquivProdArrow M V (Fin r)
    (fun _ => ν) (fun _ => π)
  have h1 := (MeasurePreserving.id μ).prod hs
  have h2 := (MeasurePreserving.id μ).prod
    (Measure.measurePreserving_swap (μ := Measure.pi (fun _ : Fin r => ν))
      (ν := Measure.pi (fun _ : Fin r => π)))
  have h3 := (measurePreserving_prodAssoc μ (Measure.pi (fun _ : Fin r => π))
    (Measure.pi (fun _ : Fin r => ν))).symm MeasurableEquiv.prodAssoc
  exact h3.comp (h2.comp h1)

def oracleOrder {X S F : Type*} [MeasurableSpace X] [MeasurableSpace S] [MeasurableSpace F] :
    ((X × S) × F) ≃ᵐ ((S × F) × X) :=
  MeasurableEquiv.prodAssoc.trans MeasurableEquiv.prodComm

theorem oracleOrder_preserving {X S F : Type*}
    [MeasurableSpace X] [MeasurableSpace S] [MeasurableSpace F]
    (μ : Measure X) [IsProbabilityMeasure μ] (ν : Measure S) [IsProbabilityMeasure ν]
    (ρ : Measure F) [IsProbabilityMeasure ρ] :
    MeasurePreserving (oracleOrder (X := X) (S := S) (F := F))
      ((μ.prod ν).prod ρ) ((ν.prod ρ).prod μ) :=
  Measure.measurePreserving_swap.comp (measurePreserving_prodAssoc μ ν ρ)

end Rearrangement

section Finite

variable {d p q r s n : ℕ} {Seed State Private : Type*}
  [MeasurableSpace Seed] [MeasurableSpace State] [MeasurableSpace Private]

def branchTests (J : ℕ) (P : Matrix (Fin d) (Fin d) ℝ)
    (pre : Procedure d p Seed State)
    (post : Procedure d q (State × (EuclideanSpace ℝ (Fin r) × Private))
      (Fin s → EuclideanSpace ℝ (Fin d)))
    (t : (Matrix (Fin d) (Fin n) ℝ × Seed) × (EuclideanSpace ℝ (Fin r) × Private)) :
    Fin s → EuclideanSpace ℝ (Fin d) :=
  post.run (sourceMatrix P J t.1.1) (pre.run (sourceMatrix P J t.1.1) t.1.2,t.2)

theorem branchTests_measurable (J : ℕ) (P : Matrix (Fin d) (Fin d) ℝ)
    (pre : Procedure d p Seed State)
    (post : Procedure d q (State × (EuclideanSpace ℝ (Fin r) × Private))
      (Fin s → EuclideanSpace ℝ (Fin d))) :
    Measurable (branchTests (n := n) J P pre post) := by
  have hA : Measurable (fun t : (Matrix (Fin d) (Fin n) ℝ × Seed) ×
      (EuclideanSpace ℝ (Fin r) × Private) => sourceMatrix P J t.1.1) :=
    (ReadoutMeasurability.sourceMatrix_measurable P J).comp measurable_fst.fst
  exact post.run_measurable.comp
    (hA.prodMk ((pre.run_measurable.comp (hA.prodMk measurable_fst.snd)).prodMk measurable_snd))

def branchHit (J : ℕ) (P : Matrix (Fin d) (Fin d) ℝ)
    (B : Matrix (Fin d) (Fin r) ℝ) (fallback : Fin d → ℝ)
    (pre : Procedure d p Seed State)
    (post : Procedure d q (State × (EuclideanSpace ℝ (Fin r) × Private))
      (Fin s → EuclideanSpace ℝ (Fin d))) (γ : ℝ) :
    Set ((Matrix (Fin d) (Fin n) ℝ × Seed) × (EuclideanSpace ℝ (Fin r) × Private)) :=
  {t | ∃ j, γ < |⟪UnmarkedReadout.sourceOutput J P t.1.1 B fallback t.2.1,
    branchTests J P pre post t j⟫_ℝ|}

theorem branchHit_measurable (J : ℕ) (P : Matrix (Fin d) (Fin d) ℝ)
    (B : Matrix (Fin d) (Fin r) ℝ) (fallback : Fin d → ℝ)
    (pre : Procedure d p Seed State)
    (post : Procedure d q (State × (EuclideanSpace ℝ (Fin r) × Private))
      (Fin s → EuclideanSpace ℝ (Fin d))) (γ : ℝ) :
    MeasurableSet (branchHit (n := n) J P B fallback pre post γ) := by
  unfold branchHit
  simp only [Set.setOf_exists]
  apply MeasurableSet.iUnion
  intro j
  have ha := UnmarkedReadout.sourceOutput_measurable_comp J P B fallback
    (fun t : (Matrix (Fin d) (Fin n) ℝ × Seed) × (EuclideanSpace ℝ (Fin r) × Private) => t.1.1)
    (fun t => t.2.1) measurable_fst.fst measurable_snd.fst
  have hy := (measurable_pi_apply j).comp (branchTests_measurable (n := n) J P pre post)
  exact measurableSet_lt measurable_const (ha.inner hy).abs

def geometryTests (J : ℕ) (P : Matrix (Fin d) (Fin d) ℝ)
    (pre : Procedure d p Seed State)
    (post : Procedure d q (State × (EuclideanSpace ℝ (Fin r) × Private))
      (Fin s → EuclideanSpace ℝ (Fin d)))
    (t : ((Matrix (Fin d) (Fin n) ℝ × Seed) × (Fin r → Private)) ×
      (Fin r → EuclideanSpace ℝ (Fin r))) : Fin r → Fin s → EuclideanSpace ℝ (Fin d) :=
  fun i => branchTests J P pre post (t.1.1, (t.2 i,t.1.2 i))

theorem geometryTests_measurable (J : ℕ) (P : Matrix (Fin d) (Fin d) ℝ)
    (pre : Procedure d p Seed State)
    (post : Procedure d q (State × (EuclideanSpace ℝ (Fin r) × Private))
      (Fin s → EuclideanSpace ℝ (Fin d))) :
    Measurable (geometryTests (n := n) J P pre post) := by
  apply measurable_pi_lambda
  intro i
  exact (branchTests_measurable (n := n) J P pre post).comp
    (measurable_fst.fst.prodMk
      (((measurable_pi_apply i).comp measurable_snd).prodMk
        ((measurable_pi_apply i).comp measurable_fst.snd)))

def commonGood (P : Matrix (Fin d) (Fin d) ℝ) (J : ℕ) :
    Set (Matrix (Fin d) (Fin n) ℝ × Seed) :=
  {t | t.1 ∈ MatrixKernelConcentration.sourceGoodEvent P J}

theorem commonGood_measurable (P : Matrix (Fin d) (Fin d) ℝ) (J : ℕ) :
    MeasurableSet (commonGood (n := n) (Seed := Seed) P J) :=
  (MatrixKernelConcentration.measurableSet_sourceGoodEvent P J).preimage measurable_fst

omit [MeasurableSpace Seed] in
theorem commonGood_eq (P : Matrix (Fin d) (Fin d) ℝ) (J : ℕ) :
    commonGood (n := n) (Seed := Seed) P J =
      MatrixKernelConcentration.sourceGoodEvent P J ×ˢ Set.univ := by
  ext t
  simp [commonGood]

def matrixProcedure (J : ℕ) (P : Matrix (Fin d) (Fin d) ℝ)
    (pre : Procedure d p Seed State)
    (post : Procedure d q (State × (EuclideanSpace ℝ (Fin r) × Private))
      (Fin s → EuclideanSpace ℝ (Fin d))) :
    Procedure d (p+r*q) (Seed × (Fin r → EuclideanSpace ℝ (Fin r) × Private))
      (Fin r → Fin s → EuclideanSpace ℝ (Fin d)) :=
  OracleSimulation.procedure (256*(J:ℝ)^2)
    (MatrixProjectorCompression.dilation P (Real.sqrt (1/(J:ℝ))))
    (ChronologicalFork.procedure pre post r)

def forkOverlap (J : ℕ) (P : Matrix (Fin d) (Fin d) ℝ)
    (pre : Procedure d p Seed State)
    (post : Procedure d q (State × (EuclideanSpace ℝ (Fin r) × Private))
      (Fin s → EuclideanSpace ℝ (Fin d)))
    (t : (Seed × (Fin r → EuclideanSpace ℝ (Fin r) × Private)) ×
      Matrix (Fin d) (Fin n) ℝ) : ℝ :=
  (branchProjector P ((matrixProcedure J P pre post).run (t.2*t.2ᵀ) t.1)*
    leftKernelProjector t.2).trace

theorem matrixProcedure_branch (J : ℕ) (P : Matrix (Fin d) (Fin d) ℝ)
    (pre : Procedure d p Seed State)
    (post : Procedure d q (State × (EuclideanSpace ℝ (Fin r) × Private))
      (Fin s → EuclideanSpace ℝ (Fin d)))
    (t : (Matrix (Fin d) (Fin n) ℝ × Seed) × (Fin r → EuclideanSpace ℝ (Fin r) × Private))
    (i : Fin r) :
    (matrixProcedure J P pre post).run (t.1.1*t.1.1ᵀ) (t.1.2,t.2) i =
      branchTests J P pre post (t.1,t.2 i) := by
  exact ChronologicalFork.source_fork_run pre post r _ _ _ _ i

/-- The actual compiled fork obeys the source-event expectation inequality.
Both fresh marks and private branch seeds have their explicit product laws. -/
theorem finite_fork_mean {J : ℕ} (hJ : 4 ≤ J) (hr : 0 < r)
    {P : Matrix (Fin d) (Fin d) ℝ} (hP : IsOrthogonalProjector P)
    (B : Matrix (Fin d) (Fin r) ℝ) (hB : Bᵀ*B = 1) (hPB : P*B = B)
    (fallback : Fin d → ℝ)
    (pre : Procedure d p Seed State)
    (post : Procedure d q (State × (EuclideanSpace ℝ (Fin r) × Private))
      (Fin s → EuclideanSpace ℝ (Fin d)))
    (hnorm : ∀ A state fresh j, ‖post.run A (state,fresh) j‖ ≤ 1)
    (matrixLaw : Measure (Matrix (Fin d) (Fin n) ℝ)) [IsProbabilityMeasure matrixLaw]
    (seedLaw : Measure Seed) [IsProbabilityMeasure seedLaw]
    (privateLaw : Measure Private) [IsProbabilityMeasure privateLaw]
    {γ : ℝ} (hγ : 0 < γ) (hδ : 5*ReadoutFilter.delta ≤ γ/4)
    (hp : 0 < (matrixLaw.prod seedLaw).real (commonGood P J)) :
    (matrixLaw.prod seedLaw).real (commonGood P J)*(r:ℝ)*
      ((cond (matrixLaw.prod seedLaw) (commonGood P J)).prod
        ((SphereGaussian.sphereLaw (EuclideanSpace ℝ (Fin r))).prod privateLaw)).real
          (branchHit J P B fallback pre post γ) ≤
      (256/γ^2)*(∫ t, forkOverlap J P pre post t
        ∂(seedLaw.prod (Measure.pi (fun _ : Fin r =>
          (SphereGaussian.sphereLaw (EuclideanSpace ℝ (Fin r))).prod privateLaw))).prod matrixLaw) +
      (r:ℝ)*Real.exp (-Real.log (3/2:ℝ)*(r:ℝ)) := by
  let ν := SphereGaussian.sphereLaw (EuclideanSpace ℝ (Fin r))
  let μ := matrixLaw.prod seedLaw
  let ξ := Measure.pi (fun _ : Fin r => privateLaw)
  let H := branchHit (n := n) J P B fallback pre post γ
  let E := commonGood (n := n) (Seed := Seed) P J
  let X := fun u : (Matrix (Fin d) (Fin n) ℝ × Seed) × (Fin r → Private) => u.1.1
  let tests := geometryTests (n := n) J P pre post
  let Egeom : Set (((Matrix (Fin d) (Fin n) ℝ × Seed) × (Fin r → Private)) ×
      (Fin r → EuclideanSpace ℝ (Fin r))) :=
    {t | X t.1 ∈ MatrixKernelConcentration.sourceGoodEvent P J}
  let f := Egeom.indicator (sourceCount J P B fallback X tests γ)
  let g := sourceOverlap P X tests
  have hmean := source_mean_hitCount_le (μ.prod ξ) hr hP hJ B hB hPB fallback
    X measurable_fst.fst tests (geometryTests_measurable J P pre post)
    (fun t i j => hnorm _ _ _ j) hγ hδ
  change (∫ t, f t ∂(μ.prod ξ).prod (Measure.pi (fun _ : Fin r => ν))) ≤
    (256/γ^2)*(∫ t, g t ∂(μ.prod ξ).prod (Measure.pi (fun _ : Fin r => ν))) +
      (r:ℝ)*Real.exp (-Real.log (3/2:ℝ)*(r:ℝ)) at hmean
  have hreg := regroup_preserving μ ν privateLaw r
  rw [← hreg.integral_comp' f, ← hreg.integral_comp' g] at hmean
  have hc (t : (Matrix (Fin d) (Fin n) ℝ × Seed) ×
      (Fin r → EuclideanSpace ℝ (Fin r) × Private)) :
      f (regroup r t) = E.indicator (fun ω => (hitCount H ω t.2 : ℝ)) t.1 := by
    classical
    by_cases he : t.1 ∈ E
    · have he' : regroup r t ∈ Egeom := he
      dsimp only [f]
      rw [Set.indicator_of_mem he', Set.indicator_of_mem he]
      unfold sourceCount sourceHits hitCount
      apply congrArg (fun S : Finset (Fin r) => (S.card:ℝ))
      apply Finset.filter_congr
      intro i _
      rfl
    · have he' : regroup r t ∉ Egeom := he
      dsimp only [f]
      rw [Set.indicator_of_not_mem he', Set.indicator_of_not_mem he]
  simp_rw [hc] at hmean
  rw [integral_event_hitCount_cond μ (ν.prod privateLaw) r (commonGood_measurable P J) hp
    (branchHit_measurable J P B fallback pre post γ)] at hmean
  have ht (t : (Matrix (Fin d) (Fin n) ℝ × Seed) ×
      (Fin r → EuclideanSpace ℝ (Fin r) × Private)) :
      g (regroup r t) = forkOverlap J P pre post (oracleOrder t) := by
    dsimp only [g, sourceOverlap, forkOverlap]
    congr 2
    apply congrArg (branchProjector P)
    funext i
    exact (matrixProcedure_branch J P pre post t i).symm
  simp_rw [ht] at hmean
  letI : IsProbabilityMeasure (Measure.pi (fun _ : Fin r => ν.prod privateLaw)) := by
    letI : IsProbabilityMeasure ν := by dsimp [ν]; infer_instance
    letI : IsProbabilityMeasure (ν.prod privateLaw) := by infer_instance
    exact Measure.pi.instIsProbabilityMeasure _
  have horder := oracleOrder_preserving matrixLaw seedLaw
    (Measure.pi (fun _ : Fin r => ν.prod privateLaw))
  have horderint := horder.integral_comp' (forkOverlap (n := n) J P pre post)
  rw [horderint] at hmean
  exact hmean

theorem commonGood_mass (P : Matrix (Fin d) (Fin d) ℝ) (J : ℕ)
    (matrixLaw : Measure (Matrix (Fin d) (Fin n) ℝ))
    (seedLaw : Measure Seed) [IsProbabilityMeasure seedLaw] :
    (matrixLaw.prod seedLaw).real (commonGood P J) =
      matrixLaw.real (MatrixKernelConcentration.sourceGoodEvent P J) := by
  rw [commonGood_eq]
  simp [measureReal_def, Measure.prod_prod]

def conditionedHitProbability (J : ℕ) (P : Matrix (Fin d) (Fin d) ℝ)
    (B : Matrix (Fin d) (Fin r) ℝ) (fallback : Fin d → ℝ)
    (pre : Procedure d p Seed State)
    (post : Procedure d q (State × (EuclideanSpace ℝ (Fin r) × Private))
      (Fin s → EuclideanSpace ℝ (Fin d)))
    (matrixLaw : Measure (Matrix (Fin d) (Fin n) ℝ)) (seedLaw : Measure Seed)
    (privateLaw : Measure Private) (γ : ℝ) : ℝ :=
  ((cond (matrixLaw.prod seedLaw) (commonGood P J)).prod
    ((SphereGaussian.sphereLaw (EuclideanSpace ℝ (Fin r))).prod privateLaw)).real
      (branchHit J P B fallback pre post γ)

theorem conditioned_input_law (P : Matrix (Fin d) (Fin d) ℝ) (J : ℕ)
    (matrixLaw : Measure (Matrix (Fin d) (Fin n) ℝ)) [IsProbabilityMeasure matrixLaw]
    (seedLaw : Measure Seed) [IsProbabilityMeasure seedLaw] :
    cond (matrixLaw.prod seedLaw) (commonGood P J) =
      (cond matrixLaw (MatrixKernelConcentration.sourceGoodEvent P J)).prod seedLaw := by
  rw [commonGood_eq]
  exact ConditionedSource.condition_matrix_only matrixLaw seedLaw
    (MatrixKernelConcentration.measurableSet_sourceGoodEvent P J)

/-- Finite chronological fork probability with independently sampled private
branch seeds. The numerator uses the literal query count `p+r*q` and output
rank `r*s`; setting `s=q+2` gives the manuscript numerator. Matrix dimensions
are written as `a+Q,b+Q`, so the residual denominator is exactly `a` and the
kernel nullity is `a-b`. The event is the actual source event. -/
theorem finite_fork_probability_bound (a b : ℕ) (hb : b ≤ a) (ha : 0 < a)
    {J : ℕ} (hJ : 4 ≤ J) (hr : 0 < r)
    {P : Matrix (Fin (a+(p+r*q))) (Fin (a+(p+r*q))) ℝ} (hP : IsOrthogonalProjector P)
    (B : Matrix (Fin (a+(p+r*q))) (Fin r) ℝ) (hB : Bᵀ*B = 1) (hPB : P*B = B)
    (fallback : Fin (a+(p+r*q)) → ℝ)
    (pre : Procedure (a+(p+r*q)) p Seed State)
    (post : Procedure (a+(p+r*q)) q (State × (EuclideanSpace ℝ (Fin r) × Private))
      (Fin s → EuclideanSpace ℝ (Fin (a+(p+r*q)))))
    (hnorm : ∀ A state fresh j, ‖post.run A (state,fresh) j‖ ≤ 1)
    (seedLaw : Measure Seed) [IsProbabilityMeasure seedLaw]
    (privateLaw : Measure Private) [IsProbabilityMeasure privateLaw]
    {v : NNReal} (hv : v ≠ 0) {γ : ℝ} (hγ : 0 < γ) (hδ : 5*ReadoutFilter.delta ≤ γ/4)
    (hp : 0 < (iidMatrixLaw (a+(p+r*q)) (b+(p+r*q)) v).real
      (MatrixKernelConcentration.sourceGoodEvent P J)) :
    conditionedHitProbability J P B fallback pre post
      (iidMatrixLaw (a+(p+r*q)) (b+(p+r*q)) v) seedLaw privateLaw γ ≤
      (512*((a:ℝ)-b)/(γ^2*(r:ℝ)*
        (iidMatrixLaw (a+(p+r*q)) (b+(p+r*q)) v).real
          (MatrixKernelConcentration.sourceGoodEvent P J)))*
        (((p+r*q:ℕ):ℝ)+(r*s:ℕ))/a +
      Real.exp (-Real.log (3/2:ℝ)*(r:ℝ))/
        (iidMatrixLaw (a+(p+r*q)) (b+(p+r*q)) v).real
          (MatrixKernelConcentration.sourceGoodEvent P J) := by
  let matrixLaw := iidMatrixLaw (a+(p+r*q)) (b+(p+r*q)) v
  let pE := matrixLaw.real (MatrixKernelConcentration.sourceGoodEvent P J)
  let fullSeed := seedLaw.prod (Measure.pi (fun _ : Fin r =>
    (SphereGaussian.sphereLaw (EuclideanSpace ℝ (Fin r))).prod privateLaw))
  letI : IsProbabilityMeasure fullSeed := by
    letI : IsProbabilityMeasure (Measure.pi (fun _ : Fin r =>
        (SphereGaussian.sphereLaw (EuclideanSpace ℝ (Fin r))).prod privateLaw)) :=
      Measure.pi.instIsProbabilityMeasure _
    dsimp [fullSeed]
    infer_instance
  let prob := conditionedHitProbability J P B fallback pre post matrixLaw seedLaw privateLaw γ
  let ε := Real.exp (-Real.log (3/2:ℝ)*(r:ℝ))
  have hmean := finite_fork_mean hJ hr hP B hB hPB fallback pre post hnorm
    matrixLaw seedLaw privateLaw hγ hδ (by rwa [commonGood_mass])
  rw [commonGood_mass] at hmean
  change pE*(r:ℝ)*prob ≤ (256/γ^2)*(∫ t, forkOverlap J P pre post t
    ∂fullSeed.prod matrixLaw)+(r:ℝ)*ε at hmean
  have hu := ChronologicalFork.procedure_overlap a b (p+r*q) r s fullSeed
    (matrixProcedure J P pre post) P hb ha hv
  have hfactor : 0 ≤ 256/γ^2 := by positivity
  have hc : pE*(r:ℝ)*prob ≤
      (256/γ^2)*(2*((a:ℝ)-b)*(((p+r*q:ℕ):ℝ)+(r*s:ℕ))/a)+(r:ℝ)*ε :=
    hmean.trans (add_le_add_right (mul_le_mul_of_nonneg_left hu hfactor) _)
  have hrR : (0:ℝ)<r := by exact_mod_cast hr
  have haR : (0:ℝ)<a := by exact_mod_cast ha
  have hpE : 0 < pE := hp
  have hdiv : prob ≤
      ((256/γ^2)*(2*((a:ℝ)-b)*(((p+r*q:ℕ):ℝ)+(r*s:ℕ))/a)+(r:ℝ)*ε)/(pE*r) :=
    (le_div_iff₀ (mul_pos hpE hrR)).mpr (by nlinarith [hc])
  apply hdiv.trans_eq
  change ((256/γ^2)*(2*((a:ℝ)-b)*(((p+r*q:ℕ):ℝ)+(r*s:ℕ))/a)+(r:ℝ)*ε)/(pE*r) =
    (512*((a:ℝ)-b)/(γ^2*(r:ℝ)*pE))*(((p+r*q:ℕ):ℝ)+(r*s:ℕ))/a + ε/pE
  field_simp [hγ.ne', hrR.ne', haR.ne', hpE.ne']
  ring

theorem source_numerator (p q r : ℕ) :
    ((p+r*q:ℕ):ℝ)+(r*(q+2):ℕ) = (p:ℝ)+2*(r:ℝ)*q+2*r := by
  push_cast
  ring

/-- The positive event-mass premise of the finite theorem is discharged for
the actual normalized Gaussian source under the proved manuscript parameter
conditions. No new analytic event is introduced. -/
theorem source_event_mass (a b Q J κ k r : ℕ)
    (hJ : 4 ≤ J) (hr : 1+4096*J^2 ≤ r) (hκ : 18874368 ≤ κ)
    (hk : k = κ*r) (hab : k+b = a) (hD : a+Q = k*J)
    (P : Matrix (Fin (a+Q)) (Fin (a+Q)) ℝ)
    (hP : IsOrthogonalProjector P) (hrank : P.rank = r) :
    99/100 ≤ (iidMatrixLaw (a+Q) (b+Q) ((a+Q:ℕ):NNReal)⁻¹).real
      (MatrixKernelConcentration.sourceGoodEvent P J) := by
  have hn : a+Q-k = b+Q := by omega
  have h := MatrixKernelConcentration.manuscript_sourceGoodEvent_probability
    hJ hr hκ hk hD P hP hrank
  rw [← hn]
  exact h

end Finite
end
end GradientHessian.ForkChronologicalProbability
