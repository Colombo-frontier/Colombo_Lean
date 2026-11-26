import NCConcave16991.DenseSmoothOracle
import Mathlib.Analysis.Calculus.FDeriv.Measurable

/-! # Actual Borel reference gradients with transcript-dependent known data -/

namespace NCConcave16991.DenseSmooth

noncomputable section

open Set MeasureTheory
open scoped InnerProductSpace BigOperators

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {n T : ℕ}

abbrev ReferenceParameters (E : Type*) (n T : ℕ) :=
  (Fin (T + 1) → E) × (Fin n → Fin (T + 1) → E)

theorem variable_radial_continuous {X : Type*} [TopologicalSpace X] {U V : X → E}
    (hU : Continuous U) (hV : Continuous V) : Continuous (fun p ↦ radialCoordinate (U p) (V p)) :=
  (hU.inner hV).div ((continuous_const.add (hV.norm.pow 2)).sqrt) (fun _ ↦ by positivity)

theorem flatTruncated_family_continuous (h : ℕ) (ρ : ℝ) (i : Fin n) :
    Continuous (fun p : ReferenceParameters E n T × PrimalSpace (primalDimension E T) ↦
      flatTruncated h ρ p.1.1 p.1.2 i p.2) := by
  have hu (j : Fin (T + 1)) : Continuous (fun p : ReferenceParameters E n T × PrimalSpace (primalDimension E T) ↦ p.1.1 j) :=
    (continuous_apply j).comp continuous_fst.fst
  have hr (j : Fin (T + 1)) : Continuous (fun p : ReferenceParameters E n T × PrimalSpace (primalDimension E T) ↦ p.1.2 i j) :=
    (continuous_apply j).comp ((continuous_apply i).comp continuous_fst.snd)
  have hx (j : Fin (T + 1)) : Continuous (fun p : ReferenceParameters E n T × PrimalSpace (primalDimension E T) ↦
      ((primalCoordinates E T).symm p.2) j) :=
    (blockProjection (E := E) j).continuous.comp ((primalCoordinates E T).symm.continuous.comp continuous_snd)
  have hrow (j : Fin (T + 1)) : Continuous (fun p : ReferenceParameters E n T × PrimalSpace (primalDimension E T) ↦
      scaledRadialCoordinate ρ (p.1.2 i j) (((primalCoordinates E T).symm p.2) j)) :=
    continuous_const.mul (variable_radial_continuous (hr j) (hx j))
  have hcoord (j : Fin (T + 1)) : Continuous (fun p : ReferenceParameters E n T × PrimalSpace (primalDimension E T) ↦
      coordinate p.1.1 ((primalCoordinates E T).symm p.2) j) :=
    variable_radial_continuous (hu j) (hx j)
  have hlinks : Continuous (fun p : ReferenceParameters E n T × PrimalSpace (primalDimension E T) ↦
      ∑ j : Fin T, if j.val < h then link ρ p.1.1 p.1.2 i j ((primalCoordinates E T).symm p.2) else 0) := by
    apply continuous_finset_sum
    intro j hj
    by_cases hjh : j.val < h
    · simpa only [hjh, ite_true, link, Function.comp_apply] using
        (gate_contDiff.continuous.comp (hcoord j.castSucc)).fun_mul ((hrow j.succ).fun_add continuous_const)
    · simpa only [hjh, ite_false] using (continuous_const : Continuous
        (fun _ : ReferenceParameters E n T × PrimalSpace (primalDimension E T) ↦ (0 : ℝ)))
  exact ((hrow 0).neg.sub hlinks).add
    (continuous_const.mul (((primalCoordinates E T).symm.continuous.comp continuous_snd).norm.pow 2))

variable [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

theorem flatTruncated_gradient_measurable (h : ℕ) (ρ : ℝ) (i : Fin n) :
    Measurable (fun p : ReferenceParameters E n T × PrimalSpace (primalDimension E T) ↦
      gradient (flatTruncated h ρ p.1.1 p.1.2 i) p.2) := by
  have hd : Measurable (fun p : ReferenceParameters E n T × PrimalSpace (primalDimension E T) ↦
      fderiv ℝ (flatTruncated h ρ p.1.1 p.1.2 i) p.2) :=
    measurable_fderiv_with_param ℝ
      (f := fun p : ReferenceParameters E n T ↦ flatTruncated h ρ p.1 p.2 i)
      (flatTruncated_family_continuous h ρ i)
  exact (InnerProductSpace.toDual ℝ (PrimalSpace (primalDimension E T))).symm.continuous.measurable.comp hd

theorem referenceValueGradient_measurable (h : ℕ) (ρ : ℝ) (i : Fin n) :
    Measurable (fun p : ReferenceParameters E n T × PrimalSpace (primalDimension E T) ↦
      (flatTruncated h ρ p.1.1 p.1.2 i p.2, gradient (flatTruncated h ρ p.1.1 p.1.2 i) p.2, (0 : DualSpace 0))) :=
  (flatTruncated_family_continuous h ρ i).measurable.prodMk
    ((flatTruncated_gradient_measurable h ρ i).prodMk measurable_const)

theorem referenceReply_measurable (hn : 0 < n) {ρ : ℝ} (hρ : 0 < ρ) (h : ℕ) :
    Measurable (fun p : ReferenceParameters E n T ×
        OracleQuery n (primalDimension E T) (smoothDualDomain (parameters hn hρ T)) ↦
      referenceReply hn hρ h p.1.1 p.1.2 p.2) := by
  have hm : Measurable (fun p : Fin n × (ReferenceParameters E n T × PrimalSpace (primalDimension E T)) ↦
      (flatTruncated h ρ p.2.1.1 p.2.1.2 p.1 p.2.2,
        gradient (flatTruncated h ρ p.2.1.1 p.2.1.2 p.1) p.2.2, (0 : DualSpace 0))) :=
    measurable_from_prod_countable_right (fun i ↦ referenceValueGradient_measurable h ρ i)
  have hp : Measurable (fun p : ReferenceParameters E n T ×
        OracleQuery n (primalDimension E T) (smoothDualDomain (parameters hn hρ T)) ↦
      (p.2.1, (p.1, p.2.2.1))) :=
    (measurable_fst.comp measurable_snd).prodMk
      (measurable_fst.prodMk (measurable_fst.comp (measurable_snd.comp measurable_snd)))
  convert hm.comp hp using 1
  all_goals rfl

end

end NCConcave16991.DenseSmooth
