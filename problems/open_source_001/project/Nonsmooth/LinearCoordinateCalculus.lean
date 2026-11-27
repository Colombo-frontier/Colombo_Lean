import Nonsmooth.VectorCoordinateGrowth

set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def coordinatePoint (L : F →L[ℝ] E) (u : E) (t : F) (x : ℝ) : E := L t + x • u

def coordinatePrecompose (L : F →L[ℝ] E) : (E →L[ℝ] ℝ) →L[ℝ] F →L[ℝ] ℝ :=
  (ContinuousLinearMap.compL ℝ F E ℝ).flip L

def coordinatePotential (U : E → ℝ) (L : F →L[ℝ] E) (u : E) (t : F) (x : ℝ) : ℝ :=
  U (coordinatePoint L u t x)

def coordinateScore (S : E → E →L[ℝ] ℝ) (L : F →L[ℝ] E) (u : E) (t : F) (x : ℝ) : F →L[ℝ] ℝ :=
  coordinatePrecompose L (S (coordinatePoint L u t x))

def coordinateHessian (H : E → E →L[ℝ] E →L[ℝ] ℝ)
    (L : F →L[ℝ] E) (u : E) (t : F) (x : ℝ) : F →L[ℝ] F →L[ℝ] ℝ :=
  ((coordinatePrecompose L).comp (H (coordinatePoint L u t x))).comp L

theorem coordinatePoint_continuous (L : F →L[ℝ] E) (u : E) :
    Continuous (Function.uncurry (coordinatePoint L u)) :=
  (L.continuous.comp continuous_fst).add (continuous_snd.smul continuous_const)

theorem coordinatePotential_hasFDerivAt (U : E → ℝ) (S : E → E →L[ℝ] ℝ)
    (hd : ∀ z, HasFDerivAt U (S z) z) (L : F →L[ℝ] E) (u : E) (t : F) (x : ℝ) :
    HasFDerivAt (fun r => coordinatePotential U L u r x) (coordinateScore S L u t x) t :=
  (hd (coordinatePoint L u t x)).comp t (L.hasFDerivAt.add_const (x • u))

theorem coordinateScore_hasFDerivAt (S : E → E →L[ℝ] ℝ)
    (H : E → E →L[ℝ] E →L[ℝ] ℝ) (hd : ∀ z, HasFDerivAt S (H z) z)
    (L : F →L[ℝ] E) (u : E) (t : F) (x : ℝ) :
    HasFDerivAt (fun r => coordinateScore S L u r x) (coordinateHessian H L u t x) t := by
  have hc : HasFDerivAt (fun z => coordinatePrecompose L (S z))
      ((coordinatePrecompose L).comp (H (coordinatePoint L u t x))) (coordinatePoint L u t x) :=
    (coordinatePrecompose L).hasFDerivAt.comp (coordinatePoint L u t x)
      (hd (coordinatePoint L u t x))
  exact hc.comp t (L.hasFDerivAt.add_const (x • u))

theorem coordinatePotential_hasDerivAt_x (U : E → ℝ) (S : E → E →L[ℝ] ℝ)
    (hd : ∀ z, HasFDerivAt U (S z) z) (L : F →L[ℝ] E) (u : E) (t : F) (x : ℝ) :
    HasDerivAt (coordinatePotential U L u t) (S (coordinatePoint L u t x) u) x := by
  apply (hd (coordinatePoint L u t x)).comp_hasDerivAt x
  change HasDerivAt (fun y : ℝ => L t + y • u) u x
  simpa only [one_smul, id_eq] using ((hasDerivAt_id x).smul_const u).const_add (L t)

theorem coordinateScore_hasDerivAt_x (S : E → E →L[ℝ] ℝ)
    (H : E → E →L[ℝ] E →L[ℝ] ℝ) (hd : ∀ z, HasFDerivAt S (H z) z)
    (L : F →L[ℝ] E) (u : E) (t : F) (x : ℝ) :
    HasDerivAt (coordinateScore S L u t)
      (coordinatePrecompose L (H (coordinatePoint L u t x) u)) x := by
  apply (coordinatePrecompose L).hasFDerivAt.comp_hasDerivAt x
  apply (hd (coordinatePoint L u t x)).comp_hasDerivAt x
  change HasDerivAt (fun y : ℝ => L t + y • u) u x
  simpa only [one_smul, id_eq] using ((hasDerivAt_id x).smul_const u).const_add (L t)

theorem coordinateDx_hasDerivAt_x (S : E → E →L[ℝ] ℝ)
    (H : E → E →L[ℝ] E →L[ℝ] ℝ) (hd : ∀ z, HasFDerivAt S (H z) z)
    (L : F →L[ℝ] E) (u : E) (t : F) (x : ℝ) :
    HasDerivAt (fun x => S (coordinatePoint L u t x) u) (H (coordinatePoint L u t x) u u) x := by
  apply (ContinuousLinearMap.apply ℝ ℝ u).hasFDerivAt.comp_hasDerivAt x
  apply (hd (coordinatePoint L u t x)).comp_hasDerivAt x
  change HasDerivAt (fun y : ℝ => L t + y • u) u x
  simpa only [one_smul, id_eq] using ((hasDerivAt_id x).smul_const u).const_add (L t)

theorem coordinate_data_continuous (U : E → ℝ) (S : E → E →L[ℝ] ℝ)
    (H : E → E →L[ℝ] E →L[ℝ] ℝ)
    (hU : Continuous U) (hS : Continuous S) (hH : Continuous H) (L : F →L[ℝ] E) (u : E) :
    Continuous (Function.uncurry (coordinatePotential U L u)) ∧
    Continuous (Function.uncurry (coordinateScore S L u)) ∧
    Continuous (Function.uncurry (coordinateHessian H L u)) := by
  have hp := coordinatePoint_continuous L u
  refine ⟨hU.comp hp, (coordinatePrecompose L).continuous.comp (hS.comp hp), ?_⟩
  exact (continuous_const.clm_comp (hH.comp hp)).clm_comp_const L

end
end Nonsmooth
