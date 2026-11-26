import Nonsmooth.C2StrongQuadraticPotential
import Nonsmooth.SoftSliceDerivatives

set_option autoImplicit false
namespace Nonsmooth
noncomputable section
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def planePoint (u v : E) (t x : ℝ) : E := t • v + x • u

theorem planePoint_continuous (u v : E) : Continuous (Function.uncurry (planePoint u v)) :=
  (continuous_fst.smul continuous_const).add (continuous_snd.smul continuous_const)

def planeSliceData (U : E → ℝ) (S : E → E →L[ℝ] ℝ)
    (A : E → E →L[ℝ] E →L[ℝ] ℝ)
    (hcU : Continuous U) (hcS : Continuous S) (hcA : Continuous A)
    (hdU : ∀ z, HasFDerivAt U (S z) z) (hdS : ∀ z, HasFDerivAt S (A z) z)
    (hsym : ∀ z p q, A z p q = A z q p) (u v : E) : SmoothSliceConstraints Unit := by
  have hp := planePoint_continuous u v
  have hx (t x : ℝ) : HasDerivAt (planePoint u v t) u x := by
    convert! ((hasDerivAt_id x).smul_const u).const_add (t • v) using 1 <;>
      first | rfl | (simpa only [one_smul]) | (funext y; simp only [planePoint, id_eq, add_comm])
  have ht (t x : ℝ) : HasDerivAt (fun r => planePoint u v r x) v t := by
    convert! ((hasDerivAt_id t).smul_const v).add_const (x • u) using 1 <;>
      first | rfl | (simpa only [one_smul]) | (funext y; simp only [planePoint, id_eq, add_comm])
  refine {
    value := fun _ t x => U (planePoint u v t x)
    dx := fun _ t x => S (planePoint u v t x) u
    dt := fun _ t x => S (planePoint u v t x) v
    dxx := fun _ t x => A (planePoint u v t x) u u
    dtx := fun _ t x => A (planePoint u v t x) u v
    dtt := fun _ t x => A (planePoint u v t x) v v
    value_cont := fun _ => hcU.comp hp
    dx_cont := fun _ => (hcS.comp hp).clm_apply continuous_const
    dt_cont := fun _ => (hcS.comp hp).clm_apply continuous_const
    dxx_cont := fun _ => ((hcA.comp hp).clm_apply continuous_const).clm_apply continuous_const
    dtx_cont := fun _ => ((hcA.comp hp).clm_apply continuous_const).clm_apply continuous_const
    dtt_cont := fun _ => ((hcA.comp hp).clm_apply continuous_const).clm_apply continuous_const
    value_dx := fun _ t x => (hdU (planePoint u v t x)).comp_hasDerivAt x (hx t x)
    value_dt := fun _ t x => (hdU (planePoint u v t x)).comp_hasDerivAt t (ht t x)
    dx_dx := ?_
    dx_dt := ?_
    dt_dx := ?_
    dt_dt := ?_
  }
  · intro _ t x
    exact (ContinuousLinearMap.apply ℝ ℝ u).hasFDerivAt.comp_hasDerivAt x
      ((hdS (planePoint u v t x)).comp_hasDerivAt x (hx t x))
  · intro _ t x
    rw [hsym (planePoint u v t x) u v]
    exact (ContinuousLinearMap.apply ℝ ℝ u).hasFDerivAt.comp_hasDerivAt t
      ((hdS (planePoint u v t x)).comp_hasDerivAt t (ht t x))
  · intro _ t x
    exact (ContinuousLinearMap.apply ℝ ℝ v).hasFDerivAt.comp_hasDerivAt x
      ((hdS (planePoint u v t x)).comp_hasDerivAt x (hx t x))
  · intro _ t x
    exact (ContinuousLinearMap.apply ℝ ℝ v).hasFDerivAt.comp_hasDerivAt t
      ((hdS (planePoint u v t x)).comp_hasDerivAt t (ht t x))

end
end Nonsmooth
