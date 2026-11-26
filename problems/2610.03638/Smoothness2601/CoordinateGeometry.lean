import Smoothness2601.Population
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Tactic

/-! Exact Euclidean coordinate changes for full gradients and all finite jets.
The lower coordinate change is a surjective linear isometry. -/
noncomputable section
open Bilevel.PrimitiveGeometry
open scoped RealInnerProductSpace
namespace Smoothness2601.CoordinateGeometry

variable {X Y Z E F G : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
  [NormedAddCommGroup Z] [InnerProductSpace ℝ Z]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G]

def joint (e : Z ≃ₗᵢ[ℝ] Y) : Joint X Z ≃ₗᵢ[ℝ] Joint X Y where
  toLinearEquiv := (WithLp.prodContinuousLinearEquiv 2 ℝ X Z).toLinearEquiv.trans
    (((LinearEquiv.refl ℝ X).prodCongr e.toLinearEquiv).trans
      (WithLp.prodContinuousLinearEquiv 2 ℝ X Y).symm.toLinearEquiv)
  norm_map' z := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    change ‖pack z.fst (e z.snd)‖ ^ 2 = ‖z‖ ^ 2
    rw [norm_sq,norm_sq]
    simp only [pack,WithLp.equiv_symm_fst,WithLp.equiv_symm_snd,e.norm_map]

@[simp] theorem joint_apply (e : Z ≃ₗᵢ[ℝ] Y) (z : Joint X Z) :
    joint e z = pack z.fst (e z.snd) := rfl

@[simp] theorem joint_symm_apply (e : Z ≃ₗᵢ[ℝ] Y) (z : Joint X Y) :
    (joint e).symm z = pack z.fst (e.symm z.snd) := rfl

theorem gradient_pullback [CompleteSpace E] [CompleteSpace F] (e : E ≃ₗᵢ[ℝ] F) {f : F → ℝ} {g : F} {x : E}
    (hf : HasGradientAt f g (e x)) : HasGradientAt (f ∘ e) (e.symm g) x := by
  apply hasGradientAt_iff_hasFDerivAt.mpr
  convert hf.hasFDerivAt.comp x e.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt using 1
  ext v
  change ⟪e.symm g,v⟫ = ⟪g,e v⟫
  simpa only [e.apply_symm_apply] using (e.inner_map_map (e.symm g) v).symm

def operator (e : Z ≃ₗᵢ[ℝ] Y) (d : E ≃ₗᵢ[ℝ] F) (A : Y →L[ℝ] E) : Z →L[ℝ] F :=
  d.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (A.comp e.toContinuousLinearEquiv.toContinuousLinearMap)

theorem operator_norm_le (e : Z ≃ₗᵢ[ℝ] Y) (d : E ≃ₗᵢ[ℝ] F) (A : Y →L[ℝ] E) :
    ‖operator e d A‖ ≤ ‖A‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro z
  simpa only [operator,ContinuousLinearMap.comp_apply,LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    ContinuousLinearEquiv.coe_coe,LinearIsometryEquiv.norm_map] using A.le_opNorm (e z)

theorem operator_sub (e : Z ≃ₗᵢ[ℝ] Y) (d : E ≃ₗᵢ[ℝ] F) (A B : Y →L[ℝ] E) :
    operator e d A-operator e d B = operator e d (A-B) := by
  ext z
  simp [operator,map_sub]

def jet (e : Z ≃ₗᵢ[ℝ] Y) (d : E ≃ₗᵢ[ℝ] F) {q : ℕ}
    (A : ContinuousMultilinearMap ℝ (fun _ : Fin q => Y) E) :
    ContinuousMultilinearMap ℝ (fun _ : Fin q => Z) F :=
  d.toContinuousLinearEquiv.toContinuousLinearMap.compContinuousMultilinearMap
    (A.compContinuousLinearMap (fun _ => e.toContinuousLinearEquiv.toContinuousLinearMap))

theorem jet_norm (e : Z ≃ₗᵢ[ℝ] Y) (d : E ≃ₗᵢ[ℝ] F) {q : ℕ}
    (A : ContinuousMultilinearMap ℝ (fun _ : Fin q => Y) E) : ‖jet e d A‖ = ‖A‖ := by
  change ‖d.toLinearIsometry.toContinuousLinearMap.compContinuousMultilinearMap
    (A.compContinuousLinearMap (fun _ => e.toContinuousLinearEquiv.toContinuousLinearMap))‖ = _
  rw [LinearIsometry.norm_compContinuousMultilinearMap d.toLinearIsometry]
  exact A.norm_compContinuous_linearIsometryEquiv (fun _ => e)

theorem jet_sub (e : Z ≃ₗᵢ[ℝ] Y) (d : E ≃ₗᵢ[ℝ] F) {q : ℕ}
    (A B : ContinuousMultilinearMap ℝ (fun _ : Fin q => Y) E) :
    jet e d A-jet e d B = jet e d (A-B) := by
  ext z
  simp [jet,map_sub]

theorem iterated_pullback (e : Z ≃ₗᵢ[ℝ] Y) (d : E ≃ₗᵢ[ℝ] F) {f : Y → E} {q : ℕ}
    (hf : ContDiff ℝ q f) (z : Z) :
    iteratedFDeriv ℝ q (d ∘ f ∘ e) z = jet e d (iteratedFDeriv ℝ q f (e z)) := by
  change iteratedFDeriv ℝ q (d.toContinuousLinearEquiv.toContinuousLinearMap ∘
    (f ∘ e.toContinuousLinearEquiv.toContinuousLinearMap)) z = _
  have hh : ContDiff ℝ q (f ∘ e.toContinuousLinearEquiv.toContinuousLinearMap) :=
    hf.comp e.toContinuousLinearEquiv.toContinuousLinearMap.contDiff
  rw [ContinuousLinearMap.iteratedFDeriv_comp_left
    d.toContinuousLinearEquiv.toContinuousLinearMap (hh.contDiffAt (x := z)) le_rfl,
    ContinuousLinearMap.iteratedFDeriv_comp_right
      e.toContinuousLinearEquiv.toContinuousLinearMap hf z le_rfl]
  rfl

theorem iterated_difference_norm (e : Z ≃ₗᵢ[ℝ] Y) (d : E ≃ₗᵢ[ℝ] F) {f : Y → E} {q : ℕ}
    (hf : ContDiff ℝ q f) (u v : Z) :
    ‖iteratedFDeriv ℝ q (d ∘ f ∘ e) u-iteratedFDeriv ℝ q (d ∘ f ∘ e) v‖ =
      ‖iteratedFDeriv ℝ q f (e u)-iteratedFDeriv ℝ q f (e v)‖ := by
  rw [iterated_pullback e d hf,iterated_pullback e d hf,jet_sub,jet_norm]

end Smoothness2601.CoordinateGeometry
