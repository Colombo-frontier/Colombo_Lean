import GradientHessian.GaussianConcentrationIBP
import Mathlib.MeasureTheory.Integral.Pi

/-! Coordinate integration by parts under an actual finite product of
standard Gaussian measures, with explicit integrability conditions. -/

noncomputable section
namespace GradientHessian.GaussianConcentration
open MeasureTheory ProbabilityTheory GaussianSquare

theorem gaussian_coordinate_integration_by_parts {m : ℕ} (i : Fin (m + 1))
    {f f' : (Fin (m + 1) → ℝ) → ℝ}
    (hd : ∀ v : Fin m → ℝ, ∀ t : ℝ,
      HasDerivAt (fun s => f (i.insertNth s v)) (f' (i.insertNth t v)) t)
    (hf : Integrable f (gaussianVector (m + 1)))
    (hf' : Integrable f' (gaussianVector (m + 1)))
    (hxf : Integrable (fun z => z i * f z) (gaussianVector (m + 1))) :
    (∫ z, z i * f z ∂gaussianVector (m + 1)) =
      ∫ z, f' z ∂gaussianVector (m + 1) := by
  let e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) i).symm
  have he : MeasurePreserving e ((gaussianReal 0 1).prod (gaussianVector m))
      (gaussianVector (m + 1)) :=
    (measurePreserving_piFinSuccAbove (fun _ : Fin (m + 1) => gaussianReal 0 1) i).symm
  have heval (t : ℝ) (v : Fin m → ℝ) : e (t, v) = i.insertNth t v := rfl
  have hip : Integrable (f ∘ e) ((gaussianReal 0 1).prod (gaussianVector m)) :=
    (he.integrable_comp_emb e.measurableEmbedding).mpr hf
  have hip' : Integrable (f' ∘ e) ((gaussianReal 0 1).prod (gaussianVector m)) :=
    (he.integrable_comp_emb e.measurableEmbedding).mpr hf'
  have hixp : Integrable ((fun z => z i * f z) ∘ e)
      ((gaussianReal 0 1).prod (gaussianVector m)) :=
    (he.integrable_comp_emb e.measurableEmbedding).mpr hxf
  rw [← he.integral_comp' (fun z => z i * f z), ← he.integral_comp' f']
  calc
    _ = ∫ v, ∫ t, e (t, v) i * f (e (t, v)) ∂gaussianReal 0 1 ∂gaussianVector m :=
      integral_prod_symm _ hixp
    _ = ∫ v, ∫ t, f' (e (t, v)) ∂gaussianReal 0 1 ∂gaussianVector m := by
      apply integral_congr_ae
      filter_upwards [hip.prod_left_ae, hip'.prod_left_ae, hixp.prod_left_ae] with v hv hv' hxv
      simp only [Function.comp_apply, heval, Fin.insertNth_apply_same] at hv hv' hxv ⊢
      exact standard_gaussian_integration_by_parts (hd v) hv hv' hxv
    _ = _ := (integral_prod_symm _ hip').symm

theorem gaussian_partial_integration_by_parts {m : ℕ} (i : Fin m)
    {f f' : (Fin m → ℝ) → ℝ}
    (hd : ∀ z, HasDerivAt (fun s => f (Function.update z i s)) (f' z) (z i))
    (hf : Integrable f (gaussianVector m))
    (hf' : Integrable f' (gaussianVector m))
    (hxf : Integrable (fun z => z i * f z) (gaussianVector m)) :
    (∫ z, z i * f z ∂gaussianVector m) = ∫ z, f' z ∂gaussianVector m := by
  cases m with
  | zero => exact Fin.elim0 i
  | succ m =>
    apply gaussian_coordinate_integration_by_parts i _ hf hf' hxf
    intro v t
    simpa only [Fin.update_insertNth, Fin.insertNth_apply_same] using hd (i.insertNth t v)

end GradientHessian.GaussianConcentration
