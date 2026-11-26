import FullJet.SmoothTaylorBounds
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

open scoped BigOperators ContDiff

namespace FullJet

universe u

variable {E F : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem iteratedFDeriv_two_evaluations {k : ℕ} {g : E → E →L[ℝ] E →L[ℝ] F}
    (hg : ContDiff ℝ k g) (x v w : E) (u : Fin k → E) :
    iteratedFDeriv ℝ k g x u v w = iteratedFDeriv ℝ k (fun y => g y v w) x u := by
  let A : (E →L[ℝ] E →L[ℝ] F) →L[ℝ] F :=
    (ContinuousLinearMap.apply ℝ F w).comp (ContinuousLinearMap.apply ℝ (E →L[ℝ] F) v)
  have he := A.iteratedFDeriv_comp_left (x := x) hg.contDiffAt (i := k) le_rfl
  have hh := congrArg (fun B : E [×k]→L[ℝ] F => B u) he
  exact hh.symm

/-- C^(k+2) suffices to exchange the last two slots. This follows by
differentiating the C² Schwarz identity k more times, with fixed directions. -/
theorem iteratedFDeriv_last_two_swap {f : E → F} {k : ℕ}
    (hf : ContDiff ℝ (k + 2) f) (x v w : E) (u : Fin k → E) :
    iteratedFDeriv ℝ (k + 2) f x (Fin.snoc (Fin.snoc u v) w) =
      iteratedFDeriv ℝ (k + 2) f x (Fin.snoc (Fin.snoc u w) v) := by
  have hD₁ : ContDiff ℝ (k + 1) (fderiv ℝ f) := hf.fderiv_right
    (by exact_mod_cast (show k + 1 + 1 ≤ k + 2 by omega))
  have hD : ContDiff ℝ k (fderiv ℝ (fderiv ℝ f)) := hD₁.fderiv_right (by simp)
  have he : (fun y => fderiv ℝ (fderiv ℝ f) y v w) =
      (fun y => fderiv ℝ (fderiv ℝ f) y w v) := by
    funext y
    exact hf.contDiffAt.isSymmSndFDerivAt (by simp [minSmoothness]) v w
  simp only [iteratedFDeriv_succ_apply_right, Fin.init_snoc, Fin.snoc_last]
  rw [iteratedFDeriv_two_evaluations hD x v w u, he,
    ← iteratedFDeriv_two_evaluations hD x w v u]

/-- With all other slots equal, the location of the remaining direction
does not matter for a genuine C^(m+1) jet. -/
theorem iteratedFDeriv_single_slot {m : ℕ} {f : E → F}
    (hf : ContDiff ℝ (m + 1) f) (x h v : E) (i : Fin (m + 1)) :
    iteratedFDeriv ℝ (m + 1) f x (Function.update (fun _ => h) i v) =
      iteratedFDeriv ℝ m (fderiv ℝ f) x (fun _ => h) v := by
  induction m generalizing F with
  | zero =>
    have hi : i = 0 := Fin.ext (by omega)
    simp [hi, iteratedFDeriv_one_apply]
  | succ m ih =>
    cases i using Fin.lastCases with
    | last =>
      rw [iteratedFDeriv_succ_apply_right]
      simp only [Fin.init_update_last, Function.update_self]
      rfl
    | cast i =>
      have hD : ContDiff ℝ (m + 1) (fderiv ℝ f) := hf.fderiv_right (by simp)
      have he := congrArg (fun A : E →L[ℝ] F => A h) (ih (F := E →L[ℝ] F) hD i)
      have hs := iteratedFDeriv_last_two_swap hf x v h (fun _ : Fin m => h)
      simp only [iteratedFDeriv_succ_apply_right, Fin.init_snoc, Fin.snoc_last] at hs
      rw [iteratedFDeriv_succ_apply_right, Fin.init_update_castSucc]
      rw [Function.update_of_ne (Fin.castSucc_ne_last i).symm]
      change iteratedFDeriv ℝ (m + 1) (fderiv ℝ f) x
        (Function.update (fun _ => h) i v) h = _
      apply he.trans
      rw [iteratedFDeriv_succ_apply_right]
      exact hs

end FullJet
