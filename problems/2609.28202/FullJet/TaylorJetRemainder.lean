import FullJet.FiniteJetSymmetry

open scoped BigOperators ContDiff

namespace FullJet

universe u

variable {E F : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem vector_tensor_diagonal_fderiv {f : E → F} {m : ℕ}
    (hf : ContDiff ℝ (m + 1) f) (x h : E) :
    fderiv ℝ (fun y => iteratedFDeriv ℝ (m + 1) f x (fun _ => y)) h =
      (m + 1 : ℝ) • iteratedFDeriv ℝ m (fderiv ℝ f) x (fun _ => h) := by
  have hd := (HasFDerivAt.multilinear_comp (iteratedFDeriv ℝ (m + 1) f x)
    (fun _ : Fin (m + 1) => hasFDerivAt_id h)).fderiv
  simp only [ContinuousLinearMap.comp_id, id_eq] at hd
  rw [hd]
  ext v
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply]
  change (∑ i : Fin (m + 1), iteratedFDeriv ℝ (m + 1) f x (Function.update (fun _ => h) i v)) = _
  simp only [iteratedFDeriv_single_slot hf x h v, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℝ, Nat.cast_add, Nat.cast_one]

theorem lineTaylor_fderiv {f : E → F} {k : ℕ} (hf : ContDiff ℝ (k + 1) f) (x h : E) :
    fderiv ℝ (lineTaylor f (k + 1) x) h = lineTaylor (fderiv ℝ f) k x h := by
  have he : lineTaylor f (k + 1) x = fun y => f x +
      ∑ j : Fin (k + 1), ((j.val + 1).factorial : ℝ)⁻¹ • iteratedFDeriv ℝ (j.val + 1) f x (fun _ => y) := by
    funext y
    rw [lineTaylor, Fin.sum_univ_succ]
    simp only [Fin.val_zero, Nat.factorial_zero, Nat.cast_one, inv_one,
      iteratedFDeriv_zero_apply, one_smul, Fin.val_succ]
  have hd (j : Fin (k + 1)) : Differentiable ℝ (fun y => iteratedFDeriv ℝ (j.val + 1) f x (fun _ => y)) :=
    ((iteratedFDeriv ℝ (j.val + 1) f x).contDiff (n := 1) |>.comp
      (contDiff_pi.mpr fun _ => contDiff_id)).differentiable le_rfl
  rw [he, fderiv_const_add, fderiv_sum (fun j _ => (hd j h).const_smul _)]
  unfold lineTaylor
  apply Finset.sum_congr rfl
  intro j _
  rw [fderiv_const_smul (hd j h), vector_tensor_diagonal_fderiv
    (hf.of_le (by exact_mod_cast j.isLt)), smul_smul]
  congr 1
  rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  field_simp

theorem iteratedFDeriv_succ_sub_norm (f g : E → F) (j : ℕ) (x y : E) :
    ‖iteratedFDeriv ℝ (j + 1) f x - iteratedFDeriv ℝ (j + 1) g y‖ =
      ‖iteratedFDeriv ℝ j (fderiv ℝ f) x - iteratedFDeriv ℝ j (fderiv ℝ g) y‖ := by
  simp only [iteratedFDeriv_succ_eq_comp_right, Function.comp_apply]
  exact (continuousMultilinearCurryRightEquiv' ℝ j E F).symm.dist_map _ _

theorem iteratedFDeriv_zero_sub_norm (f g : E → F) (x y : E) :
    ‖iteratedFDeriv ℝ 0 f x - iteratedFDeriv ℝ 0 g y‖ = ‖f x - g y‖ := by
  simp only [iteratedFDeriv_zero_eq_comp, Function.comp_apply]
  simpa only [dist_eq_norm] using (continuousMultilinearCurryFin0 ℝ E F).symm.dist_map (f x) (g y)

/-- Every derivative of the Taylor polynomial approximates the corresponding
true derivative, with a dimension-free error under the original C^p,Lip(D^p) class. -/
theorem lineTaylor_jet_remainder {q j : ℕ} {f : E → F}
    (hf : ContDiff ℝ (q + j) f) (L : ℝ) (hL : 0 ≤ L)
    (hlip : ∀ a b, ‖iteratedFDeriv ℝ (q + j) f a - iteratedFDeriv ℝ (q + j) f b‖ ≤ L * ‖a - b‖)
    (x h : E) :
    ‖iteratedFDeriv ℝ j f (x + h) - iteratedFDeriv ℝ j (lineTaylor f (q + j) x) h‖ ≤
      L * ‖h‖ ^ (q + 1) := by
  induction j generalizing F with
  | zero =>
    rw [iteratedFDeriv_zero_sub_norm]
    exact lineTaylor_remainder hf L hL hlip x h
  | succ j ih =>
    have hD : ContDiff ℝ (q + j) (fderiv ℝ f) := hf.fderiv_right
      (by exact_mod_cast (show q + j + 1 ≤ q + (j + 1) by omega))
    have hDl : ∀ a b, ‖iteratedFDeriv ℝ (q + j) (fderiv ℝ f) a -
        iteratedFDeriv ℝ (q + j) (fderiv ℝ f) b‖ ≤ L * ‖a - b‖ := by
      intro a b
      rw [← iteratedFDeriv_succ_sub_norm]
      exact hlip a b
    have he : fderiv ℝ (lineTaylor f (q + (j + 1)) x) = lineTaylor (fderiv ℝ f) (q + j) x := by
      funext y
      exact lineTaylor_fderiv hf x y
    rw [iteratedFDeriv_succ_sub_norm, he]
    exact ih hD hDl

end FullJet
