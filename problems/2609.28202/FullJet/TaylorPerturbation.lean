import FullJet.TaylorModel

open scoped BigOperators ContDiff

namespace FullJet

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {p : ℕ}

theorem tensor_diagonal_norm {m : ℕ} (A : E [×m]→L[ℝ] ℝ) (h : E) :
    ‖A (fun _ => h)‖ ≤ ‖A‖ * ‖h‖ ^ m := by
  simpa using A.le_opNorm (fun _ => h)

theorem tensor_slot_norm {m : ℕ} (A : E [×(m + 1)]→L[ℝ] ℝ) (h : E) (i : Fin (m + 1)) :
    ‖A.toContinuousLinearMap (fun _ => h) i‖ ≤ ‖A‖ * ‖h‖ ^ m := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  have ha := A.le_opNorm (Function.update (fun _ => h) i v)
  calc
    ‖A.toContinuousLinearMap (fun _ => h) i v‖
        ≤ ‖A‖ * ∏ j, ‖Function.update (fun _ => h) i v j‖ := ha
    _ = (‖A‖ * ‖h‖ ^ m) * ‖v‖ := by
      rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
      simp only [Function.update_self]
      have he : (∏ j ∈ Finset.univ.erase i, ‖Function.update (fun _ => h) i v j‖) = ‖h‖ ^ m := by
        calc
          _ = ∏ _j ∈ Finset.univ.erase i, ‖h‖ := by
            apply Finset.prod_congr rfl
            intro j hj
            rw [Function.update_of_ne (Finset.mem_erase.mp hj).1]
          _ = _ := by simp
      rw [he, mul_assoc]

theorem tensor_diagonal_fderiv {m : ℕ} (A : E [×m]→L[ℝ] ℝ) (h : E) :
    fderiv ℝ (fun y => A (fun _ => y)) h = ∑ i, A.toContinuousLinearMap (fun _ => h) i := by
  have hd := HasFDerivAt.multilinear_comp A (fun _ : Fin m => hasFDerivAt_id h)
  simpa using hd.fderiv

theorem tensor_diagonal_fderiv_norm {m : ℕ} (A : E [×(m + 1)]→L[ℝ] ℝ) (h : E) :
    ‖fderiv ℝ (fun y => A (fun _ => y)) h‖ ≤ (m + 1 : ℝ) * ‖A‖ * ‖h‖ ^ m := by
  rw [tensor_diagonal_fderiv]
  calc
    _ ≤ ∑ i : Fin (m + 1), ‖A.toContinuousLinearMap (fun _ => h) i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin (m + 1), ‖A‖ * ‖h‖ ^ m := Finset.sum_le_sum (fun i _ => tensor_slot_norm A h i)
    _ = _ := by simp; ring

theorem jetTaylor_sub (J K : JetPacket p E) (h : E) :
    jetTaylor (J - K) h = jetTaylor J h - jetTaylor K h := by
  unfold jetTaylor
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  change ((j.val + 1).factorial : ℝ)⁻¹ *
    (J j.succ (fun _ => h) - K j.succ (fun _ => h)) = _
  ring

theorem jetTaylor_norm (J : JetPacket p E) (h : E) :
    ‖jetTaylor J h‖ ≤ ∑ j : Fin p,
      ((j.val + 1).factorial : ℝ)⁻¹ * ‖J j.succ‖ * ‖h‖ ^ (j.val + 1) := by
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro j _
  rw [norm_mul, Real.norm_of_nonneg (by positivity)]
  exact (mul_le_mul_of_nonneg_left (tensor_diagonal_norm (J j.succ) h) (by positivity)).trans_eq
    (by simp only [Fin.val_succ]; ring)

theorem jetTaylor_perturbation (J K : JetPacket p E) (h : E) :
    ‖jetTaylor J h - jetTaylor K h‖ ≤ ∑ j : Fin p,
      ((j.val + 1).factorial : ℝ)⁻¹ * ‖J j.succ - K j.succ‖ * ‖h‖ ^ (j.val + 1) := by
  rw [← jetTaylor_sub]
  exact jetTaylor_norm (J - K) h

theorem jetTaylor_fderiv (J : JetPacket p E) (h : E) :
    fderiv ℝ (jetTaylor J) h = ∑ j : Fin p,
      ((j.val + 1).factorial : ℝ)⁻¹ • fderiv ℝ (fun y => J j.succ (fun _ => y)) h := by
  have hd (j : Fin p) : Differentiable ℝ (fun y => J j.succ (fun _ => y)) :=
    ((J j.succ).contDiff (n := 1) |>.comp (contDiff_pi.mpr fun _ => contDiff_id)).differentiable le_rfl
  unfold jetTaylor
  rw [fderiv_sum (fun j _ => (hd j h).const_mul _)]
  apply Finset.sum_congr rfl
  intro j _
  exact fderiv_const_mul (hd j h) _

theorem jetTaylor_fderiv_norm (J : JetPacket p E) (h : E) :
    ‖fderiv ℝ (jetTaylor J) h‖ ≤ ∑ j : Fin p,
      (j.val.factorial : ℝ)⁻¹ * ‖J j.succ‖ * ‖h‖ ^ j.val := by
  rw [jetTaylor_fderiv]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro j _
  change ‖((j.val + 1).factorial : ℝ)⁻¹ •
    (fderiv ℝ (fun y : E => J j.succ (fun _ => y)) h : E →L[ℝ] ℝ)‖ ≤ _
  have hs := norm_smul ((j.val + 1).factorial : ℝ)⁻¹
    (fderiv ℝ (fun y : E => J j.succ (fun _ => y)) h)
  rw [hs, Real.norm_of_nonneg (by positivity)]
  have hb := mul_le_mul_of_nonneg_left (tensor_diagonal_fderiv_norm (J j.succ) h)
    (show 0 ≤ ((j.val + 1).factorial : ℝ)⁻¹ by positivity)
  apply hb.trans_eq
  rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  field_simp
  ring

theorem jetTaylor_fderiv_perturbation (J K : JetPacket p E) (h : E) :
    ‖fderiv ℝ (jetTaylor J) h - fderiv ℝ (jetTaylor K) h‖ ≤ ∑ j : Fin p,
      (j.val.factorial : ℝ)⁻¹ * ‖J j.succ - K j.succ‖ * ‖h‖ ^ j.val := by
  have hd (A : JetPacket p E) : Differentiable ℝ (jetTaylor A) :=
    (jetTaylor_contDiff A).differentiable (by simp)
  have heq : jetTaylor (J - K) = fun y => jetTaylor J y - jetTaylor K y :=
    funext (jetTaylor_sub J K)
  have hn := jetTaylor_fderiv_norm (J - K) h
  rwa [heq, fderiv_sub (hd J h) (hd K h)] at hn

end FullJet
