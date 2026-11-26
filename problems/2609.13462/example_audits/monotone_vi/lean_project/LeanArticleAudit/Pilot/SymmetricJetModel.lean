import LeanArticleAudit.Pilot.Oracle
import LeanArticleAudit.Pilot.RadialModel

open Set
open scoped BigOperators RealInnerProductSpace

namespace LeanArticleAudit.Pilot

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

noncomputable def diagonalCLM (n : ℕ) : E →L[ℝ] (Fin n → E) :=
  ContinuousLinearMap.pi fun _ ↦ ContinuousLinearMap.id ℝ E

@[simp] theorem diagonalCLM_apply (n : ℕ) (h : E) :
    diagonalCLM (E := E) n h = fun _ ↦ h := rfl

/-- Taylor polynomial determined by a symmetric exact-jet payload. -/
noncomputable def symmetricJetTaylor (p : ℕ) (x : E)
    (jet : SymmetricExactJet E p) (y : E) : E :=
  ∑ j : Fin p, (Nat.factorial j.1 : ℝ)⁻¹ •
    (jet j).1 (fun _ ↦ y - x)

/-- The literal Fréchet derivative of the preceding finite polynomial. -/
noncomputable def symmetricJetTaylorDerivative (p : ℕ) (x : E)
    (jet : SymmetricExactJet E p) (y : E) : E →L[ℝ] E :=
  ∑ j : Fin p, (Nat.factorial j.1 : ℝ)⁻¹ •
    ((jet j).1.linearDeriv (fun _ ↦ y - x)).comp (diagonalCLM j.1)

theorem hasFDerivAt_symmetricJetTaylor (p : ℕ) (x : E)
    (jet : SymmetricExactJet E p) (y : E) :
    HasFDerivAt (symmetricJetTaylor p x jet)
      (symmetricJetTaylorDerivative p x jet y) y := by
  classical
  unfold symmetricJetTaylor symmetricJetTaylorDerivative
  have hterm (j : Fin p) : HasFDerivAt
      (fun z : E ↦ (Nat.factorial j.1 : ℝ)⁻¹ •
        (jet j).1 (fun _ ↦ z - x))
      ((Nat.factorial j.1 : ℝ)⁻¹ •
        ((jet j).1.linearDeriv (fun _ ↦ y - x)).comp (diagonalCLM j.1)) y := by
    have haff : HasFDerivAt (fun z : E ↦ (fun _ : Fin j.1 ↦ z - x))
        (diagonalCLM j.1) y := by
      unfold diagonalCLM
      exact hasFDerivAt_pi.mpr fun _ ↦ (hasFDerivAt_id y).sub_const x
    exact (((jet j).1.hasFDerivAt (fun _ ↦ y - x)).comp y haff).const_smul
      ((Nat.factorial j.1 : ℝ)⁻¹)
  have hs := HasFDerivAt.sum (u := Finset.univ) fun j _ ↦ hterm j
  convert hs using 1
  funext z
  simp only [Finset.sum_apply]

theorem fderiv_symmetricJetTaylor (p : ℕ) (x : E)
    (jet : SymmetricExactJet E p) (y : E) :
    fderiv ℝ (symmetricJetTaylor p x jet) y =
      symmetricJetTaylorDerivative p x jet y :=
  (hasFDerivAt_symmetricJetTaylor p x jet y).fderiv

theorem symmetricJetTaylor_eq_taylorModel (p : ℕ) (F : E → E) (x : E)
    (jet : SymmetricExactJet E p)
    (hexact : ∀ j : Fin p, (jet j).1 = iteratedFDeriv ℝ j.1 F x) :
    symmetricJetTaylor p x jet = taylorModel p F x := by
  funext y
  rw [symmetricJetTaylor, taylorModel]
  simp_rw [hexact]
  exact Fin.sum_univ_eq_sum_range (fun j : ℕ ↦
    (Nat.factorial j : ℝ)⁻¹ • iteratedFDeriv ℝ j F x (fun _ ↦ y - x)) p

/-- Explicit derivative equality for a Taylor model represented by an exact
symmetric jet.  This closes the ambiguity between the displayed polynomial
and its Fréchet derivative. -/
theorem fderiv_taylorModel_eq_symmetricJetTaylorDerivative
    (p : ℕ) (F : E → E) (x : E) (jet : SymmetricExactJet E p)
    (hexact : ∀ j : Fin p, (jet j).1 = iteratedFDeriv ℝ j.1 F x) (y : E) :
    fderiv ℝ (taylorModel p F x) y = symmetricJetTaylorDerivative p x jet y := by
  rw [← symmetricJetTaylor_eq_taylorModel p F x jet hexact]
  exact fderiv_symmetricJetTaylor p x jet y

private theorem symmetric_update_eq_last (n : ℕ)
    (A : SymmetricContinuousMultilinearMap E (n + 1)) (s h : E)
    (i : Fin (n + 1)) :
    A.1 (Function.update (fun _ ↦ s) i h) =
      A.1 (Function.update (fun _ ↦ s) (Fin.last n) h) := by
  let σ : Equiv.Perm (Fin (n + 1)) := Equiv.swap i (Fin.last n)
  have hs := A.2 σ
  have heval := DFunLike.congr_fun hs (Function.update (fun _ ↦ s) (Fin.last n) h)
  rw [ContinuousMultilinearMap.domDomCongr_apply] at heval
  rw [← heval]
  congr 1
  funext k
  by_cases hki : k = i <;> by_cases hkl : k = Fin.last n <;>
    simp [σ, Function.update, Equiv.swap_apply_def, hki, hkl] at * <;> subst_vars
  all_goals simp [eq_comm]

private theorem symmetric_linearDeriv_diagonal (n : ℕ)
    (A : SymmetricContinuousMultilinearMap E (n + 1)) (s h : E) :
    A.1.linearDeriv (fun _ ↦ s) (fun _ ↦ h) =
      (n + 1 : ℝ) • A.1 (Function.update (fun _ ↦ s) (Fin.last n) h) := by
  rw [ContinuousMultilinearMap.linearDeriv_apply]
  simp_rw [symmetric_update_eq_last n A s h]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  simpa using (Nat.cast_smul_eq_nsmul ℝ (n + 1)
    (A.1 (Function.update (fun _ ↦ s) (Fin.last n) h))).symm

noncomputable def shiftedSymmetricJetDerivative (q : ℕ) (x : E)
    (jet : SymmetricExactJet E (q + 1)) (y : E) : E →L[ℝ] E :=
  ∑ i : Fin q, (Nat.factorial i.1 : ℝ)⁻¹ •
    (jet ⟨i.1 + 1, by omega⟩).1.curryRight (fun _ ↦ y - x)

theorem symmetricJetTaylorDerivative_eq_shifted (q : ℕ) (x : E)
    (jet : SymmetricExactJet E (q + 1)) (y : E) :
    symmetricJetTaylorDerivative (q + 1) x jet y =
      shiftedSymmetricJetDerivative q x jet y := by
  classical
  ext h
  rw [symmetricJetTaylorDerivative, shiftedSymmetricJetDerivative,
    ContinuousLinearMap.sum_apply, ContinuousLinearMap.sum_apply]
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, Nat.factorial_zero, Nat.cast_one, inv_one, one_smul,
    ContinuousLinearMap.comp_apply, diagonalCLM_apply,
    ContinuousMultilinearMap.linearDeriv_apply, Finset.univ_eq_empty, Finset.sum_empty,
    zero_add]
  apply Finset.sum_congr rfl
  intro i _
  simp only [smul_apply, ContinuousLinearMap.comp_apply,
    diagonalCLM_apply]
  change (Nat.factorial (i.1 + 1) : ℝ)⁻¹ •
      (((jet i.succ).1.linearDeriv (fun _ ↦ y - x)) (fun _ ↦ h)) = _
  have hd := symmetric_linearDeriv_diagonal i.1 (jet i.succ) (y - x) h
  calc
    (Nat.factorial (i.1 + 1) : ℝ)⁻¹ •
        (((jet i.succ).1.linearDeriv (fun _ ↦ y - x)) (fun _ ↦ h)) =
      (Nat.factorial (i.1 + 1) : ℝ)⁻¹ •
        ((i.1 + 1 : ℝ) • (jet i.succ).1
          (Function.update (fun _ ↦ y - x) (Fin.last i.1) h)) :=
      congrArg (fun z : E ↦ (Nat.factorial (i.1 + 1) : ℝ)⁻¹ • z) hd
    _ = (Nat.factorial i.1 : ℝ)⁻¹ •
        ((jet ⟨i.1 + 1, by omega⟩).1.curryRight (fun _ ↦ y - x)) h := by
      rw [ContinuousMultilinearMap.curryRight_apply]
      have harg : Function.update (fun _ : Fin (i.1 + 1) ↦ y - x)
          (Fin.last i.1) h = Fin.snoc (fun _ : Fin i.1 ↦ y - x) h := by
        funext k
        by_cases hk : k = Fin.last i.1
        · subst k
          simp [Fin.snoc, Function.update]
        · have hkne : k.1 ≠ i.1 := by
            intro heq
            apply hk
            apply Fin.ext
            simpa using heq
          have hklt : k.1 < i.1 := by omega
          simp [Fin.snoc, Function.update, hk, hklt]
      change (Nat.factorial (i.1 + 1) : ℝ)⁻¹ • (i.1 + 1 : ℝ) •
          (jet ⟨i.1 + 1, by omega⟩).1
            (Function.update (fun _ : Fin (i.1 + 1) ↦ y - x) (Fin.last i.1) h) = _
      rw [harg, smul_smul]
      congr 1
      rw [Nat.factorial_succ]
      push_cast
      field_simp

theorem shiftedSymmetricJetDerivative_eq_taylorModelDerivative
    (q : ℕ) (F : E → E) (x : E) (jet : SymmetricExactJet E (q + 1))
    (hexact : ∀ j : Fin (q + 1), (jet j).1 = iteratedFDeriv ℝ j.1 F x)
    (y : E) : shiftedSymmetricJetDerivative q x jet y =
      taylorModelDerivative (q + 1) F x y := by
  classical
  ext h
  rw [shiftedSymmetricJetDerivative, taylorModelDerivative, taylorModel,
    ContinuousLinearMap.sum_apply]
  simp only [Nat.add_sub_cancel, ContinuousLinearMap.sum_apply]
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro n hn
  simp only [ContinuousLinearMap.smul_apply]
  rw [hexact ⟨n + 1, by omega⟩, ContinuousMultilinearMap.curryRight_apply,
    iteratedFDeriv_succ_apply_right]
  simp

theorem fderiv_taylorModel_eq_taylorModelDerivative_of_exactSymmetricJet
    (q : ℕ) (F : E → E) (x : E) (jet : SymmetricExactJet E (q + 1))
    (hexact : ∀ j : Fin (q + 1), (jet j).1 = iteratedFDeriv ℝ j.1 F x)
    (y : E) : fderiv ℝ (taylorModel (q + 1) F x) y =
      taylorModelDerivative (q + 1) F x y := by
  rw [fderiv_taylorModel_eq_symmetricJetTaylorDerivative (q + 1) F x jet hexact y,
    symmetricJetTaylorDerivative_eq_shifted,
    shiftedSymmetricJetDerivative_eq_taylorModelDerivative q F x jet hexact y]

theorem fderiv_taylorModel_eq_taylorModelDerivative_of_exactSymmetricJet'
    (p : ℕ) (hp : 1 ≤ p) (F : E → E) (x : E) (jet : SymmetricExactJet E p)
    (hexact : ∀ j : Fin p, (jet j).1 = iteratedFDeriv ℝ j.1 F x)
    (y : E) : fderiv ℝ (taylorModel p F x) y =
      taylorModelDerivative p F x y := by
  obtain ⟨q, rfl⟩ : ∃ q : ℕ, p = q + 1 := ⟨p - 1, by omega⟩
  exact fderiv_taylorModel_eq_taylorModelDerivative_of_exactSymmetricJet
    q F x jet hexact y

end
end LeanArticleAudit.Pilot
