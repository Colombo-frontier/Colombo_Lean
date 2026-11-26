import Bilevel.ChiExtensionSum

/-! Exact coefficient normalization and finite coarse-sum jet bounds on
the common Euclidean space of all normal coordinates. -/
noncomputable section
open scoped BigOperators
namespace Bilevel.ChiExtensionCalibration
open ChiExtension PrimitiveGeometry
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem normalized_jet_norm {f : E → ℝ} (hf : ContDiff ℝ 3 f)
    {d : ℝ} (hd : 0 < d) (k : ℕ) (hk : k ≤ 3) (z : E) :
    ‖iteratedFDeriv ℝ k (fun x => f x/d) z‖ = ‖iteratedFDeriv ℝ k f z‖/d := by
  have he : (fun x => f x/d) = fun x => d⁻¹ • f x := by funext x; simp [div_eq_inv_mul]
  rw [he,iteratedFDeriv_const_smul_apply' ((hf.of_le (show (k:WithTop ℕ∞) ≤ 3 by exact_mod_cast hk)).contDiffAt),
    norm_smul d⁻¹ (iteratedFDeriv ℝ k f z),Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hd)]
  ring

theorem coarseSum_normalized_jets {n m : ℕ} (index : Fin n → Fin m)
    (f : Fin n → E → ℝ) (N ell h : Fin n → ℝ) (M d : ℝ)
    (hf : ∀ j,ContDiff ℝ 3 (f j)) (hN : ∀ j,1 ≤ N j) (hell : ∀ j,0 ≤ ell j)
    (hh : ∀ j,0 < h j) (hM : 0 ≤ M) (hd : 0 < d)
    (hb : ∀ j z,|f j z| ≤ M*N j*ell j*(h j)^2 ∧
      ‖iteratedFDeriv ℝ 1 (f j) z‖ ≤ M*ell j*h j*Real.sqrt (N j) ∧
      ‖iteratedFDeriv ℝ 2 (f j) z‖ ≤ M*ell j ∧
      ‖iteratedFDeriv ℝ 3 (f j) z‖ ≤ M*ell j/h j)
    (z : Full E m) :
    let W := fun j => h j*(N j)^(1/3:ℝ)
    let H := fun x => coarseSum index f W x/d
    ‖iteratedFDeriv ℝ 1 H z‖ ≤ ∑ j : Fin n,2*SmallGapLiftSupport.C*M*N j*ell j*(h j)^2/d ∧
    ‖iteratedFDeriv ℝ 2 H z‖ ≤ ∑ j : Fin n,4*SmallGapLiftSupport.C*M*ell j*h j*((N j)^(1/3:ℝ))^2/d ∧
    ‖iteratedFDeriv ℝ 3 H z‖ ≤ ∑ j : Fin n,8*SmallGapLiftSupport.C*M*ell j*(N j)^(1/3:ℝ)/d := by
  dsimp only
  have hW (j : Fin n) : 0 < h j*(N j)^(1/3:ℝ) :=
    mul_pos (hh j) (Real.rpow_pos_of_pos (by linarith [hN j]) _)
  have hf' := coarseSum_contDiff index f _ hf hW
  have hj (j : Fin n) := normalTerm_coarse_jets m (index j) (hf j) (hN j) (hell j) (hh j) hM (hb j) z
  have sumBound (k : ℕ) (hk : k ≤ 3) (B : Fin n → ℝ)
      (hB : ∀ j,‖iteratedFDeriv ℝ k (normalTerm m (index j) (f j) (h j*(N j)^(1/3:ℝ))) z‖ ≤ B j) :
      ‖iteratedFDeriv ℝ k (fun x => coarseSum index f (fun j => h j*(N j)^(1/3:ℝ)) x/d) z‖ ≤
        ∑ j : Fin n,B j/d := by
    rw [normalized_jet_norm hf' hd k hk]
    have hs := div_le_div_of_nonneg_right (coarseSum_jet_bound index f _ hf hW z k hk B hB) hd.le
    simpa only [Finset.sum_div] using hs
  exact ⟨sumBound 1 (by norm_num) _ (fun j => (hj j).1),
    sumBound 2 (by norm_num) _ (fun j => (hj j).2.1),
    sumBound 3 (by norm_num) _ (fun j => (hj j).2.2)⟩

theorem fineTerm_normalized_jet {m : ℕ} (i : Fin m) (D : CompensatedMean.Data (E:=E))
    {d : ℝ} (hd : 0 < d) (z : Full E m) (k : ℕ) (hk : k ≤ 3) {B : ℝ}
    (hb : ‖iteratedFDeriv ℝ k D.coupling (normalSlice m i z)‖ ≤ B) :
    ‖iteratedFDeriv ℝ k (fun x => fineTerm m i D x/d) z‖ ≤ B/d := by
  rw [normalized_jet_norm (fineTerm_contDiff m i D) hd k hk]
  exact div_le_div_of_nonneg_right ((fineTerm_jet_contraction m i D z k hk).trans hb) hd.le

end Bilevel.ChiExtensionCalibration
