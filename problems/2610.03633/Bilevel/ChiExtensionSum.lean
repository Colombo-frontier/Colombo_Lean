import Bilevel.ChiExtensionFineTrace

/-! The hidden extension is the actual finite sum of coarse terms and the
deepest fine coupling on a common Euclidean space. These assembly lemmas
keep every term's budget explicit for the source calibration. -/
noncomputable section
namespace Bilevel.ChiExtension
open PrimitiveGeometry
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def coarseSum {n m : ℕ} (index : Fin n → Fin m) (f : Fin n → E → ℝ) (W : Fin n → ℝ)
    (z : Full E m) : ℝ := ∑ j : Fin n,normalTerm m (index j) (f j) (W j) z

def hidden {n m : ℕ} (index : Fin n → Fin m) (f : Fin n → E → ℝ) (W : Fin n → ℝ)
    (i : Fin m) (D : CompensatedMean.Data (E:=E)) (lambdaExt : ℝ) (z : Full E m) : ℝ :=
  lambdaExt*(coarseSum index f W z+fineTerm m i D z)

theorem coarseSum_contDiff {n m : ℕ} (index : Fin n → Fin m) (f : Fin n → E → ℝ) (W : Fin n → ℝ)
    (hf : ∀ j,ContDiff ℝ 3 (f j)) (hW : ∀ j,0<W j) : ContDiff ℝ 3 (coarseSum index f W) :=
  ContDiff.sum (fun j _ => normalTerm_contDiff m (index j) (hf j) (hW j))

theorem hidden_contDiff {n m : ℕ} (index : Fin n → Fin m) (f : Fin n → E → ℝ) (W : Fin n → ℝ)
    (hf : ∀ j,ContDiff ℝ 3 (f j)) (hW : ∀ j,0<W j)
    (i : Fin m) (D : CompensatedMean.Data (E:=E)) (lambdaExt : ℝ) :
    ContDiff ℝ 3 (hidden index f W i D lambdaExt) :=
  contDiff_const.mul ((coarseSum_contDiff index f W hf hW).add (fineTerm_contDiff m i D))

theorem hidden_zero_trace {n m : ℕ} (index : Fin n → Fin m) (f : Fin n → E → ℝ) (W : Fin n → ℝ)
    (hW : ∀ j,0<W j) (i : Fin m) (D : CompensatedMean.Data (E:=E)) (lambdaExt : ℝ) (p : E) :
    hidden index f W i D lambdaExt (pack p 0)=0 := by
  have hc : coarseSum index f W (pack p 0)=0 :=
    Finset.sum_eq_zero (fun j _ => normalTerm_zero_trace m (index j) (f j) (hW j) p)
  simp only [hidden,hc,fineTerm_zero_trace,add_zero,mul_zero]

set_option maxHeartbeats 1200000 in
theorem hidden_normal_gradient {n m : ℕ} (index : Fin n → Fin m) (f : Fin n → E → ℝ) (W : Fin n → ℝ)
    (hW : ∀ j,0<W j) (i : Fin m) (D : CompensatedMean.Data (E:=E)) (lambdaExt : ℝ) (p : E) :
    HasGradientAt (fun q : Normals m => hidden index f W i D lambdaExt (pack p q))
      (lambdaExt • ((∑ j : Fin n,EuclideanSpace.single (index j) (f j p))+
        EuclideanSpace.single i (D.r p))) 0 := by
  have hs := HasFDerivAt.sum (u:=Finset.univ) (fun j _ =>
    (normalTerm_normal_gradient m (index j) (f j) (hW j) p).hasFDerivAt)
  have ht := (hs.add (fineTerm_normal_gradient m i D p).hasFDerivAt).const_mul lambdaExt
  apply hasGradientAt_iff_hasFDerivAt.mpr
  convert ht using 1
  ext q
  simp [InnerProductSpace.toDual_apply,inner_add_left,real_inner_smul_left,
    inner_sum,ContinuousLinearMap.sum_apply,EuclideanSpace.inner_single_left,mul_comm]

theorem coarseSum_jet_bound {n m : ℕ} (index : Fin n → Fin m) (f : Fin n → E → ℝ) (W : Fin n → ℝ)
    (hf : ∀ j,ContDiff ℝ 3 (f j)) (hW : ∀ j,0<W j) (z : Full E m) (k : ℕ) (hk : k≤3)
    (B : Fin n → ℝ) (hb : ∀ j,‖iteratedFDeriv ℝ k (normalTerm m (index j) (f j) (W j)) z‖≤B j) :
    ‖iteratedFDeriv ℝ k (coarseSum index f W) z‖≤∑ j : Fin n,B j := by
  unfold coarseSum
  rw [iteratedFDeriv_sum (fun j _ => (normalTerm_contDiff m (index j) (hf j) (hW j)).of_le
    (show (k:WithTop ℕ∞)≤3 by exact_mod_cast hk))]
  simp only [Finset.sum_apply]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun j _ => hb j))

theorem hidden_jet_bound {n m : ℕ} (index : Fin n → Fin m) (f : Fin n → E → ℝ) (W : Fin n → ℝ)
    (hf : ∀ j,ContDiff ℝ 3 (f j)) (hW : ∀ j,0<W j) (i : Fin m) (D : CompensatedMean.Data (E:=E))
    (lambdaExt : ℝ) (hlambdaExt : 0≤lambdaExt) (z : Full E m) (k : ℕ) (hk : k≤3)
    (B : Fin n → ℝ) (Bfine : ℝ)
    (hb : ∀ j,‖iteratedFDeriv ℝ k (normalTerm m (index j) (f j) (W j)) z‖≤B j)
    (hbf : ‖iteratedFDeriv ℝ k D.coupling (normalSlice m i z)‖≤Bfine) :
    ‖iteratedFDeriv ℝ k (hidden index f W i D lambdaExt) z‖≤lambdaExt*((∑ j : Fin n,B j)+Bfine) := by
  have hcs := coarseSum_contDiff index f W hf hW
  have hfs := fineTerm_contDiff m i D
  have hk' : (k:WithTop ℕ∞)≤3 := by exact_mod_cast hk
  change ‖iteratedFDeriv ℝ k (fun w => lambdaExt • (coarseSum index f W w+fineTerm m i D w)) z‖≤_
  rw [iteratedFDeriv_const_smul_apply' (((hcs.add hfs).of_le hk').contDiffAt),
    norm_smul,Real.norm_eq_abs,abs_of_nonneg hlambdaExt,
    iteratedFDeriv_add_apply' ((hcs.of_le hk').contDiffAt) ((hfs.of_le hk').contDiffAt)]
  apply mul_le_mul_of_nonneg_left _ hlambdaExt
  exact (norm_add_le _ _).trans (add_le_add (coarseSum_jet_bound index f W hf hW z k hk B hb)
    ((fineTerm_jet_contraction m i D z k hk).trans hbf))

end Bilevel.ChiExtension
