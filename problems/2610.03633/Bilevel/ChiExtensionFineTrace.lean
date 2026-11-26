import Bilevel.ChiExtensionTerms

/-! Exact normal trace and full-space jet contraction for the actual finite
fine coupling. Its decomposition is retained before normal-coordinate
embedding; all summands use the same deepest normal coordinate. -/
noncomputable section
open scoped RealInnerProductSpace
namespace Bilevel.ChiExtension
open PrimitiveGeometry
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def fineTerm (m : ℕ) (i : Fin m) (D : CompensatedMean.Data (E:=E)) : Full E m → ℝ :=
  D.coupling ∘ normalSlice m i

theorem fineTerm_sum (m : ℕ) (i : Fin m) (D : CompensatedMean.Data (E:=E)) (z : Full E m) :
    fineTerm m i D z=∑ j ∈ Finset.range (D.J+1),normalTerm m i (D.e j) (D.w j) z := rfl

theorem fineTerm_contDiff (m : ℕ) (i : Fin m) (D : CompensatedMean.Data (E:=E)) :
    ContDiff ℝ 3 (fineTerm m i D) := D.coupling_contDiff.comp (normalSlice (E:=E) m i).contDiff

theorem fineTerm_zero_trace (m : ℕ) (i : Fin m) (D : CompensatedMean.Data (E:=E)) (p : E) :
    fineTerm m i D (pack p 0)=0 := by
  rw [fineTerm_sum]
  apply Finset.sum_eq_zero
  intro j hj
  exact normalTerm_zero_trace m i (D.e j) (D.w_pos j (by have := Finset.mem_range.mp hj;omega)) p

set_option maxHeartbeats 1200000 in
theorem fineTerm_normal_gradient (m : ℕ) (i : Fin m) (D : CompensatedMean.Data (E:=E)) (p : E) :
    HasGradientAt (fun q : Normals m => fineTerm m i D (pack p q))
      (EuclideanSpace.single i (D.r p)) 0 := by
  have hs := HasFDerivAt.sum (u:=Finset.range (D.J+1)) (fun j hj =>
    (normalTerm_normal_gradient m i (D.e j) (D.w_pos j (by have := Finset.mem_range.mp hj;omega)) p).hasFDerivAt)
  apply hasGradientAt_iff_hasFDerivAt.mpr
  convert hs using 1
  ext q
  simp only [ContinuousLinearMap.sum_apply,InnerProductSpace.toDual_apply,
    EuclideanSpace.inner_single_left,map_sum,conj_trivial]
  rw [← Finset.sum_mul,D.decomposition]

theorem fineTerm_jet_contraction (m : ℕ) (i : Fin m) (D : CompensatedMean.Data (E:=E))
    (z : Full E m) (k : ℕ) (hk : k≤3) :
    ‖iteratedFDeriv ℝ k (fineTerm m i D) z‖≤‖iteratedFDeriv ℝ k D.coupling (normalSlice m i z)‖ :=
  contraction_jet D.coupling_contDiff (normalSlice m i) (normalSlice_norm_le m i) z k hk

end Bilevel.ChiExtension
