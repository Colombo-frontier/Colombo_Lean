import Bilevel.ChiExtensionSum

/-! The complete finite extension formula, including the unbounded public
radial terms. Global second/third derivative bounds are summed only after
each term has been embedded into the common Euclidean product. -/
noncomputable section
open scoped RealInnerProductSpace
namespace Bilevel.ChiExtension
open PrimitiveGeometry
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

set_option maxHeartbeats 1200000 in
theorem radialTerm_normal_gradient (m : ℕ) (i : Fin m) (L : E →L[ℝ] F) (hL : ‖L‖≤1)
    (ν R d : ℝ) (hR : 0<R) (p : E) :
    HasGradientAt (fun q : Normals m => radialTerm m i L hL ν R d (pack p q))
      (EuclideanSpace.single i ((ν*R^2/d)*(Real.sqrt (1+‖L p‖^2/R^2)-1))) 0 := by
  have hp := ((PublicRadialExtension.potential_contDiff (ν*R/d) R
    (PublicRadialExtension.normalDirection : Joint F ℝ) 3).differentiable (by norm_num)
      (pack (L p) (0:ℝ))).hasGradientAt
  change HasGradientAt (PublicRadialExtension.radial ν R d)
    (gradient (PublicRadialExtension.radial ν R d) (pack (L p) 0)) (pack (L p) 0) at hp
  rw [PublicRadialExtension.radial_normal_trace_gradient ν R d hR] at hp
  have hd := (PrimitiveGeometry.partial_y hp).hasDerivAt
  let ev : Normals m →L[ℝ] ℝ := EuclideanSpace.proj i
  have hproj : HasFDerivAt ev ev (0:Normals m) := ev.hasFDerivAt
  have hd' : HasDerivAt (fun t : ℝ => PublicRadialExtension.radial ν R d (pack (L p) t))
      ((ν*R^2/d)*(Real.sqrt (1+‖L p‖^2/R^2)-1)) (ev 0) := by
    simpa only [map_zero,conj_trivial] using hd
  have hcomp := hd'.comp_hasFDerivAt 0 hproj
  apply hasGradientAt_iff_hasFDerivAt.mpr
  convert hcomp using 1
  ext q
  simp [ev,InnerProductSpace.toDual_apply,EuclideanSpace.inner_single_left,mul_comm]

def radialSum {n m : ℕ} (index : Fin n → Fin m) (L : Fin n → E →L[ℝ] F)
    (hL : ∀ j,‖L j‖≤1) (ν R : Fin n → ℝ) (d : ℝ) (z : Full E m) : ℝ :=
  ∑ j : Fin n,radialTerm m (index j) (L j) (hL j) (ν j) (R j) d z

omit [CompleteSpace F] in
theorem radialSum_contDiff {n m : ℕ} (index : Fin n → Fin m) (L : Fin n → E →L[ℝ] F)
    (hL : ∀ j,‖L j‖≤1) (ν R : Fin n → ℝ) (d : ℝ) : ContDiff ℝ 3 (radialSum index L hL ν R d) :=
  ContDiff.sum (fun j _ => radialTerm_contDiff m (index j) (L j) (hL j) (ν j) (R j) d)

omit [CompleteSpace F] in
theorem radialSum_zero_trace {n m : ℕ} (index : Fin n → Fin m) (L : Fin n → E →L[ℝ] F)
    (hL : ∀ j,‖L j‖≤1) (ν R : Fin n → ℝ) (d : ℝ) (p : E) :
    radialSum index L hL ν R d (pack p 0)=0 :=
  Finset.sum_eq_zero (fun j _ => radialTerm_zero_trace m (index j) (L j) (hL j) (ν j) (R j) d p)

theorem radialSum_jets {n m : ℕ} (index : Fin n → Fin m) (L : Fin n → E →L[ℝ] F)
    (hL : ∀ j,‖L j‖≤1) (ν R : Fin n → ℝ) (d : ℝ)
    (hν : ∀ j,0≤ν j) (hR : ∀ j,0<R j) (hd : 0<d) (z : Full E m) :
    ‖iteratedFDeriv ℝ 2 (radialSum index L hL ν R d) z‖≤∑ j : Fin n,3*(ν j*R j/d) ∧
    ‖iteratedFDeriv ℝ 3 (radialSum index L hL ν R d) z‖≤∑ j : Fin n,9*ν j/d := by
  have sumBound (k : ℕ) (hk : k≤3) (B : Fin n → ℝ)
      (hb : ∀ j,‖iteratedFDeriv ℝ k (radialTerm m (index j) (L j) (hL j) (ν j) (R j) d) z‖≤B j) :
      ‖iteratedFDeriv ℝ k (radialSum index L hL ν R d) z‖≤∑ j : Fin n,B j := by
    unfold radialSum
    rw [iteratedFDeriv_sum (fun j _ => (radialTerm_contDiff m (index j) (L j) (hL j) (ν j) (R j) d).of_le
      (show (k:WithTop ℕ∞)≤3 by exact_mod_cast hk))]
    simp only [Finset.sum_apply]
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun j _ => hb j))
  have hj (j : Fin n) := radialTerm_jets m (index j) (L j) (hL j) (ν j) (R j) d (hν j) (hR j) hd z
  exact ⟨sumBound 2 (by norm_num) _ (fun j => (hj j).1),sumBound 3 (by norm_num) _ (fun j => (hj j).2)⟩

end Bilevel.ChiExtension
