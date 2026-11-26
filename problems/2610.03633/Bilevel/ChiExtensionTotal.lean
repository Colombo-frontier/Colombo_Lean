import Bilevel.ChiExtensionRadialSum

/-! Actual hidden-plus-public extension with exact normal trace and global
mixed-jet assembly. Numerical source calibration is deliberately separate. -/
noncomputable section
namespace Bilevel.ChiExtension
open PrimitiveGeometry
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

theorem radialSum_normal_gradient {n m : ℕ} (index : Fin n → Fin m) (L : Fin n → E →L[ℝ] F)
    (hL : ∀ j,‖L j‖≤1) (ν R : Fin n → ℝ) (d : ℝ) (hR : ∀ j,0<R j) (p : E) :
    HasGradientAt (fun q : Normals m => radialSum index L hL ν R d (pack p q))
      (∑ j : Fin n,EuclideanSpace.single (index j)
        ((ν j*(R j)^2/d)*(Real.sqrt (1+‖L j p‖^2/(R j)^2)-1))) 0 := by
  have hs := HasFDerivAt.sum (u:=Finset.univ) (fun j _ =>
    (radialTerm_normal_gradient m (index j) (L j) (hL j) (ν j) (R j) d (hR j) p).hasFDerivAt)
  apply hasGradientAt_iff_hasFDerivAt.mpr
  convert hs using 1
  exact map_sum _ _ _

def total {n a m : ℕ} (index : Fin n → Fin m) (f : Fin n → E → ℝ) (W : Fin n → ℝ)
    (i : Fin m) (D : CompensatedMean.Data (E:=E)) (lambdaExt : ℝ)
    (radialIndex : Fin a → Fin m) (L : Fin a → E →L[ℝ] F) (hL : ∀ j,‖L j‖≤1)
    (ν R : Fin a → ℝ) (d : ℝ) (z : Full E m) : ℝ :=
  hidden index f W i D lambdaExt z+radialSum radialIndex L hL ν R d z

omit [CompleteSpace F] in
theorem total_contDiff {n a m : ℕ} (index : Fin n → Fin m) (f : Fin n → E → ℝ) (W : Fin n → ℝ)
    (hf : ∀ j,ContDiff ℝ 3 (f j)) (hW : ∀ j,0<W j)
    (i : Fin m) (D : CompensatedMean.Data (E:=E)) (lambdaExt : ℝ)
    (radialIndex : Fin a → Fin m) (L : Fin a → E →L[ℝ] F) (hL : ∀ j,‖L j‖≤1)
    (ν R : Fin a → ℝ) (d : ℝ) :
    ContDiff ℝ 3 (total index f W i D lambdaExt radialIndex L hL ν R d) :=
  (hidden_contDiff index f W hf hW i D lambdaExt).add (radialSum_contDiff radialIndex L hL ν R d)

omit [CompleteSpace F] in
theorem total_zero_trace {n a m : ℕ} (index : Fin n → Fin m) (f : Fin n → E → ℝ) (W : Fin n → ℝ)
    (hW : ∀ j,0<W j) (i : Fin m) (D : CompensatedMean.Data (E:=E)) (lambdaExt : ℝ)
    (radialIndex : Fin a → Fin m) (L : Fin a → E →L[ℝ] F) (hL : ∀ j,‖L j‖≤1)
    (ν R : Fin a → ℝ) (d : ℝ) (p : E) :
    total index f W i D lambdaExt radialIndex L hL ν R d (pack p 0)=0 := by
  rw [total,hidden_zero_trace index f W hW,radialSum_zero_trace,add_zero]

theorem total_normal_gradient {n a m : ℕ} (index : Fin n → Fin m) (f : Fin n → E → ℝ) (W : Fin n → ℝ)
    (hW : ∀ j,0<W j) (i : Fin m) (D : CompensatedMean.Data (E:=E)) (lambdaExt : ℝ)
    (radialIndex : Fin a → Fin m) (L : Fin a → E →L[ℝ] F) (hL : ∀ j,‖L j‖≤1)
    (ν R : Fin a → ℝ) (d : ℝ) (hR : ∀ j,0<R j) (p : E) :
    HasGradientAt (fun q : Normals m => total index f W i D lambdaExt radialIndex L hL ν R d (pack p q))
      (lambdaExt • ((∑ j : Fin n,EuclideanSpace.single (index j) (f j p))+EuclideanSpace.single i (D.r p))+
        ∑ j : Fin a,EuclideanSpace.single (radialIndex j)
          ((ν j*(R j)^2/d)*(Real.sqrt (1+‖L j p‖^2/(R j)^2)-1))) 0 := by
  have hh := (hidden_normal_gradient index f W hW i D lambdaExt p).hasFDerivAt.add
    (radialSum_normal_gradient radialIndex L hL ν R d hR p).hasFDerivAt
  apply hasGradientAt_iff_hasFDerivAt.mpr
  simpa only [map_add] using hh

omit [CompleteSpace F] in
theorem total_jet_bound {n a m : ℕ} (index : Fin n → Fin m) (f : Fin n → E → ℝ) (W : Fin n → ℝ)
    (hf : ∀ j,ContDiff ℝ 3 (f j)) (hW : ∀ j,0<W j)
    (i : Fin m) (D : CompensatedMean.Data (E:=E)) (lambdaExt : ℝ)
    (radialIndex : Fin a → Fin m) (L : Fin a → E →L[ℝ] F) (hL : ∀ j,‖L j‖≤1)
    (ν R : Fin a → ℝ) (d : ℝ) (z : Full E m) (k : ℕ) (hk : k≤3)
    (Bhidden Bradial : ℝ)
    (hh : ‖iteratedFDeriv ℝ k (hidden index f W i D lambdaExt) z‖≤Bhidden)
    (hr : ‖iteratedFDeriv ℝ k (radialSum radialIndex L hL ν R d) z‖≤Bradial) :
    ‖iteratedFDeriv ℝ k (total index f W i D lambdaExt radialIndex L hL ν R d) z‖≤Bhidden+Bradial := by
  have hk' : (k:WithTop ℕ∞)≤3 := by exact_mod_cast hk
  unfold total
  rw [iteratedFDeriv_add_apply' (((hidden_contDiff index f W hf hW i D lambdaExt).of_le hk').contDiffAt)
    (((radialSum_contDiff radialIndex L hL ν R d).of_le hk').contDiffAt)]
  exact (norm_add_le _ _).trans (add_le_add hh hr)

end Bilevel.ChiExtension
