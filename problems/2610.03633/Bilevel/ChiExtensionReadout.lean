import Bilevel.ChiExtensionTotal

/-! Exact scalar readout of all actual normal derivatives. Repeated normal
indices are permitted; the source uses distinct coarse/public coordinates. -/
noncomputable section
open scoped BigOperators
namespace Bilevel.ChiExtension
open PrimitiveGeometry RadialWrapper

def normalReadout (m : ℕ) : Normals m →L[ℝ] ℝ := ∑ i : Fin m,EuclideanSpace.proj (𝕜:=ℝ) i

theorem normalReadout_apply (m : ℕ) (q : Normals m) : normalReadout m q=∑ i : Fin m,q i := by
  simp [normalReadout,ContinuousLinearMap.sum_apply]

theorem normalReadout_single {m : ℕ} (i : Fin m) (a : ℝ) : normalReadout m (EuclideanSpace.single i a)=a := by
  classical
  rw [normalReadout_apply]
  simp [EuclideanSpace.single_apply]

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

theorem total_normal_readout {n a m : ℕ} (index : Fin n → Fin m) (f : Fin n → E → ℝ) (W : Fin n → ℝ)
    (hW : ∀ j,0<W j) (i : Fin m) (D : CompensatedMean.Data (E:=E))
    (radialIndex : Fin a → Fin m) (L : Fin a → E →L[ℝ] F) (hL : ∀ j,‖L j‖≤1)
    (ν R : Fin a → ℝ) (d : ℝ) (hd : d≠0) (hR : ∀ j,0<R j) (p : E) :
    d*normalReadout m (gradient (fun q : Normals m =>
      total index f W i D (1/d) radialIndex L hL ν R d (pack p q)) 0)=
      (∑ j : Fin n,f j p)+D.r p+∑ j : Fin a,bowl (ν j) (R j) (L j p) := by
  rw [(total_normal_gradient index f W hW i D (1/d) radialIndex L hL ν R d hR p).gradient]
  simp only [map_add,map_smul,map_sum,normalReadout_single,smul_eq_mul]
  rw [mul_add,Finset.mul_sum]
  have hh : d*((1/d)*((∑ j : Fin n,f j p)+D.r p))=(∑ j : Fin n,f j p)+D.r p := by field_simp
  rw [hh]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  unfold bowl
  field_simp

end Bilevel.ChiExtension
