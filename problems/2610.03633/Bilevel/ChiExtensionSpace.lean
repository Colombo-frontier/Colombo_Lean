import Bilevel.ChiCoarseExtension
import Bilevel.PublicRadialCertificate

/-! Euclidean realization of all dual normal coordinates. Each individual
normal extension is pulled back by an actual contraction, so its mixed-jet
budget remains valid in the full space. -/
noncomputable section
namespace Bilevel.ChiExtension
open PrimitiveGeometry

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

abbrev Normals (m : ℕ) := EuclideanSpace ℝ (Fin m)
abbrev Full (E : Type*) (m : ℕ) := Joint E (Normals m)

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] in
theorem normal_coordinate_bound {m : ℕ} (z : Full E m) (i : Fin m) :
    |z.snd i| ≤ ‖z.snd‖ := by
  simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le z.snd i

def normalSliceLinear (m : ℕ) (i : Fin m) : Full E m →ₗ[ℝ] CompensatedMean.LowerSpace E where
  toFun z := CompensatedMean.pack E z.fst (z.snd i) 0
  map_add' z w := by
    simpa only [PiLp.add_apply,add_zero] using CompensatedMean.pack_add z.fst w.fst (z.snd i) (w.snd i) 0 0
  map_smul' c z := by
    simpa only [PiLp.smul_apply,smul_eq_mul,mul_zero] using CompensatedMean.pack_smul c z.fst (z.snd i) 0

theorem normalSliceLinear_norm_le (m : ℕ) (i : Fin m) (z : Full E m) :
    ‖normalSliceLinear m i z‖ ≤ ‖z‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  change ‖CompensatedMean.pack E z.fst (z.snd i) 0‖^2 ≤ ‖z‖^2
  rw [CompensatedMean.pack_norm_sq,PrimitiveGeometry.norm_sq]
  have hh := normal_coordinate_bound z i
  have hs := pow_le_pow_left₀ (abs_nonneg _) hh 2
  nlinarith [sq_abs (z.snd i)]

def normalSlice (m : ℕ) (i : Fin m) : Full E m →L[ℝ] CompensatedMean.LowerSpace E :=
  (normalSliceLinear m i).mkContinuous 1 (by intro z;simpa only [one_mul] using normalSliceLinear_norm_le m i z)

@[simp] theorem normalSlice_pack (m : ℕ) (i : Fin m) (p : E) (q : Normals m) :
    normalSlice m i (pack p q)=CompensatedMean.pack E p (q i) 0 := rfl

theorem normalSlice_norm_le (m : ℕ) (i : Fin m) : ‖normalSlice (E:=E) m i‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro z
  simpa only [one_mul] using normalSliceLinear_norm_le m i z

def radialSliceLinear (m : ℕ) (i : Fin m) (L : E →L[ℝ] F) : Full E m →ₗ[ℝ] Joint F ℝ where
  toFun z := pack (L z.fst) (z.snd i)
  map_add' z w := by
    change pack (L (z.fst+w.fst)) (z.snd i+w.snd i)=pack (L z.fst+L w.fst) (z.snd i+w.snd i)
    rw [map_add]
  map_smul' c z := by
    change pack (L (c • z.fst)) (c • z.snd i)=pack (c • L z.fst) (c • z.snd i)
    rw [map_smul]

theorem radialSliceLinear_norm_le (m : ℕ) (i : Fin m) (L : E →L[ℝ] F)
    (hL : ‖L‖ ≤ 1) (z : Full E m) : ‖radialSliceLinear m i L z‖ ≤ ‖z‖ := by
  have hLp : ‖L z.fst‖ ≤ ‖z.fst‖ := (L.le_opNorm _).trans
    ((mul_le_mul_of_nonneg_right hL (norm_nonneg _)).trans_eq (one_mul _))
  have hq := normal_coordinate_bound z i
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  change ‖pack (L z.fst) (z.snd i)‖^2 ≤ ‖z‖^2
  rw [PrimitiveGeometry.norm_sq,PrimitiveGeometry.norm_sq]
  change ‖L z.fst‖^2+‖z.snd i‖^2 ≤ ‖z.fst‖^2+‖z.snd‖^2
  rw [Real.norm_eq_abs]
  exact add_le_add (pow_le_pow_left₀ (norm_nonneg _) hLp 2) (pow_le_pow_left₀ (abs_nonneg _) hq 2)

def radialSlice (m : ℕ) (i : Fin m) (L : E →L[ℝ] F) (hL : ‖L‖ ≤ 1) : Full E m →L[ℝ] Joint F ℝ :=
  (radialSliceLinear m i L).mkContinuous 1 (by intro z;simpa only [one_mul] using radialSliceLinear_norm_le m i L hL z)

@[simp] theorem radialSlice_pack (m : ℕ) (i : Fin m) (L : E →L[ℝ] F) (hL : ‖L‖ ≤ 1)
    (p : E) (q : Normals m) : radialSlice m i L hL (pack p q)=pack (L p) (q i) := rfl

theorem radialSlice_norm_le (m : ℕ) (i : Fin m) (L : E →L[ℝ] F) (hL : ‖L‖ ≤ 1) :
    ‖radialSlice m i L hL‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro z
  simpa only [one_mul] using radialSliceLinear_norm_le m i L hL z

theorem contraction_jet {f : F → ℝ} (hf : ContDiff ℝ 3 f) (L : E →L[ℝ] F)
    (hL : ‖L‖ ≤ 1) (x : E) (k : ℕ) (hk : k ≤ 3) :
    ‖iteratedFDeriv ℝ k (f ∘ L) x‖ ≤ ‖iteratedFDeriv ℝ k f (L x)‖ := by
  rw [L.iteratedFDeriv_comp_right hf x (by exact_mod_cast hk)]
  apply (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans
  simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left
    (pow_le_one₀ (norm_nonneg L) hL) (norm_nonneg _)

end Bilevel.ChiExtension
