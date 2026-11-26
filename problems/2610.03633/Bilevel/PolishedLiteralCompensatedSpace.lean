import Bilevel.Model
import Mathlib.Analysis.InnerProductSpace.ProdL2

/-! The lower space of the mean lift, including the source's dummy scalar
block. All norms below are Euclidean product norms. -/

noncomputable section
namespace Bilevel.PolishedLiteralCompensated
open scoped RealInnerProductSpace

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]

abbrev LowerSpace := WithLp 2 (E × EuclideanSpace ℝ (Fin 2))

def uProj : LowerSpace E →L[ℝ] E :=
  (ContinuousLinearMap.fst ℝ E (EuclideanSpace ℝ (Fin 2))).comp
    (WithLp.prodContinuousLinearEquiv 2 ℝ E (EuclideanSpace ℝ (Fin 2))).toContinuousLinearMap

def scalarProj : LowerSpace E →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  (ContinuousLinearMap.snd ℝ E (EuclideanSpace ℝ (Fin 2))).comp
    (WithLp.prodContinuousLinearEquiv 2 ℝ E (EuclideanSpace ℝ (Fin 2))).toContinuousLinearMap

def sProj : LowerSpace E →L[ℝ] ℝ := (EuclideanSpace.proj 0).comp (scalarProj E)
def zProj : LowerSpace E →L[ℝ] ℝ := (EuclideanSpace.proj 1).comp (scalarProj E)

def pack (u : E) (s z : ℝ) : LowerSpace E :=
  (WithLp.equiv 2 (E × EuclideanSpace ℝ (Fin 2))).symm
    (u, s • EuclideanSpace.single 0 1 + z • EuclideanSpace.single 1 1)

variable {E}

@[simp] theorem uProj_pack (u : E) (s z : ℝ) : uProj E (pack E u s z) = u := rfl
@[simp] theorem sProj_pack (u : E) (s z : ℝ) : sProj E (pack E u s z) = s := by
  simp [sProj, scalarProj, pack, EuclideanSpace.single_apply]
@[simp] theorem zProj_pack (u : E) (s z : ℝ) : zProj E (pack E u s z) = z := by
  simp [zProj, scalarProj, pack, EuclideanSpace.single_apply]

theorem lower_inner (v w : LowerSpace E) :
    ⟪v,w⟫ = ⟪uProj E v,uProj E w⟫ + sProj E v*sProj E w + zProj E v*zProj E w := by
  rw [WithLp.prod_inner_apply, PiLp.inner_apply]
  simp only [Fin.sum_univ_succ, Fin.val_zero, Fin.val_succ, Fin.sum_univ_zero, add_zero,
    RCLike.inner_apply, conj_trivial]
  change ⟪uProj E v,uProj E w⟫ + (sProj E w*sProj E v+zProj E w*zProj E v) = _
  ring

theorem inner_pack (u : E) (s z : ℝ) (w : LowerSpace E) :
    ⟪pack E u s z,w⟫ = ⟪u,uProj E w⟫+s*sProj E w+z*zProj E w := by
  rw [lower_inner,uProj_pack,sProj_pack,zProj_pack]

theorem lower_norm_sq (y : LowerSpace E) :
    ‖y‖^2 = ‖uProj E y‖^2+(sProj E y)^2+(zProj E y)^2 := by
  rw [← real_inner_self_eq_norm_sq, lower_inner, real_inner_self_eq_norm_sq]
  ring

theorem uProj_norm_le (y : LowerSpace E) : ‖uProj E y‖ ≤ ‖y‖ := by
  have h := lower_norm_sq y
  nlinarith [sq_nonneg (sProj E y),sq_nonneg (zProj E y),norm_nonneg y,norm_nonneg (uProj E y)]

theorem sProj_norm_le (y : LowerSpace E) : |sProj E y| ≤ ‖y‖ := by
  have h := lower_norm_sq y
  nlinarith [sq_nonneg ‖uProj E y‖,sq_nonneg (zProj E y),norm_nonneg y,
    abs_nonneg (sProj E y),sq_abs (sProj E y)]

theorem zProj_norm_le (y : LowerSpace E) : |zProj E y| ≤ ‖y‖ := by
  have h := lower_norm_sq y
  nlinarith [sq_nonneg ‖uProj E y‖,sq_nonneg (sProj E y),norm_nonneg y,
    abs_nonneg (zProj E y),sq_abs (zProj E y)]

theorem uProj_opNorm_le : ‖uProj E‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro y
  simpa only [one_mul] using uProj_norm_le y

theorem sProj_opNorm_le : ‖sProj E‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro y
  simpa only [one_mul,Real.norm_eq_abs] using sProj_norm_le y

theorem zProj_opNorm_le : ‖zProj E‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro y
  simpa only [one_mul,Real.norm_eq_abs] using zProj_norm_le y

theorem pack_norm_sq (u : E) (s z : ℝ) : ‖pack E u s z‖^2 = ‖u‖^2+s^2+z^2 := by
  rw [lower_norm_sq,uProj_pack,sProj_pack,zProj_pack]

theorem pack_norm_le (u : E) (s z : ℝ) : ‖pack E u s z‖ ≤ ‖u‖+|s|+|z| := by
  have h := pack_norm_sq u s z
  nlinarith [norm_nonneg (pack E u s z), norm_nonneg u,abs_nonneg s,abs_nonneg z,
    mul_nonneg (norm_nonneg u) (abs_nonneg s),mul_nonneg (norm_nonneg u) (abs_nonneg z),
    mul_nonneg (abs_nonneg s) (abs_nonneg z),sq_abs s,sq_abs z]

theorem pack_ext {y y' : LowerSpace E}
    (hu : uProj E y = uProj E y') (hs : sProj E y = sProj E y')
    (hz : zProj E y = zProj E y') : y = y' := by
  apply (WithLp.equiv 2 (E × EuclideanSpace ℝ (Fin 2))).injective
  apply Prod.ext hu
  ext i
  fin_cases i
  · exact hs
  · exact hz

@[simp] theorem pack_zero : pack E (0:E) 0 0 = 0 := by
  apply pack_ext <;> simp

theorem pack_add (u v : E) (s t z w : ℝ) :
    pack E (u+v) (s+t) (z+w) = pack E u s z+pack E v t w := by
  apply pack_ext <;> simp

theorem pack_smul (c : ℝ) (u : E) (s z : ℝ) :
    pack E (c • u) (c*s) (c*z) = c • pack E u s z := by
  apply pack_ext <;> simp

end Bilevel.PolishedLiteralCompensated
