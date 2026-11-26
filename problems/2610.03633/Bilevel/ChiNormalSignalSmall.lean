import Bilevel.CompactNormalGradient
import Bilevel.ChiExtensionTerms

/-! A full-gradient bound for an actual compact normal term derived only
from its gradient Lipschitz constant and the normal support width. -/
noncomputable section
namespace Bilevel.ChiExtension
open PrimitiveGeometry
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def normalCoordinate (s : ℕ) (i : Fin s) : Full E s →L[ℝ] ℝ :=
  (CompensatedMean.sProj E).comp (normalSlice s i)

omit [CompleteSpace E] in
theorem normalCoordinate_apply (s : ℕ) (i : Fin s) (z : Full E s) : normalCoordinate s i z=z.snd i := by
  change CompensatedMean.sProj E (normalSlice s i (pack z.fst z.snd))=z.snd i
  rw [normalSlice_pack,CompensatedMean.sProj_pack]

def normalDirection (s : ℕ) (i : Fin s) : Full E s := pack 0 (EuclideanSpace.single i 1)

omit [CompleteSpace E] in
theorem normalDirection_coordinate (s : ℕ) (i : Fin s) :
    normalCoordinate s i (normalDirection (E:=E) s i)=1 := by
  rw [normalCoordinate_apply]
  change (EuclideanSpace.single i (1:ℝ)) i=1
  simp only [EuclideanSpace.single_apply,if_pos rfl,if_true]

omit [CompleteSpace E] in
theorem normalDirection_norm (s : ℕ) (i : Fin s) : ‖normalDirection (E:=E) s i‖=1 := by
  have hh := norm_sq (normalDirection (E:=E) s i)
  change ‖normalDirection (E:=E) s i‖^2=‖(0:E)‖^2+‖EuclideanSpace.single i (1:ℝ)‖^2 at hh
  simp only [norm_zero,zero_pow,zero_add,EuclideanSpace.norm_single,norm_one,one_pow] at hh
  norm_num at hh
  rcases hh with hh|hh
  · exact hh
  · nlinarith [norm_nonneg (normalDirection (E:=E) s i)]

theorem normalTerm_compact_gradient_bound (s : ℕ) (i : Fin s) (f : E → ℝ)
    (W dn : ℝ) (hW : 0<W) (δ : NNReal)
    (hLip : LipschitzWith δ (gradient (fun z => normalTerm s i f W z/dn))) (z : Full E s) :
    ‖gradient (fun y => normalTerm s i f W y/dn) z‖≤3*(δ:ℝ)*W := by
  apply CompactNormal.gradient_norm_le _ (normalCoordinate s i) (normalDirection s i) W hW
    (normalDirection_coordinate s i) (normalDirection_norm s i).le _ δ hLip z
  intro y hy
  rw [normalCoordinate_apply] at hy
  change normalTerm s i f W (pack y.fst y.snd)/dn=0
  rw [normalTerm_formula,SmallGapProfiles.normal_support W (y.snd i) hW hy,mul_zero,zero_div]

end Bilevel.ChiExtension
