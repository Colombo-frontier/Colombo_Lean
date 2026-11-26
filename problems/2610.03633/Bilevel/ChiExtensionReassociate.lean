import Bilevel.ChiExtensionReadout
import Bilevel.ChiOuterCarrierSelectors

/-! Exact isometric reassociation of the extension variables to the partial
conjugate interface. All mixed derivative budgets are preserved. -/
noncomputable section
namespace Bilevel.ChiExtension
open PrimitiveGeometry
variable {X U V : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]

def associateLeft : Joint X (Joint U V) →ₗᵢ[ℝ] Joint (Joint X U) V where
  toFun z := pack (pack z.fst z.snd.fst) z.snd.snd
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  norm_map' z := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simp only [norm_sq]
    change (‖z.fst‖^2+‖z.snd.fst‖^2)+‖z.snd.snd‖^2=‖z.fst‖^2+(‖z.snd.fst‖^2+‖z.snd.snd‖^2)
    ring

def associateRight : Joint (Joint X U) V →ₗᵢ[ℝ] Joint X (Joint U V) where
  toFun z := pack z.fst.fst (pack z.fst.snd z.snd)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  norm_map' z := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simp only [norm_sq]
    change ‖z.fst.fst‖^2+(‖z.fst.snd‖^2+‖z.snd‖^2)=(‖z.fst.fst‖^2+‖z.fst.snd‖^2)+‖z.snd‖^2
    ring

theorem associateLeft_norm_le : ‖(associateLeft (X:=X) (U:=U) (V:=V)).toContinuousLinearMap‖≤1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro z
  simpa only [one_mul] using (associateLeft.norm_map z).le

theorem associateRight_norm_le : ‖(associateRight (X:=X) (U:=U) (V:=V)).toContinuousLinearMap‖≤1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro z
  simpa only [one_mul] using (associateRight.norm_map z).le

theorem associateLeft_right (z : Joint (Joint X U) V) : associateLeft (associateRight z)=z := rfl
theorem associateRight_left (z : Joint X (Joint U V)) : associateRight (associateLeft z)=z := rfl

def reassociate (f : Joint (Joint X U) V → ℝ) : Joint X (Joint U V) → ℝ := f ∘ associateLeft

theorem reassociate_contDiff {f : Joint (Joint X U) V → ℝ} (hf : ContDiff ℝ 3 f) :
    ContDiff ℝ 3 (reassociate f) := by
  change ContDiff ℝ 3 (f ∘ (associateLeft (X:=X) (U:=U) (V:=V)).toContinuousLinearMap)
  exact hf.comp (associateLeft (X:=X) (U:=U) (V:=V)).toContinuousLinearMap.contDiff

theorem reassociate_jet_bound {f : Joint (Joint X U) V → ℝ} (hf : ContDiff ℝ 3 f)
    (z : Joint X (Joint U V)) (k : ℕ) (hk : k≤3) :
    ‖iteratedFDeriv ℝ k (reassociate f) z‖≤‖iteratedFDeriv ℝ k f (associateLeft z)‖ :=
  ChiOuter.contraction_jet_bound (associateLeft (X:=X) (U:=U) (V:=V)).toContinuousLinearMap
    (associateLeft_norm_le (X:=X) (U:=U) (V:=V)) hf z k hk

end Bilevel.ChiExtension
