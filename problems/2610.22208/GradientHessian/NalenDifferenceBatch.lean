import GradientHessian.NalenPolicy
import GradientHessian.ClockedOracleExpansion
import GradientHessian.NalenSymmetricDifference

/-! The actual d+1-query finite-difference decoder. It queries the
snapshot itself and its coordinate shifts, then symmetrizes the recovered
gradient columns. Joint measurability and operator error are proved. -/

noncomputable section
namespace GradientHessian.NalenPolicy
open Model Nalen MeasureTheory
open scoped InnerProductSpace

def encodeHessian {d : ℕ} (B : Point d →L[ℝ] Point d) : Second d :=
  (InnerProductSpace.toDual ℝ (Point d)).toContinuousLinearEquiv.toContinuousLinearMap.comp B

theorem encodeHessian_continuous (d : ℕ) : Continuous (encodeHessian (d := d)) :=
  continuous_const.clm_comp continuous_id

theorem readHessian_encoded {d : ℕ} (a : ℝ) (g : First d) (B : Point d →L[ℝ] Point d) :
    readHessian (a,g,encodeHessian B)=B := by
  apply ContinuousLinearMap.ext
  intro x
  change (InnerProductSpace.toDual ℝ (Point d)).symm ((InnerProductSpace.toDual ℝ (Point d)) (B x))=B x
  exact (InnerProductSpace.toDual ℝ (Point d)).symm_apply_apply _

def differenceQuery (d : ℕ) (δ : ℝ) (j : Fin (d+1)) (z : Point d) : Point d :=
  Fin.cases z (fun i => z+differenceStep (Fin d) δ • EuclideanSpace.basisFun (Fin d) ℝ i) j

theorem differenceQuery_measurable (d : ℕ) (δ : ℝ) (j : Fin (d+1)) :
    Measurable (differenceQuery d δ j) := by
  refine Fin.cases ?_ (fun i => ?_) j
  · exact measurable_id
  · exact measurable_id.add_const _

def differenceDecode (d : ℕ) (δ : ℝ) (ys : Fin (d+1) → OrdinaryReply d) : RichReply d :=
  ((ys 0).1,(ys 0).2,encodeHessian (approximateFromGradients (EuclideanSpace.basisFun (Fin d) ℝ) δ
    (readGradient (ys 0)) (fun i => readGradient (ys i.succ))))

theorem differenceApproximate_continuous (d : ℕ) (δ : ℝ) :
    Continuous (fun p : Point d × (Fin d → Point d) =>
      approximateFromGradients (EuclideanSpace.basisFun (Fin d) ℝ) δ p.1 p.2) :=
  approximateFromGradients_continuous (E := Point d) (I := Fin d) _ δ

theorem differenceDecode_continuous (d : ℕ) (δ : ℝ) : Continuous (differenceDecode d δ) := by
  have he (i : Fin (d+1)) : Continuous (fun ys : Fin (d+1) → OrdinaryReply d => readGradient (ys i)) :=
    (InnerProductSpace.toDual ℝ (Point d)).symm.continuous.comp (continuous_apply i).snd
  have hinput : Continuous (fun ys : Fin (d+1) → OrdinaryReply d =>
      (readGradient (ys 0),fun i : Fin d => readGradient (ys i.succ))) :=
    (he 0).prodMk (continuous_pi (fun i => he i.succ))
  have hB : Continuous (fun ys : Fin (d+1) → OrdinaryReply d =>
      approximateFromGradients (EuclideanSpace.basisFun (Fin d) ℝ) δ
        (readGradient (ys 0)) (fun i => readGradient (ys i.succ))) := by
    simpa only [Function.comp_def] using (differenceApproximate_continuous d δ).comp hinput
  exact (continuous_apply (0 : Fin (d+1))).fst.prodMk
    ((continuous_apply (0 : Fin (d+1))).snd.prodMk ((encodeHessian_continuous d).comp hB))

theorem differenceDecode_measurable (d : ℕ) (δ : ℝ) : Measurable (differenceDecode d δ) :=
  (differenceDecode_continuous d δ).measurable

theorem readHessian_differenceDecode (d : ℕ) (δ : ℝ) (ys : Fin (d+1) → OrdinaryReply d) :
    readHessian (differenceDecode d δ ys)=approximateFromGradients (EuclideanSpace.basisFun (Fin d) ℝ) δ
      (readGradient (ys 0)) (fun i => readGradient (ys i.succ)) :=
  readHessian_encoded _ _ _

def differenceBatch (d : ℕ) (δ : ℝ) :
    ClockedOracle.Batch (Point d) (OrdinaryReply d) (RichReply d) (d+1) where
  query := differenceQuery d δ
  decode := fun p => differenceDecode d δ p.2
  default := (0,0)
  query_measurable := differenceQuery_measurable d δ
  decode_measurable := (differenceDecode_measurable d δ).comp measurable_snd

def differenceRich {d : ℕ} (δ : ℝ) (f : Point d → ℝ) : Point d → RichReply d :=
  (differenceBatch d δ).oracle (ordinaryOracle f)

theorem differenceRich_hessian {d : ℕ} (δ : ℝ) (f : Point d → ℝ) (z : Point d) :
    readHessian (differenceRich δ f z)=
      approximateFromGradients (EuclideanSpace.basisFun (Fin d) ℝ) δ (gradient f z)
        (fun i => gradient f (z+differenceStep (Fin d) δ • EuclideanSpace.basisFun (Fin d) ℝ i)) := by
  change readHessian (differenceDecode d δ (fun i => ordinaryOracle f (differenceQuery d δ i z)))=_
  rw [readHessian_differenceDecode]
  rfl

theorem differenceRich_symmetric {d : ℕ} (δ : ℝ) (f : Point d → ℝ) (z x y : Point d) :
    ⟪readHessian (differenceRich δ f z) x,y⟫_ℝ=⟪x,readHessian (differenceRich δ f z) y⟫_ℝ := by
  rw [differenceRich_hessian]
  exact approximateFromGradients_symmetric _ _ _ _ _ _

theorem differenceRich_error {d : ℕ} (hd : 0<d) {δ : ℝ} (hδ : 0<δ)
    {f : Point d → ℝ} (hf : ContDiff ℝ 2 f) (hL : LipschitzWith 1 (fderiv ℝ (fderiv ℝ f))) (z : Point d) :
    ‖readHessian (differenceRich δ f z)-hessianOperator f z‖≤δ := by
  letI : Nonempty (Fin d) := ⟨⟨0,hd⟩⟩
  rw [differenceRich_hessian]
  exact approximateFromGradients_error _ hf hL z hδ

end GradientHessian.NalenPolicy
