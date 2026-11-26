import Bilevel.ChiHierarchyIndex
import Bilevel.ChiSourceAuxiliaryFrame
import Bilevel.TransportNetworkAuxiliary

/-! An actual finite independent Haar prior for the macro frame and every
legal hierarchy node. Reindexing identifies it exactly with the auxiliary
orientation product used by the transport observer. -/
noncomputable section
open MeasureTheory
namespace Bilevel.ChiHierarchyHaar
open ChiHierarchyIndex

abbrev Orientations (counts : ℕ → ℕ) (J D : ℕ) := FrameIndex counts J → OrthogonalHaar.Group D

def law (counts : ℕ → ℕ) (J D : ℕ) : Measure (Orientations counts J D) :=
  Measure.pi (fun _ => OrthogonalHaar.law D)

instance probability (counts : ℕ → ℕ) (J D : ℕ) : IsProbabilityMeasure (law counts J D) := by
  unfold law
  infer_instance

def enumerateOrientations (counts : ℕ → ℕ) (J D : ℕ) (a : Orientations counts J D) :
    Fin (Fintype.card (FrameIndex counts J)) → OrthogonalHaar.Group D :=
  fun i => a ((enumerate counts J).symm i)

theorem enumerate_preserving (counts : ℕ → ℕ) (J D : ℕ) :
    MeasurePreserving (enumerateOrientations counts J D) (law counts J D)
      (Measure.pi (fun _ : Fin (Fintype.card (FrameIndex counts J)) => OrthogonalHaar.law D)) := by
  convert measurePreserving_piCongrLeft (fun _ => OrthogonalHaar.law D) (enumerate counts J) using 1
  funext a i
  simp [enumerateOrientations,MeasurableEquiv.coe_piCongrLeft]

def columns {counts : ℕ → ℕ} {J D : ℕ}
    (hD : ∀ i : FrameIndex counts J, chainSize i+1 ≤ D) (a : Orientations counts J D)
    (i : FrameIndex counts J) : Fin (chainSize i+1) → EuclideanGaussian.Space D :=
  HaarFrame.frame D (chainSize i+1) (hD i) (a i)

theorem columns_measurable {counts : ℕ → ℕ} {J D : ℕ}
    (hD : ∀ i : FrameIndex counts J, chainSize i+1 ≤ D) : Measurable (columns hD) := by
  apply measurable_pi_lambda
  intro i
  exact (HaarFrame.frame_measurable D _ (hD i)).comp (measurable_pi_apply i)

theorem columns_preserving {counts : ℕ → ℕ} {J D : ℕ}
    (hD : ∀ i : FrameIndex counts J, chainSize i+1 ≤ D) :
    MeasurePreserving (columns hD) (law counts J D)
      (Measure.pi (fun i => HaarFrame.frameLaw D (chainSize i+1) (hD i))) :=
  measurePreserving_pi _ _ (fun i => ⟨HaarFrame.frame_measurable D _ (hD i),rfl⟩)

theorem columns_orthonormal {counts : ℕ → ℕ} {J D : ℕ}
    (hD : ∀ i : FrameIndex counts J, chainSize i+1 ≤ D) (a : Orientations counts J D)
    (i : FrameIndex counts J) : Orthonormal ℝ (columns hD a i) :=
  HaarFrame.frame_orthonormal D _ (hD i) (a i)

def frame {counts : ℕ → ℕ} {J D : ℕ}
    (hD : ∀ i : FrameIndex counts J, chainSize i+1 ≤ D) (a : Orientations counts J D)
    (i : FrameIndex counts J) : ChiBoundedChain.Space (chainSize i) →ₗᵢ[ℝ] EuclideanGaussian.Space D :=
  (OrthogonalAction.isometry D (a i)).toLinearIsometry.comp
    (ChiPrefixEvaluation.auxiliaryFrame (chainSize i) D (hD i))

theorem frame_basis {counts : ℕ → ℕ} {J D : ℕ}
    (hD : ∀ i : FrameIndex counts J, chainSize i+1 ≤ D) (a : Orientations counts J D)
    (i : FrameIndex counts J) (k : Fin (chainSize i+1)) :
    frame hD a i (ChiBoundedChain.basis k) = columns hD a i k := by
  change OrthogonalAction.isometry D (a i)
    (ChiPrefixEvaluation.auxiliaryFrame _ D (hD i) (ChiBoundedChain.basis k)) = _
  rw [ChiPrefixEvaluation.auxiliaryFrame_basis]
  simp only [columns,HaarFrame.frame,EuclideanSpace.basisFun_apply]
  rfl

abbrev NetworkSample (counts : ℕ → ℕ) (J n D : ℕ) :=
  TransportNetwork.Latent n D × Orientations counts J D

def networkLaw (counts : ℕ → ℕ) (J n D : ℕ) : Measure (NetworkSample counts J n D) :=
  (TransportNetwork.law n D).prod (law counts J D)

instance network_probability (counts : ℕ → ℕ) (J n D : ℕ) :
    IsProbabilityMeasure (networkLaw counts J n D) := by
  unfold networkLaw
  infer_instance

def asAuxiliary (counts : ℕ → ℕ) (J n D : ℕ) (a : NetworkSample counts J n D) :
    TransportNetworkAuxiliary.Sample n D (Fintype.card (FrameIndex counts J)) :=
  (a.1,enumerateOrientations counts J D a.2)

theorem asAuxiliary_preserving (counts : ℕ → ℕ) (J n D : ℕ) :
    MeasurePreserving (asAuxiliary counts J n D) (networkLaw counts J n D)
      (TransportNetworkAuxiliary.law n D (Fintype.card (FrameIndex counts J))) :=
  (MeasurePreserving.id (TransportNetwork.law n D)).prod (enumerate_preserving counts J D)

theorem asAuxiliary_columns {counts : ℕ → ℕ} {J n D : ℕ}
    (hD : ∀ i : FrameIndex counts J, chainSize i+1 ≤ D) (a : NetworkSample counts J n D)
    (i : FrameIndex counts J) :
    TransportNetworkAuxiliary.auxiliaryFrame (chainSize i+1) (hD i) (enumerate counts J i)
      (asAuxiliary counts J n D a) = columns hD a.2 i := by
  simp only [TransportNetworkAuxiliary.auxiliaryFrame,asAuxiliary,enumerateOrientations,
    Equiv.symm_apply_apply,columns]

end Bilevel.ChiHierarchyHaar
