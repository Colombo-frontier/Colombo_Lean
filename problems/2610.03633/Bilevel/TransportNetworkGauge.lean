import Bilevel.ProjectionPosterior
import Mathlib.MeasureTheory.Constructions.Pi

/-! An actual random path network: one independent Haar root orientation and
independent Haar edge maps. Layerwise gauge transformations preserve this
product law and transport each physical frame equivariantly. -/
noncomputable section
open MeasureTheory
open scoped RealInnerProductSpace BigOperators
namespace Bilevel.TransportNetwork
open EuclideanGaussian OrthogonalAction
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 400000

abbrev Vertex (n : ℕ) := Fin (n+1)
abbrev Edge (n : ℕ) := Fin n
abbrev Gauge (n d : ℕ) := Vertex n → OrthogonalHaar.Group d
abbrev Latent (n d : ℕ) := OrthogonalHaar.Group d × (Edge n → OrthogonalHaar.Group d)

def src {n : ℕ} (i : Edge n) : Vertex n := i.castSucc
def dst {n : ℕ} (i : Edge n) : Vertex n := i.succ

def gauge {n d : ℕ} (R : Gauge n d) (z : Latent n d) : Latent n d :=
  (R 0*z.1,fun i => R (dst i)*z.2 i*(R (src i))⁻¹)

instance gaugeAction (n d : ℕ) : MulAction (Gauge n d) (Latent n d) where
  smul := gauge
  one_smul z := by
    change gauge 1 z = z
    apply Prod.ext
    · simp [gauge]
    · funext i; simp [gauge]
  mul_smul R S z := by
    change gauge (R*S) z = gauge R (gauge S z)
    apply Prod.ext
    · simp [gauge,mul_assoc]
    · funext i; simp [gauge,mul_assoc]

@[simp] theorem gauge_action_apply {n d : ℕ} (R : Gauge n d) (z : Latent n d) :
    R • z = gauge R z := rfl

theorem gauge_continuous (n d : ℕ) :
    Continuous (fun p : Gauge n d × Latent n d => gauge p.1 p.2) := by
  apply Continuous.prodMk
  · exact ((continuous_apply 0).comp continuous_fst).mul (continuous_fst.comp continuous_snd)
  · apply continuous_pi
    intro i
    exact (((continuous_apply (dst i)).comp continuous_fst).mul
      ((continuous_apply i).comp (continuous_snd.comp continuous_snd))).mul
      (((continuous_apply (src i)).comp continuous_fst).inv)

instance gaugeMeasurableAction (n d : ℕ) : MeasurableSMul₂ (Gauge n d) (Latent n d) :=
  ⟨(gauge_continuous n d).measurable⟩

def law (n d : ℕ) : Measure (Latent n d) :=
  (OrthogonalHaar.law d).prod (Measure.pi (fun _ : Edge n => OrthogonalHaar.law d))

instance law_probability (n d : ℕ) : IsProbabilityMeasure (law n d) := by
  unfold law
  infer_instance

theorem gauge_preserving (n d : ℕ) (R : Gauge n d) :
    MeasurePreserving (gauge R) (law n d) (law n d) := by
  have hr := measurePreserving_mul_left (OrthogonalHaar.law d) (R 0)
  have he (i : Edge n) : MeasurePreserving
      (fun A : OrthogonalHaar.Group d => R (dst i)*A*(R (src i))⁻¹)
      (OrthogonalHaar.law d) (OrthogonalHaar.law d) :=
    (measurePreserving_mul_right (OrthogonalHaar.law d) (R (src i))⁻¹).comp
      (measurePreserving_mul_left (OrthogonalHaar.law d) (R (dst i)))
  exact hr.prod (measurePreserving_pi _ _ he)

/-- Orientations are computed along the actual edges, with unused natural
indices padded by identity only outside the finite physical path. -/
def orientation {n d : ℕ} (z : Latent n d) : ℕ → OrthogonalHaar.Group d
  | 0 => z.1
  | k+1 => (if h : k < n then z.2 ⟨k,h⟩ else 1)*orientation z k

theorem orientation_continuous (n d k : ℕ) :
    Continuous (fun z : Latent n d => orientation z k) := by
  induction k with
  | zero => exact continuous_fst
  | succ k ih =>
    by_cases h : k < n
    · simpa only [orientation,dif_pos h] using
        (((continuous_apply (⟨k,h⟩ : Edge n)).comp continuous_snd).mul ih)
    · simpa only [orientation,dif_neg h,one_mul] using ih

theorem orientation_gauge {n d : ℕ} (R : Gauge n d) (z : Latent n d)
    (k : ℕ) (hk : k ≤ n) :
    orientation (gauge R z) k = R ⟨k,Nat.lt_succ_of_le hk⟩*orientation z k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hkn : k < n := Nat.lt_of_succ_le hk
    rw [orientation,orientation,dif_pos hkn,dif_pos hkn,ih (Nat.le_of_lt hkn)]
    simp [gauge,src,dst,mul_assoc]

def frame {n d : ℕ} (T : ℕ) (hT : T ≤ d) (z : Latent n d)
    (v : Vertex n) (i : Fin T) : Space d :=
  orientation z v.val • (EuclideanSpace.basisFun (Fin d) ℝ) (Fin.castLE hT i)

theorem frame_coordinate_measurable (n d T : ℕ) (hT : T ≤ d) (v : Vertex n) (i : Fin T) :
    Measurable (fun z : Latent n d => frame T hT z v i) := by
  change Measurable (fun z : Latent n d =>
    HaarFrame.frame d T hT (orientation z v.val) i)
  exact ((measurable_pi_apply i).comp (HaarFrame.frame_measurable d T hT)).comp
    (orientation_continuous n d v.val).measurable

theorem frame_measurable (n d T : ℕ) (hT : T ≤ d) :
    Measurable (frame (n := n) (d := d) T hT) :=
  measurable_pi_lambda _ (fun v => measurable_pi_lambda _
    (fun i => frame_coordinate_measurable n d T hT v i))

theorem frame_orthonormal {n d : ℕ} (T : ℕ) (hT : T ≤ d)
    (z : Latent n d) (v : Vertex n) : Orthonormal ℝ (frame T hT z v) :=
  (((EuclideanSpace.basisFun (Fin d) ℝ).orthonormal.comp (Fin.castLE hT)
    (Fin.castLE_injective hT)).comp_linearIsometryEquiv (isometry d (orientation z v.val)))

theorem frame_gauge {n d : ℕ} (T : ℕ) (hT : T ≤ d) (R : Gauge n d)
    (z : Latent n d) (v : Vertex n) (i : Fin T) :
    frame T hT (gauge R z) v i = R v • frame T hT z v i := by
  unfold frame
  rw [orientation_gauge R z v.val (Nat.le_of_lt_succ v.isLt),mul_smul]

theorem edge_frame {n d : ℕ} (T : ℕ) (hT : T ≤ d) (z : Latent n d)
    (e : Edge n) (i : Fin T) :
    z.2 e • frame T hT z (src e) i = frame T hT z (dst e) i := by
  simp only [frame,src,dst,Fin.val_succ,Fin.coe_castSucc,orientation,dif_pos e.isLt,mul_smul]

end Bilevel.TransportNetwork
