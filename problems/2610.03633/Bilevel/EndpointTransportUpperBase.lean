import Bilevel.EndpointTransportRadialSpace
import Bilevel.EndpointTransportOuterCarriers
import Bilevel.ChiOuterSourceUpperBase

/-! The actual physical upper base. The last-parent release remains in the
physical carrier, including at depth one; the macro-only term is separated
before estimating the lower-variable gradient. -/
noncomputable section
set_option maxHeartbeats 300000
namespace Bilevel.EndpointTransportResponse
open ChiBoundedChain ChiRecursive ChiCarrier ChiOuter PrimitiveGeometry PartialLegendre
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem scalar_add_jet_bound {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (f g : X → ℝ) (hf : ContDiff ℝ 3 f) (hg : ContDiff ℝ 3 g)
    (x : X) (k : ℕ) (hk : k≤3) (A B : ℝ)
    (ha : ‖iteratedFDeriv ℝ k f x‖≤A) (hb : ‖iteratedFDeriv ℝ k g x‖≤B) :
    ‖iteratedFDeriv ℝ k (fun y => f y+g y) x‖≤A+B := by
  have hk' : (k:WithTop ℕ∞)≤3 := by exact_mod_cast hk
  rw [iteratedFDeriv_add_apply' ((hf.of_le hk').contDiffAt) ((hg.of_le hk').contDiffAt)]
  exact (norm_add_le _ _).trans (add_le_add ha hb)

def baseOrdinaryCoordinates (m n D : ℕ) : PhysicalBase E m n D →L[ℝ] Joint E (Blocks m (Block D)) :=
  packLinear.comp ((baseMacroProjection m n D).prod (baseOrdinaryProjection m n D))

omit [CompleteSpace E] in
theorem baseOrdinaryCoordinates_norm (m n D : ℕ) : ‖baseOrdinaryCoordinates (E:=E) m n D‖≤1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro z
  change ‖pack z.fst z.snd.fst‖≤1*‖z‖
  rw [one_mul]
  have h1 := norm_sq z
  have h2 := norm_sq z.snd
  have h3 := norm_sq (pack z.fst z.snd.fst)
  change ‖pack z.fst z.snd.fst‖^2=‖z.fst‖^2+‖z.snd.fst‖^2 at h3
  nlinarith [norm_nonneg z,norm_nonneg (pack z.fst z.snd.fst),sq_nonneg ‖z.snd.snd‖]

def physicalBaseLower {n D : ℕ} (m : ℕ) (Q : Rotations n D) (M : Node E)
    (G : Geometry (Block D)) (d : ℕ) (ρ R : ℝ) (z : PhysicalBase E m n D) : ℝ :=
  outerReleaseCorrection m M (fun i => G 0 [i.val]) (baseOrdinaryCoordinates m n D z)+
    outerPhysicalCarrier m Q M (baseMacroProjection m n D) G
      (baseOrdinaryProjection m n D) (basePhysicalProjection m n D) d 0 z+
    baseRadial m ρ R (baseOrdinaryCoordinates m n D z)

def physicalUpperBase {n D : ℕ} (m : ℕ) (Q : Rotations n D) (M : Node E) (ν : ℝ)
    (G : Geometry (Block D)) (d : ℕ) (ρ R : ℝ) (z : PhysicalBase E m n D) : ℝ :=
  macroValue M.n M.ell M.width ν M.radius M.frame (baseMacroProjection m n D z)+physicalBaseLower m Q M G d ρ R z

theorem physicalBaseLower_contDiff {n D : ℕ} (m : ℕ) (Q : Rotations n D) (M : Node E)
    (G : Geometry (Block D)) (d : ℕ) (ρ R : ℝ) : ContDiff ℝ 3 (physicalBaseLower m Q M G d ρ R) := by
  have he : physicalBaseLower m Q M G d ρ R=
      ((outerReleaseCorrection m M (fun i => G 0 [i.val])) ∘ baseOrdinaryCoordinates m n D)+
      outerPhysicalCarrier m Q M (baseMacroProjection m n D) G
        (baseOrdinaryProjection m n D) (basePhysicalProjection m n D) d 0+
      (baseRadial m ρ R ∘ baseOrdinaryCoordinates m n D) := rfl
  rw [he]
  have hcor := (outerReleaseCorrection_contDiff m M (fun i => G 0 [i.val])).comp
    (baseOrdinaryCoordinates m n D).contDiff
  have hcar := outerPhysicalCarrier_contDiff m Q M (baseMacroProjection m n D) G
    (baseOrdinaryProjection m n D) (basePhysicalProjection m n D) d 0
  have hrad := (baseRadial_contDiff m ρ R).comp (baseOrdinaryCoordinates (E:=E) m n D).contDiff
  exact (hcor.add hcar).add hrad

theorem physicalUpperBase_contDiff {n D : ℕ} (m : ℕ) (Q : Rotations n D) (M : Node E) (ν : ℝ)
    (G : Geometry (Block D)) (d : ℕ) (ρ R : ℝ) : ContDiff ℝ 3 (physicalUpperBase m Q M ν G d ρ R) := by
  have he : physicalUpperBase m Q M ν G d ρ R=
      (macroValue M.n M.ell M.width ν M.radius M.frame ∘ baseMacroProjection m n D)+
        physicalBaseLower m Q M G d ρ R := rfl
  rw [he]
  have hm := (macro_contDiff M ν 3).comp (baseMacroProjection m n D).contDiff
  exact hm.add (physicalBaseLower_contDiff m Q M G d ρ R)

theorem physicalBaseLower_jet_bound {n D : ℕ} (m : ℕ) (Q : Rotations n D) (M : Node E)
    (G : Geometry (Block D)) (d : ℕ) (ρ R : ℝ) (z : PhysicalBase E m n D)
    (k : ℕ) (hk : k≤3) (Bc Br Bp : ℝ)
    (hc : ‖iteratedFDeriv ℝ k (outerReleaseCorrection m M (fun i => G 0 [i.val]))
      (baseOrdinaryCoordinates m n D z)‖≤Bc)
    (hr : ‖iteratedFDeriv ℝ k (outerPhysicalCarrier m Q M (baseMacroProjection m n D) G
      (baseOrdinaryProjection m n D) (basePhysicalProjection m n D) d 0) z‖≤Br)
    (hp : ‖iteratedFDeriv ℝ k (baseRadial m ρ R) (baseOrdinaryCoordinates m n D z)‖≤Bp) :
    ‖iteratedFDeriv ℝ k (physicalBaseLower m Q M G d ρ R) z‖≤Bc+Br+Bp := by
  have hk' : (k:WithTop ℕ∞)≤3 := by exact_mod_cast hk
  let C := baseOrdinaryCoordinates (E:=E) m n D
  have hcor := (outerReleaseCorrection_contDiff m M (fun i => G 0 [i.val])).comp C.contDiff
  have hcar := outerPhysicalCarrier_contDiff m Q M (baseMacroProjection m n D) G
    (baseOrdinaryProjection m n D) (basePhysicalProjection m n D) d 0
  have hrad := (baseRadial_contDiff m ρ R).comp C.contDiff
  change ‖iteratedFDeriv ℝ k (fun x =>
    ((outerReleaseCorrection m M (fun i => G 0 [i.val])) ∘ C) x+
    (outerPhysicalCarrier m Q M (baseMacroProjection m n D) G
      (baseOrdinaryProjection m n D) (basePhysicalProjection m n D) d 0) x+
    (baseRadial m ρ R ∘ C) x) z‖≤Bc+Br+Bp
  rw [iteratedFDeriv_add_apply' (((hcor.add hcar).of_le hk').contDiffAt) ((hrad.of_le hk').contDiffAt),
    iteratedFDeriv_add_apply' ((hcor.of_le hk').contDiffAt) ((hcar.of_le hk').contDiffAt)]
  exact (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add
    ((linear_jet_contraction C (baseOrdinaryCoordinates_norm m n D)
      (outerReleaseCorrection_contDiff m M (fun i => G 0 [i.val])) z k hk).trans hc) hr))
    ((linear_jet_contraction C (baseOrdinaryCoordinates_norm m n D) (baseRadial_contDiff m ρ R) z k hk).trans hp))

theorem physicalUpperBase_lower_gradient_bound {n D : ℕ} (m : ℕ) (Q : Rotations n D) (M : Node E) (ν : ℝ)
    (G : Geometry (Block D)) (d : ℕ) (ρ R : ℝ) (x : E) (v : HybridTangent (Blocks m (Block D)) n D)
    (B : ℝ) (hb : ‖iteratedFDeriv ℝ 1 (physicalBaseLower m Q M G d ρ R) (pack x v)‖≤B) :
    ‖gradient (fun w => physicalUpperBase m Q M ν G d ρ R (pack x w)) v‖≤B := by
  have hg := (((physicalBaseLower_contDiff m Q M G d ρ R).differentiable (by norm_num)) (pack x v)).hasGradientAt
  have hy := PrimitiveGeometry.partial_y hg
  rw [Composition.norm_first,← GradientJetBounds.gradient_norm_eq] at hb
  change ‖gradient (fun w => macroValue M.n M.ell M.width ν M.radius M.frame x+
    physicalBaseLower m Q M G d ρ R (pack x w)) v‖≤B
  rw [← norm_fderiv_eq_norm_gradient,fderiv_const_add,norm_fderiv_eq_norm_gradient,hy.gradient]
  exact (WithLp.norm_snd_le E (gradient (physicalBaseLower m Q M G d ρ R) (pack x v))).trans hb

end Bilevel.EndpointTransportResponse

