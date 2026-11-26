import Bilevel.ChiCarrierRadialForce
import Bilevel.ChiCarrierFineCouplingLocality
import Bilevel.ChiFineSourceForce

/-! Actual selected fine extension: exact terminal-block pre-wrapper force
and its inverse-square-root variation bound, independent of recursion depth.
The common terminal parameters and radius are explicit geometric equalities. -/
noncomputable section
open scoped BigOperators
namespace Bilevel.ChiCarrier
open ChiBoundedChain ChiRecursive ZeroChainSchedule SmallGapLiftSupport
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem selectFamily_weighted_sum {ι : Type*} (S : Finset ι) (m : ℕ) (D : Geometry E)
    (leaf : ι → ℕ → List ℕ → Blocks m E → ℝ) (w : ι → ℝ)
    (d j : ℕ) (I : List ℕ) (x : Blocks m E) :
    selectFamily m D (fun k P y => ∑ a ∈ S,leaf a k P y*w a) d j I x=
      ∑ a ∈ S,selectFamily m D (leaf a) d j I x*w a := by
  induction d generalizing j I with
  | zero => rfl
  | succ d ih =>
    simp only [selectFamily,ih,Finset.mul_sum,Finset.sum_mul,mul_assoc]
    exact Finset.sum_comm

theorem selectedCoupling_eq_activeLeaves (m : ℕ) (D : Geometry E) (P : ChiFine.Parameters)
    (d j : ℕ) (I : List ℕ) (lambdaExt s : ℝ)
    (hell : ∀ Q,(D (j+d) Q).ell=P.ℓ) (hwidth : ∀ Q,(D (j+d) Q).width=P.β)
    (x : Blocks m E) :
    lambdaExt*selectedCoupling m D d j I P.c P.θ (CompensatedMean.pack (Blocks m E) x s 0)=
      selectFamily m D (fun k Q => jointLatentLeaf m k (D k Q)
        (P.activeSlice (D k Q).n lambdaExt s)) d j I x := by
  let leaf := fun k Q (y : Blocks m E) => ∑ p ∈ Finset.range (levels P.θ+1),
    jointFinePiece m k (D k Q) P.c P.θ p y*
      (lambdaExt*SmallGapProfiles.normal (width P.c P.β P.θ p) s)
  have he : selectFamily m D leaf d j I=
      selectFamily m D (fun k Q => jointLatentLeaf m k (D k Q)
        (P.activeSlice (D k Q).n lambdaExt s)) d j I := by
    apply selectFamily_congr_leaf
    intro Q
    funext y
    change (∑ p ∈ Finset.range (levels P.θ+1),jointFinePiece m (j+d) (D (j+d) Q) P.c P.θ p y*
      (lambdaExt*SmallGapProfiles.normal (width P.c P.β P.θ p) s))=
      P.activeSlice (D (j+d) Q).n lambdaExt s ((D (j+d) Q).coordinates (block m (j+d) y))
    rw [P.activeSlice_sum]
    apply Finset.sum_congr rfl
    intro p _
    simp only [jointFinePiece,Function.comp_apply,ChiFine.Parameters.pieces,
      ChiFine.Parameters.amplitude,hell,hwidth]
  rw [← he,selectFamily_weighted_sum]
  rw [selectedCoupling_slice_eq,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  simp only [selectedFinePiece,hwidth]
  ring

def selectedFineLatentForce (m : ℕ) (D : Geometry E) (P : ChiFine.Parameters)
    (lambdaExt s : ℝ) (d j : ℕ) (I : List ℕ) (x : Blocks m E) : E :=
  selectedLatentForce m D (fun k Q => P.activeSlice (D k Q).n lambdaExt s) d j I x

theorem selectedCoupling_terminal_force {m : ℕ} (D : Geometry E) (P : ChiFine.Parameters)
    (d j : ℕ) (I : List ℕ) (t : Fin m) (ht : t.val=j+d) (lambdaExt s R : ℝ) (hR : 0<R)
    (hell : ∀ Q,(D (j+d) Q).ell=P.ℓ) (hwidth : ∀ Q,(D (j+d) Q).width=P.β)
    (hRnode : ∀ Q,(D (j+d) Q).radius=R) (x : Blocks m E) :
    (gradient (fun y => lambdaExt*selectedCoupling m D d j I P.c P.θ
      (CompensatedMean.pack (Blocks m E) y s 0)) x) t=
      RadialWrapper.compressDerivative R (x t) (selectedFineLatentForce m D P lambdaExt s d j I x) := by
  rw [show (fun y => lambdaExt*selectedCoupling m D d j I P.c P.θ
    (CompensatedMean.pack (Blocks m E) y s 0))=
    selectFamily m D (fun k Q => jointLatentLeaf m k (D k Q)
      (P.activeSlice (D k Q).n lambdaExt s)) d j I from
        funext (selectedCoupling_eq_activeLeaves m D P d j I lambdaExt s hell hwidth)]
  exact selected_radial_terminal_gradient D _
    (fun k Q => P.activeSlice_contDiff (D k Q).n lambdaExt s) d j I t ht R hR hRnode x

set_option maxHeartbeats 800000 in
theorem selectedFineLatentForce_bound : ∃ B : ℝ,1≤B ∧
    ∀ (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
      (m : ℕ) (D : Geometry F) (P : ChiFine.Parameters) (lambdaExt : ℝ),0≤lambdaExt →
      ∀ (s : ℝ) (d j : ℕ) (I : List ℕ) (x : Blocks m F),
      ‖selectedFineLatentForce m D P lambdaExt s d j I x‖≤
        2*C*B*lambdaExt*P.c*P.ℓ*P.β^2/Real.sqrt P.θ := by
  obtain ⟨B,hB,hforce⟩ := ChiFine.latent_active_force_bound
  refine ⟨B,hB,fun F _ _ _ m D P lambdaExt hlambda s d j I x => ?_⟩
  have hb : 0≤2*C*B*lambdaExt*P.ℓ*P.β*width P.c P.β P.θ 0 := by
    have := C_pos
    have := P.ell_nonneg
    have := P.β_pos
    have := width_pos P.c P.β P.θ P.c_pos P.β_pos P.θ_ge_one 0
    positivity
  apply (selectedLatentForce_norm_le m D (fun k Q => P.activeSlice (D k Q).n lambdaExt s) d j I x _ hb
    (fun Q z => hforce P (D (j+d) Q).n lambdaExt hlambda s z)).trans_eq
  rw [ChiFine.first_normal_width P.c P.β P.θ (by linarith [P.θ_ge_one])]
  ring

end Bilevel.ChiCarrier
