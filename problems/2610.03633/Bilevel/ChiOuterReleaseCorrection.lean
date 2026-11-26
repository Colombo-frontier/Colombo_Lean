import Bilevel.ChiOuterReleaseJets

/-! Actual mixed release-correction budgets at the macro-to-base interface. -/
noncomputable section
open scoped BigOperators
namespace Bilevel.ChiOuter
open ChiBoundedChain ChiRecursive ChiCarrier PrimitiveGeometry
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

theorem outerReleaseCorrection_selected (m : ℕ) (M : Node E) (kids : Fin (M.n+1) → Node F) :
    outerReleaseCorrection m M kids=fun z => ∑ i : Fin (M.n+1),jointOuterSelector m M i z*
      (outerIncomingFactor m M i z*(jointRelease m 0 (kids i) z.snd-1)) := by
  funext z
  apply Finset.sum_congr rfl
  intro i _
  rw [outerResidual_factor]
  ring

theorem constructed_outer_release_correction_jets : ∃ C : ℝ,1≤C ∧
    ∀ (E F : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
      [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
      (M : Node E) (kids : Fin (M.n+1) → Node F),0≤M.ell → 0<M.width → M.width≤M.radius →
      (∀ i,0≤(kids i).ell) → (∀ i,0<(kids i).width) → (∀ i,(kids i).width≤(kids i).radius) →
      (∀ i,(kids i).parentWidth=M.width) → (∀ i,M.width≤(kids i).radius) →
      ∀ (m : ℕ) (z : Joint E (Blocks m F)) (k : ℕ),k≤3 →
      ‖iteratedFDeriv ℝ k (outerReleaseCorrection m M kids) z‖≤C*(M.ell*M.width^2)/M.width^k := by
  obtain ⟨Cr,hCr,hres⟩ := constructed_outer_residual_jets
  obtain ⟨Cq,hCq,hrel⟩ := constructed_joint_node_jets
  have hCr0 : 0≤Cr := by linarith
  have hCq0 : 0≤Cq := by linarith
  refine ⟨8*Cr*Cq,by nlinarith [mul_le_mul hCr hCq zero_le_one hCr0],
    fun E F _ _ _ _ _ _ M kids hell hh hhR hcell hch hchR hcparent hcR m z k hk => ?_⟩
  let f := fun i : Fin (M.n+1) => fun y : Joint E (Blocks m F) =>
    outerIncomingFactor m M i y*(jointRelease m 0 (kids i) y.snd-1)
  have hf (i : Fin (M.n+1)) : ContDiff ℝ 3 (f i) :=
    (outerIncomingFactor_contDiff m M i).mul
      (((jointRelease_contDiff m 0 (kids i) 3).comp (innerProjection (E:=E) (F:=F) m).contDiff).sub contDiff_const)
  rw [outerReleaseCorrection_selected]
  apply outer_selected_joint_sum_bound m M f hf z k hk _ (by positivity)
  intro i
  have he : (fun y => jointOuterSelector m M i y*f i y)=
      fun y => wrappedResidual M i y.fst*(jointRelease m 0 (kids i) y.snd-1) := by
    funext y
    rw [outerResidual_factor]
    dsimp only [f]
    ring
  rw [he]
  have hr (q : ℕ) (hq : q≤k) :
      ‖iteratedFDeriv ℝ q (fun y : Joint E (Blocks m F) => wrappedResidual M i y.fst) z‖≤
        (Cr*(M.ell*M.width^2))/M.width^q := hres E F M hell hh hhR m i z q (by omega)
  have hq (q : ℕ) (hq : q≤k) :
      ‖iteratedFDeriv ℝ q (fun y : Joint E (Blocks m F) => jointRelease m 0 (kids i) y.snd-1) z‖≤Cq/M.width^q := by
    apply (contraction_jet_bound (innerProjection (E:=E) (F:=F) m) (innerProjection_norm_le m)
      ((jointRelease_contDiff m 0 (kids i) 3).sub contDiff_const) z q (by omega)).trans
    apply release_sub_one_jet_bound m 0 (kids i) Cq M.width hCq z.snd q (by omega)
    have hz := (hrel F (kids i) (hcell i) (hch i) (hchR i)
      (by rw [hcparent i];exact hh) (by rw [hcparent i];exact hcR i) m 0 0 z.snd q (by omega)).2.2
    simpa only [hcparent i] using hz
  have hs := same_width_product_jets ((wrappedResidual_contDiff M i 3).comp
      (outerProjection (E:=E) (F:=F) m).contDiff)
    (((jointRelease_contDiff m 0 (kids i) 3).comp (innerProjection (E:=E) (F:=F) m).contDiff).sub contDiff_const)
    (Cr*(M.ell*M.width^2)) Cq M.width (by positivity) hCq0 hh z k hk hr hq
  convert hs using 1
  ring

end Bilevel.ChiOuter
