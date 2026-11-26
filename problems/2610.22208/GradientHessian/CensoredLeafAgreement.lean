import GradientHessian.CensoredLeafOracle
import GradientHessian.NumericalGateJets

/-! Equality with the literal leaf under the concrete local miss conditions.
The current inner port removes the entire future forcing tail. Hidden memory
blocks become their public quadratics; the current unknown numerical gate
is removed by its pointwise second jet, including the closed plateau seam. -/

noncomputable section
namespace GradientHessian.CensoredLeaf

open Classical InnerCoordinates JetLocality SecondJetAlgebra Filter
open scoped Topology BigOperators

variable {Y E : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] {m : ℕ}

theorem weighted_prefix (p e : Fin m → ℝ) (k : Fin m) (hk : p k=0) :
    (∑ i,InnerSelector.weight p i*e i)=
      (∑ i,if i<k then InnerSelector.weight p i*e i else 0)+prefixWeight p k*e k := by
  have he i : InnerSelector.weight p i*e i=
      (if i<k then InnerSelector.weight p i*e i else 0)+(if i=k then prefixWeight p k*e k else 0) := by
    by_cases hi : i<k
    · simp [hi,ne_of_lt hi]
    · by_cases hi' : i=k
      · subst i; simp [InnerSelector.weight,prefixWeight,hk]
      · have hki : k < i := lt_of_le_of_ne (le_of_not_gt hi) (Ne.symm hi')
        have hp : (∏ j : Fin m,if j < i then p j else 1)=0 :=
          Finset.prod_eq_zero (Finset.mem_univ k) (by simp [hki,hk])
        simp [InnerSelector.weight,hp,hi,hi']
  rw [Finset.sum_congr rfl (fun i (_ : i ∈ Finset.univ) => he i)]
  simp only [Finset.sum_add_distrib,Finset.sum_ite_eq',Finset.mem_univ,if_true]

def coreObjective (mask : Mask m) (A : Y →L[ℝ] Y) (θ : Leaf.Marks Y E m) (Z : Leaf.Space Y E m) : ℝ :=
  LeafNumerical.base m (Leaf.capRadius m) A (numerical Y E m (Inner.absoluteDepth+2) Z)+coreKnownTerm mask θ Z

theorem coreObjective_contDiff (hm : 1≤m) (mask : Mask m) (A : Y →L[ℝ] Y) (θ : Leaf.Marks Y E m) :
    ContDiff ℝ 3 (coreObjective mask A θ) := by
  have he : coreObjective mask A θ = fun Z =>
      Leaf.objective A θ.1 θ.2.1 θ.2.2 Z-Leaf.knownTerm θ.1 θ.2.1 θ.2.2 Z+coreKnownTerm mask θ Z := by
    funext Z
    rw [Leaf.objective_decomposition]
    unfold coreObjective Leaf.knownTerm
    ring
  have hcore : ContDiff ℝ 3 (fun Z : Leaf.Space Y E m => coreKnownTerm mask θ Z) := by
    have hc : (fun Z : Leaf.Space Y E m => coreKnownTerm mask θ Z) =
        coreKnownJoint mask ∘ (fun Z => (θ,Z)) := rfl
    rw [hc]
    exact (coreKnownJoint_contDiff (Y := Y) (E := E) mask).comp
      (contDiff_const.prodMk contDiff_id)
  rw [he]
  exact ((Leaf.objective_contDiff hm A θ.1 θ.2.1 θ.2.2).sub
    (Leaf.knownTerm_contDiff θ.1 θ.2.1 θ.2.2)).add hcore

theorem leaf_eq_core_of_port_zero (mask : Mask m) (A : Y →L[ℝ] Y) (θ : Leaf.Marks Y E m)
    (Z : Leaf.Space Y E m) (hg : mask.readout=true) (hp : Inner.ports θ.2.2 Z mask.current=0) :
    Leaf.objective A θ.1 θ.2.1 θ.2.2 Z=coreObjective mask A θ Z := by
  rw [Leaf.objective_decomposition]
  unfold Inner.residual Inner.forcingSum
  rw [InnerSelector.select_eq_weighted_sum]
  rw [weighted_prefix _ _ mask.current hp]
  simp only [coreObjective,coreKnownTerm,currentPayload,hg,if_true]
  ring

theorem leaf_core_near (mask : Mask m) (A : Y →L[ℝ] Y) (θ : Leaf.Marks Y E m)
    (Z : Leaf.Space Y E m) (hg : mask.readout=true)
    (hp : (fun W => Inner.ports θ.2.2 W mask.current) =ᶠ[𝓝 Z] fun _ => 0) :
    Leaf.objective A θ.1 θ.2.1 θ.2.2 =ᶠ[𝓝 Z] coreObjective mask A θ := by
  filter_upwards [hp] with W hW
  exact leaf_eq_core_of_port_zero mask A θ W hg hW

theorem ports_view_before (mask : Mask m) (θ : Leaf.Marks Y E m)
    (hv : ∀ i,i<mask.current → mask.memory i=true) (Z : Leaf.Space Y E m)
    {i : Fin m} (hi : i<mask.current) : Inner.ports (view mask θ).2.2 Z i=Inner.ports θ.2.2 Z i := by
  simp [Inner.ports,view,hv i hi]

theorem prefixWeight_view (mask : Mask m) (θ : Leaf.Marks Y E m)
    (hv : ∀ i,i<mask.current → mask.memory i=true) (Z : Leaf.Space Y E m)
    (k : Fin m) (hk : k≤mask.current) :
    prefixWeight (Inner.ports (view mask θ).2.2 Z) k=prefixWeight (Inner.ports θ.2.2 Z) k := by
  apply Finset.prod_congr rfl
  intro i _
  by_cases hi : i<k
  · simp only [if_pos hi,ports_view_before mask θ hv Z (hi.trans_le hk)]
  · simp only [if_neg hi]

theorem weight_view_before (mask : Mask m) (θ : Leaf.Marks Y E m)
    (hv : ∀ i,i<mask.current → mask.memory i=true) (Z : Leaf.Space Y E m)
    {i : Fin m} (hi : i<mask.current) :
    InnerSelector.weight (Inner.ports (view mask θ).2.2 Z) i=InnerSelector.weight (Inner.ports θ.2.2 Z) i := by
  change (1-Inner.ports (view mask θ).2.2 Z i)*prefixWeight (Inner.ports (view mask θ).2.2 Z) i=_
  rw [ports_view_before mask θ hv Z hi,prefixWeight_view mask θ hv Z i hi.le]
  rfl

theorem payload_view_before (mask : Mask m) (θ : Leaf.Marks Y E m)
    (hv : ∀ i,i<mask.current → mask.memory i=true) (Z : Leaf.Space Y E m)
    {i : Fin m} (hi : i<mask.current) :
    Inner.payload (view mask θ).1 (view mask θ).2.1 (view mask θ).2.2 Z i=Inner.payload θ.1 θ.2.1 θ.2.2 Z i := by
  simp [Inner.payload,view,hi,hi.le,hv i hi]

theorem currentPayload_view (mask : Mask m) (θ : Leaf.Marks Y E m)
    (hv : mask.readout=true → mask.memory mask.current=true) (Z : Leaf.Space Y E m) :
    currentPayload mask (view mask θ) Z=currentPayload mask θ Z := by
  cases hg : mask.readout with
  | false => simp [currentPayload,view,hg]
  | true => simp [currentPayload,Inner.payload,view,hg,hv hg]

theorem zero_block_public (U : EuclideanRegisters.Registers E (Inner.absoluteDepth+2)) :
    Inner.block (0 : Fin (Inner.absoluteDepth+2) → E) U=
      LatchChain.publicQuadratic (Inner.absoluteDepth+1) (Inner.radius Inner.absoluteDepth) U := by
  apply MemoryMissJets.self_eq_public_of_zero_gates
  · exact fun j => (Inner.radius_pos _ j).ne'
  · intro j
    simp [LatchChain.u,LatchActivation.readout,Profiles.chi_zero (by norm_num : (0:ℝ)≤1/4)]

theorem selfSum_near_view (mask : Mask m) (θ : Leaf.Marks Y E m) (Z : Leaf.Space Y E m)
    (hmiss : ∀ i,mask.memory i=false → ∀ j,
      |LatchChain.u (Inner.radius Inner.absoluteDepth j) (θ.2.2 i j)
        (tasks Y E m (Inner.absoluteDepth+2) Z i j)|≤1/8) :
    Inner.selfSum θ.2.2 =ᶠ[𝓝 Z] Inner.selfSum (view mask θ).2.2 := by
  have hb (i : Fin m) :
      (fun W : Leaf.Space Y E m => Inner.block (θ.2.2 i) (tasks Y E m (Inner.absoluteDepth+2) W i)) =ᶠ[𝓝 Z]
      fun W => Inner.block ((view mask θ).2.2 i) (tasks Y E m (Inner.absoluteDepth+2) W i) := by
    cases hi : mask.memory i with
    | true => simp only [view,hi,if_true]; exact Filter.Eventually.of_forall (fun _ => rfl)
    | false =>
      have hn := MemoryMissJets.self_near_public (Inner.absoluteDepth+1)
        (Inner.taskProjection (Y := Y) (E := E) m Inner.absoluteDepth i) (θ.2.2 i)
        (Inner.radius Inner.absoluteDepth) (fun j => (Inner.radius_pos _ j).ne') Z (hmiss i hi)
      filter_upwards [hn] with W hW
      simp only [view,hi,Bool.false_eq_true,if_false]
      exact hW.trans (zero_block_public _).symm
  filter_upwards [Filter.eventually_all.mpr hb] with W hW
  exact Finset.sum_congr rfl (fun i _ => hW i)

theorem core_near_objective (mask : Mask m) (A : Y →L[ℝ] Y) (θ : Leaf.Marks Y E m)
    (Z : Leaf.Space Y E m) (hpast : ∀ i,i<mask.current → mask.memory i=true)
    (hcur : mask.readout=true → mask.memory mask.current=true)
    (hmiss : ∀ i,mask.memory i=false → ∀ j,
      |LatchChain.u (Inner.radius Inner.absoluteDepth j) (θ.2.2 i j)
        (tasks Y E m (Inner.absoluteDepth+2) Z i j)|≤1/8) :
    coreObjective mask A θ =ᶠ[𝓝 Z] objective mask A θ := by
  filter_upwards [selfSum_near_view mask θ Z hmiss] with W hW
  have hsum : (∑ i,if i<mask.current then InnerSelector.weight (Inner.ports (view mask θ).2.2 W) i *
      Inner.payload (view mask θ).1 (view mask θ).2.1 (view mask θ).2.2 W i else 0)=
    ∑ i,if i<mask.current then InnerSelector.weight (Inner.ports θ.2.2 W) i*Inner.payload θ.1 θ.2.1 θ.2.2 W i else 0 := by
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : i<mask.current
    · simp only [if_pos hi,weight_view_before mask θ hpast W hi,payload_view_before mask θ hpast W hi]
    · simp only [if_neg hi]
  simp only [coreObjective,objective,knownTerm,coreKnownTerm,hsum,
    prefixWeight_view mask θ hpast W mask.current le_rfl,currentPayload_view mask θ hcur W,hW]

theorem full_leaf_richJet_eq (hm : 1≤m) (mask : Mask m) (A : Y →L[ℝ] Y) (θ : Leaf.Marks Y E m)
    (Z : Leaf.Space Y E m) (hpast : ∀ i,i<mask.current → mask.memory i=true)
    (hcur : mask.readout=true → mask.memory mask.current=true)
    (hport : (fun W => Inner.ports θ.2.2 W mask.current) =ᶠ[𝓝 Z] fun _ => 0)
    (hmiss : ∀ i,mask.memory i=false → ∀ j,
      |LatchChain.u (Inner.radius Inner.absoluteDepth j) (θ.2.2 i j)
        (tasks Y E m (Inner.absoluteDepth+2) Z i j)|≤1/8)
    (hgate : mask.readout=false →
      InverseGate.gateArg (θ.2.1 mask.current) (numerical Y E m (Inner.absoluteDepth+2) Z)≤1/4) :
    richJet (Leaf.objective A θ.1 θ.2.1 θ.2.2) Z=richJet (objective mask A θ) Z := by
  let full : Mask m := { mask with readout := true }
  have hfirst := richJet_congr_of_eventuallyEq (leaf_core_near full A θ Z rfl hport)
  have hlast := richJet_congr_of_eventuallyEq (core_near_objective mask A θ Z hpast hcur hmiss)
  apply hfirst.trans
  apply Eq.trans _ hlast
  cases hg : mask.readout with
  | true =>
    have he : full=mask := by
      cases mask
      simp_all only [full]
    rw [he]
  | false =>
    have he : coreObjective full A θ = fun W => coreObjective mask A θ W -
        (prefixWeight (Inner.ports θ.2.2 W) mask.current * Inner.input (θ.2.2 mask.current)
          (tasks Y E m (Inner.absoluteDepth+2) W mask.current)) *
          InverseGate.gate (θ.2.1 mask.current) (numerical Y E m (Inner.absoluteDepth+2) W) := by
      funext W
      simp only [coreObjective,coreKnownTerm,currentPayload,full,hg,Bool.false_eq_true,if_false,if_true,Inner.payload]
      ring
    rw [he]
    apply NumericalGateJets.remove_sub_gated_term _ _ _ _
      ((coreObjective_contDiff hm mask A θ).of_le (by decide)) _ Z (hgate hg)
    have hp : ContDiff ℝ 2 (fun W : Leaf.Space Y E m => prefixWeight (Inner.ports θ.2.2 W) mask.current) := by
      apply contDiff_prod
      intro i _
      by_cases hi : i<mask.current
      · simpa [hi] using (Inner.ports_contDiff θ.2.2 i).of_le (by decide : (2:WithTop ℕ∞)≤3)
      · simp only [if_neg hi]; exact contDiff_const
    exact hp.mul (((Inner.input_contDiff (θ.2.2 mask.current)).comp
      (Inner.taskProjection (Y := Y) (E := E) m Inner.absoluteDepth mask.current).contDiff).of_le (by decide))

end GradientHessian.CensoredLeaf
