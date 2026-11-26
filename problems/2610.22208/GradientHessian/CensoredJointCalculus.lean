import GradientHessian.CensoredOracleDecomposition

/-! Joint C3 regularity in the finite coefficient product and physical point.
Partial physical derivatives therefore give Borel exact oracle decoders. -/

noncomputable section
namespace GradientHessian.CensoredOracle
universe u
open HigherHierarchy CensoredHierarchy HierarchyParameters InnerCoordinates

section Finite
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem prefix_joint_contDiff (k : Fin b) (port : Fin b → F → ℝ)
    (hp : ∀ i,ContDiff ℝ 3 (port i)) :
    ContDiff ℝ 3 (fun x => CensoredLeaf.prefixWeight (fun i => port i x) k) := by
  apply contDiff_prod
  intro i _
  by_cases hi : i<k
  · simpa only [if_pos hi] using hp i
  · simp only [if_neg hi]; exact contDiff_const

theorem frontier_joint_contDiff (k : Fin b) (Q : F → ℝ) (S : ℝ)
    (child port self incoming parent : Fin b → F → ℝ) (active : F → ℝ)
    (hQ : ContDiff ℝ 3 Q) (hc : ∀ i,ContDiff ℝ 3 (child i))
    (ho : ∀ i,ContDiff ℝ 3 (port i)) (hs : ∀ i,ContDiff ℝ 3 (self i))
    (hi : ∀ i,ContDiff ℝ 3 (incoming i)) (hp : ∀ i,ContDiff ℝ 3 (parent i))
    (ha : ContDiff ℝ 3 active) :
    ContDiff ℝ 3 (FrontierOracleScalar.scalar k Q S child port self incoming parent active) := by
  have hw i : ContDiff ℝ 3 (fun x => InnerSelector.weight (fun j => parent j x) i) :=
    (contDiff_const.sub (hp i)).mul (prefix_joint_contDiff i parent hp)
  exact ((hQ.add (ContDiff.sum (fun i _ => by
    by_cases hh : i<k
    · simpa only [if_pos hh] using (hw i).mul ((((hc i).sub hQ).sub contDiff_const).sub ((hi i).mul (ho i)))
    · simp only [if_neg hh]; exact contDiff_const))).add
      ((prefix_joint_contDiff k parent hp).mul ((ha.sub hQ).sub contDiff_const))).add
      (ContDiff.sum (fun i _ => hs i))
end Finite

variable {Y E : Type u} {H : ℕ → Type u} {m : ℕ}
variable [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [∀ h,NormedAddCommGroup (H h)] [∀ h,InnerProductSpace ℝ (H h)]

def knownJoint (K : ℝ) (t : ℕ) (p : Plan m t) (q : Parameters Y E H m t × Space Y E H m t) : ℝ :=
  known K t p (decode t q.1) q.2
def weightJoint (K : ℝ) (t : ℕ) (p : Plan m t) (q : Parameters Y E H m t × Space Y E H m t) : ℝ :=
  weight K t p (decode t q.1) q.2
def objectiveJoint (K : ℝ) (t : ℕ) (p : Plan m t) (q : Parameters Y E H m t × Space Y E H m t) : ℝ :=
  CensoredHierarchy.scalar K t p (decode t q.1) q.2

theorem first_joint_contDiff (K : ℝ) (p : Plan m 0) :
    ContDiff ℝ 3 (knownJoint (Y := Y) (E := E) (H := H) K 0 p) ∧
    ContDiff ℝ 3 (weightJoint (Y := Y) (E := E) (H := H) K 0 p) := by
  let F := Parameters Y E H m 0 × Space Y E H m 0
  let N := CensoredFirstHeight.lower (Y := Y) (E := E) (m := m)
  have hZ : ContDiff ℝ 3 (Prod.snd : F → Space Y E H m 0) := contDiff_snd
  have hN := N.contDiff.comp hZ
  have hQ := (Leaf.publicQuadratic_contDiff (m+1)).comp hN
  have hv (i : Fin 8) (j : Fin (FirstHeight.depth (m+1)+2)) :
      ContDiff ℝ 3 (fun q : F => q.1.2 i j) := by fun_prop
  have hp i := JointMarkedCalculus.ports_contDiff hv hZ i
  have hc i : ContDiff ℝ 3 (fun q : F => FirstHeight.children (decode 0 q.1) i (N q.2)) :=
    JointMarkedCalculus.objective_contDiff (by omega) (by fun_prop) (fun _ => by fun_prop)
      (fun _ => by fun_prop) (fun _ _ => by fun_prop) hN
  have ho i : ContDiff ℝ 3 (fun q : F => FirstHeight.childPorts (decode 0 q.1) i (N q.2)) :=
    JointMarkedCalculus.ports_contDiff (fun _ _ => by fun_prop) hN (Fin.last m)
  have hi i := JointMarkedCalculus.incoming_contDiff 1 (hv i 0)
    (JointMarkedCalculus.coordinate_contDiff hZ i 0)
  have hs i : ContDiff ℝ 3 (fun q : F => CensoredFirstHeight.maskedSelf (decode 0 q.1) p.2.1 i q.2) := by
    apply JointMarkedCalculus.self_contDiff (FirstHeight.depth (m+1)+1) _ contDiff_const
    · intro j
      cases he : p.2.1 i with
      | true => simpa only [he,if_true] using hv i j
      | false => simp only [he,Bool.false_eq_true,if_false]; exact contDiff_const
    · exact (CensoredFirstHeight.blockMap (Y := Y) (E := E) (m := m) i).contDiff.comp hZ
  have ha : ContDiff ℝ 3 (fun q : F => CensoredLeaf.knownTerm p.2.2 (q.1.1 p.1).2 (N q.2)) := by
    have he : (fun q : F => CensoredLeaf.knownTerm p.2.2 (q.1.1 p.1).2 (N q.2))=
        CensoredLeaf.knownJoint p.2.2 ∘ (fun q : F => ((q.1.1 p.1).2,N q.2)) := rfl
    rw [he]
    exact (CensoredLeaf.knownJoint_contDiff p.2.2).comp
      ((by fun_prop : ContDiff ℝ 3 (fun q : F => (q.1.1 p.1).2)).prodMk hN)
  exact ⟨frontier_joint_contDiff p.1 _ _ _ _ _ _ _ _ hQ hc ho hs hi hp ha,
    prefix_joint_contDiff p.1 _ hp⟩

theorem joint_contDiff {K : ℝ} (hK : 0<K) : ∀ t (p : Plan m t),
    ContDiff ℝ 3 (knownJoint (Y := Y) (E := E) (H := H) K t p) ∧
    ContDiff ℝ 3 (weightJoint (Y := Y) (E := E) (H := H) K t p) := by
  intro t
  induction t with
  | zero => exact first_joint_contDiff K
  | succ t ih =>
    intro p
    let F := Parameters Y E H m (t+1) × Space Y E H m (t+1)
    have hchildMap (i : Fin 8) : ContDiff ℝ 3
        (fun q : F => (q.1.1 i,lower (Space Y E H m t) (H t) q.2)) :=
      (by fun_prop : ContDiff ℝ 3 (fun q : F => q.1.1 i)).prodMk
        ((lower (Space Y E H m t) (H t)).contDiff.comp contDiff_snd)
    have hc i := (HierarchyParameters.scalarJoint_contDiff hK t).comp (hchildMap i)
    have ho i := (outgoingJoint_contDiff hK t).comp (hchildMap i)
    have hQ := (baseline_contDiff hK t).comp ((lower (Space Y E H m t) (H t)).contDiff.comp
      (contDiff_snd : ContDiff ℝ 3 (Prod.snd : F → _)))
    have hl (i : Fin 8) := localized_joint_contDiff (radius_pos m hK t) (width_pos m t)
      ((contDiff_const : ContDiff ℝ 3 (fun _ : F => radius m K t)).smul
        (by fun_prop : ContDiff ℝ 3 (fun q : F => q.1.2 i)))
      ((parentAt (Space Y E H m t) (H t) i).contDiff.comp contDiff_snd)
    have hs i : ContDiff ℝ 3 (fun q : F => CensoredHierarchy.maskedSelf K t (decode (t+1) q.1) p.2.1 i q.2) := by
      cases he : p.2.1 i with
      | true => simpa only [CensoredHierarchy.maskedSelf,he,if_true] using (hl i).1
      | false =>
        simpa only [CensoredHierarchy.maskedSelf,he,Bool.false_eq_true,if_false] using
          (Localized.publicPotential_contDiff (radius_pos m hK t) 3).comp
            ((parentAt (Space Y E H m t) (H t) i).contDiff.comp (contDiff_snd : ContDiff ℝ 3 (Prod.snd : F → _)))
    have ha := (ih p.2.2).1.comp (hchildMap p.1)
    have hw := (ih p.2.2).2.comp (hchildMap p.1)
    exact ⟨frontier_joint_contDiff p.1 _ _ _ _ _ _ _ _ hQ hc ho hs
      (fun i => (hl i).2.1) (fun i => (hl i).2.2) ha,
      (prefix_joint_contDiff p.1 _ (fun i => (hl i).2.2)).mul hw⟩

theorem selectedMatrix_contDiff (t : ℕ) (p : Plan m t) :
    ContDiff ℝ 3 (fun θ : Parameters Y E H m t => selectedMatrix t p (decode t θ)) := by
  induction t with
  | zero => change ContDiff ℝ 3 (fun θ : Parameters Y E H m 0 => (θ.1 p.1).1); fun_prop
  | succ t ih =>
    exact (ih p.2.2).comp
      (by fun_prop : ContDiff ℝ 3 (fun θ : Parameters Y E H m (t+1) => θ.1 p.1))

theorem objectiveJoint_contDiff {K : ℝ} (hK : 0<K) (t : ℕ) (p : Plan m t) :
    ContDiff ℝ 3 (objectiveJoint (Y := Y) (E := E) (H := H) K t p) := by
  have he : objectiveJoint (Y := Y) (E := E) (H := H) K t p = fun q => knownJoint K t p q+weightJoint K t p q*
      LeafNumerical.base (m+1 : ℕ) (Leaf.capRadius (m+1)) (selectedMatrix t p (decode t q.1))
        (numericalMap t q.2) := funext (fun q => scalar_decomposition K t p _ _)
  have hA := (selectedMatrix_contDiff (Y := Y) (E := E) (H := H) t p).comp
    (contDiff_fst : ContDiff ℝ 3 (Prod.fst : Parameters Y E H m t × Space Y E H m t → _))
  have hy := (numericalMap (Y := Y) (E := E) (H := H) (m := m) t).contDiff.comp
    (contDiff_snd : ContDiff ℝ 3 (Prod.snd : Parameters Y E H m t × Space Y E H m t → _))
  have hbase : ContDiff ℝ 3 (fun q : Parameters Y E H m t × Space Y E H m t =>
      LeafNumerical.base (m+1 : ℕ) (Leaf.capRadius (m+1)) (selectedMatrix t p (decode t q.1))
        (numericalMap t q.2)) := by
    simp only [LeafNumerical.base,LeafCorrection.correction,LeafCorrection.quadratic,
      LeafNumerical.deviation,ContinuousLinearMap.sub_apply,ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.id_apply]
    exact (contDiff_const.mul (hy.norm_sq ℝ)).add
      ((contDiff_const.mul ((LeafCutoff.cutoff_contDiff (Leaf.capRadius_pos (by omega))).comp hy)).mul
        (hy.inner ℝ ((hA.clm_apply hy).sub (contDiff_const.smul hy))))
  rw [he]
  exact (joint_contDiff hK t p).1.add ((joint_contDiff hK t p).2.mul hbase)

end GradientHessian.CensoredOracle
