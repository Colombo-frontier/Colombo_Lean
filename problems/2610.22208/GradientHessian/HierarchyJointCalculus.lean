import GradientHessian.HierarchyParameters

/-! Joint C3 dependence of the literal hierarchy on its complete marked
coefficients and physical point, before the measurable readout assembly. -/

noncomputable section
namespace GradientHessian.HierarchyParameters
universe u
open HigherHierarchy InnerCoordinates

section Localized
variable {F E : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem localized_joint_contDiff {R w : ℝ} (hR : 0 < R) (hw : 0 < w)
    {c z : F → E} (hc : ContDiff ℝ 3 c) (hz : ContDiff ℝ 3 z) :
    ContDiff ℝ 3 (fun x => Localized.potential R w (c x) (z x)) ∧
    ContDiff ℝ 3 (fun x => Localized.incoming R w (c x) (z x)) ∧
    ContDiff ℝ 3 (fun x => Localized.port w (c x) (z x)) := by
  have hs := (hz.sub hc).norm_sq ℝ
  have hcut : ContDiff ℝ 3 (fun x => Localized.cutoff w (c x) (z x)) :=
    contDiff_const.sub (Profiles.contDiff_step.comp ((hs.sub contDiff_const).div_const _))
  have hwell : ContDiff ℝ 3 (fun x => Localized.well R w (c x) (z x)) :=
    (((Localized.publicPotential_contDiff hR 3).comp hc).sub contDiff_const).add (contDiff_const.mul hs)
  have hP := (Localized.publicPotential_contDiff hR 3).comp hz
  have hV : ContDiff ℝ 3 (fun x => Localized.potential R w (c x) (z x)) :=
    hP.add (hcut.mul (hwell.sub hP))
  have hG : ContDiff ℝ 3 (fun x => Localized.drive w (c x) (z x)) := by
    apply contDiff_const.mul
    apply ContDiff.sqrt (contDiff_const.add hs)
    intro x
    nlinarith [sq_nonneg ‖z x-c x‖]
  exact ⟨hV,(hV.sub hG).add contDiff_const,
    contDiff_const.sub (Profiles.contDiff_step.comp ((hs.sub contDiff_const).div_const _))⟩
end Localized

variable {Y E : Type u} {H : ℕ → Type u} {m : ℕ}
variable [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [∀ t, NormedAddCommGroup (H t)] [∀ t, InnerProductSpace ℝ (H t)]

theorem first_scalarJoint_contDiff (K : ℝ) :
    ContDiff ℝ 3 (scalarJoint (Y := Y) (E := E) (H := H) (m := m) K 0) := by
  let N := numerical (Leaf.Space Y E (m+1)) E 8 (FirstHeight.depth (m+1)+2)
  have hZ : ContDiff ℝ 3 (fun p : Parameters Y E H m 0 × Space Y E H m 0 => p.2) := contDiff_snd
  have hN : ContDiff ℝ 3 (fun p : Parameters Y E H m 0 × Space Y E H m 0 => N p.2) := N.contDiff.comp hZ
  have hQ := (Leaf.publicQuadratic_contDiff (m+1)).comp hN
  have hv (i : Fin 8) (j : Fin (FirstHeight.depth (m+1)+2)) :
      ContDiff ℝ 3 (fun p : Parameters Y E H m 0 × Space Y E H m 0 => p.1.2 i j) := by fun_prop
  have hp (i : Fin 8) := JointMarkedCalculus.ports_contDiff hv hZ i
  have hchild (i : Fin 8) : ContDiff ℝ 3 (fun p : Parameters Y E H m 0 × Space Y E H m 0 =>
      Leaf.objective (p.1.1 i).1 (p.1.1 i).2.1 (p.1.1 i).2.2.1 (p.1.1 i).2.2.2 (N p.2)) :=
    JointMarkedCalculus.objective_contDiff (by omega) (by fun_prop) (fun _ => by fun_prop)
      (fun _ => by fun_prop) (fun _ _ => by fun_prop) hN
  have hport (i : Fin 8) : ContDiff ℝ 3 (fun p : Parameters Y E H m 0 × Space Y E H m 0 =>
      Leaf.outgoing (p.1.1 i).2.2.2 (N p.2)) :=
    JointMarkedCalculus.ports_contDiff (fun _ _ => by fun_prop) hN (Fin.last m)
  have hB (i : Fin 8) : ContDiff ℝ 3 (fun p : Parameters Y E H m 0 × Space Y E H m 0 =>
      Inner.input (p.1.2 i) (tasks (Leaf.Space Y E (m+1)) E 8 (FirstHeight.depth (m+1)+2) p.2 i)) :=
    JointMarkedCalculus.incoming_contDiff 1 (hv i 0) (JointMarkedCalculus.coordinate_contDiff hZ i 0)
  have he (i : Fin 8) : ContDiff ℝ 3 (fun p : Parameters Y E H m 0 × Space Y E H m 0 =>
      FirstHeight.payload (Leaf.publicQuadratic (m+1)) (FirstHeight.children (decode 0 p.1))
        (FirstHeight.childPorts (decode 0 p.1)) (FirstHeight.spacing m) (decode 0 p.1).outerDirections p.2 i) :=
    (((hchild i).sub hQ).sub contDiff_const).sub ((hB i).mul (hport i))
  have hself := JointMarkedCalculus.selfSum_contDiff hv hZ
  exact (hQ.add (FirstHeightSelector.select_contDiff 8 _ _ _ hp he contDiff_const)).add hself

theorem outgoingJoint_contDiff {K : ℝ} (hK : 0 < K) (t : ℕ) :
    ContDiff ℝ 3 (outgoingJoint (Y := Y) (E := E) (H := H) (m := m) K t) := by
  cases t with
  | zero => exact JointMarkedCalculus.ports_contDiff (fun _ _ => by fun_prop) contDiff_snd (Fin.last 7)
  | succ t =>
    exact (localized_joint_contDiff (radius_pos m hK t) (width_pos m t)
      (contDiff_const.smul (by fun_prop : ContDiff ℝ 3
        (fun p : Parameters Y E H m (t+1) × Space Y E H m (t+1) => p.1.2 (Fin.last 7))))
      ((parentAt (Space Y E H m t) (H t) (Fin.last 7)).contDiff.comp contDiff_snd)).2.2

theorem scalarJoint_contDiff {K : ℝ} (hK : 0 < K) : ∀ t,
    ContDiff ℝ 3 (scalarJoint (Y := Y) (E := E) (H := H) (m := m) K t) := by
  intro t
  induction t with
  | zero => exact first_scalarJoint_contDiff K
  | succ t ih =>
    let F := Parameters Y E H m (t+1) × Space Y E H m (t+1)
    have hchildMap (i : Fin 8) : ContDiff ℝ 3
        (fun p : F => (p.1.1 i, lower (Space Y E H m t) (H t) p.2)) :=
      (by fun_prop : ContDiff ℝ 3 (fun p : F => p.1.1 i)).prodMk
        ((lower (Space Y E H m t) (H t)).contDiff.comp contDiff_snd)
    have hc (i : Fin 8) := ih.comp (hchildMap i)
    have ho (i : Fin 8) := (outgoingJoint_contDiff hK t).comp (hchildMap i)
    have hQ : ContDiff ℝ 3 (fun p : F => baseline K t (lower (Space Y E H m t) (H t) p.2)) :=
      (baseline_contDiff hK t).comp ((lower (Space Y E H m t) (H t)).contDiff.comp contDiff_snd)
    have hl (i : Fin 8) := localized_joint_contDiff (radius_pos m hK t) (width_pos m t)
      ((contDiff_const : ContDiff ℝ 3 (fun _ : F => radius m K t)).smul
        (by fun_prop : ContDiff ℝ 3 (fun p : F => p.1.2 i)))
      ((parentAt (Space Y E H m t) (H t) i).contDiff.comp contDiff_snd)
    have he (i : Fin 8) : ContDiff ℝ 3 (fun p : F =>
        nodePayload (baseline K t) (fun j => scalar K t (decode t (p.1.1 j)))
          (fun j => outgoing K t (decode t (p.1.1 j))) (spacing m K t) (radius m K t) (width m t)
          (centers K (decode (t+1) p.1)) p.2 i) :=
      (((hc i).sub hQ).sub contDiff_const).sub ((hl i).2.1.mul (ho i))
    exact (hQ.add (FirstHeightSelector.select_contDiff 8 _ _ _ (fun i => (hl i).2.2) he contDiff_const)).add
      (ContDiff.sum (fun i _ => (hl i).1))

end GradientHessian.HierarchyParameters
