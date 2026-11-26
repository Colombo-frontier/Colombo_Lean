import GradientHessian.HigherHierarchyActivationGradient

/-! Localized node activation from the proved child activation interface.
The recursive theorem subsequently discharges that interface by induction. -/

noncomputable section
namespace GradientHessian.HigherHierarchy

variable {F E : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem node_parent_gradient_le (Q : F → ℝ) (child childPort : Fin 8 → F → ℝ) (S : ℝ)
    {R w : ℝ} (hR : 0 < R) (hw : 0 < w) (c : Fin 8 → E) (l : ℝ)
    (hQ : ContDiff ℝ 3 Q) (hc : ∀ i, ContDiff ℝ 3 (child i)) (ho : ∀ i, ContDiff ℝ 3 (childPort i))
    (Z : Layer F E) (i : Fin 8) (hprev : ∀ j, j < i → nodePorts w c Z j = 1)
    (hg : ‖gradient (nodeDriven Q child childPort S R w c l) Z‖ ≤ 1) :
    ‖gradient (Localized.potential R w (c i)) (parent F E Z i) -
      ((1-nodePorts w c Z i)*childPort i (lower F E Z)) • gradient (Localized.incoming R w (c i)) (parent F E Z i) +
      (nodeTail Q child childPort S R w c Z i-nodePayload Q child childPort S R w c Z i-
        (if i = Fin.last 7 then l else 0)) • gradient (Localized.port w (c i)) (parent F E Z i)‖ ≤ 1 := by
  have hs := (parent_gradient_norm_le (nodeDriven Q child childPort S R w c l) Z i
    ((nodeDriven_contDiff Q child childPort S hR hw c l hQ hc ho).differentiable (by norm_num) Z)).trans hg
  obtain ⟨C,hC⟩ := nodeDriven_parent_slice Q child childPort S R w c l Z i hprev
  rw [funext hC] at hs
  have hd := parentExpression_hasGradientAt hR hw (c i) (parent F E Z i)
    (child i (lower F E Z)-Q (lower F E Z)-(i.val:ℝ)*S) (childPort i (lower F E Z))
    (nodeTail Q child childPort S R w c Z i) (if i = Fin.last 7 then l else 0)
  rw [(LatchChain.add_constant_hasGradientAt hd C).gradient] at hs
  exact hs

theorem node_first_zero_child_gradient (Q : F → ℝ) (child childPort : Fin 8 → F → ℝ) (S : ℝ)
    {R w : ℝ} (hR : 0 < R) (hw : 0 < w) (c : Fin 8 → E) (l : ℝ)
    (hQ : ContDiff ℝ 3 Q) (hc : ∀ i, ContDiff ℝ 3 (child i)) (ho : ∀ i, ContDiff ℝ 3 (childPort i))
    (Z : Layer F E) (i : Fin 8) (hprev : ∀ j, j < i → nodePorts w c Z j = 1)
    (hi : nodePorts w c Z i = 0)
    (hg : ‖gradient (nodeDriven Q child childPort S R w c l) Z‖ ≤ 1) :
    ‖gradient (fun x => child i x-nodeIncoming R w c Z i*childPort i x) (lower F E Z)‖ ≤ 1 := by
  have hs := (lower_gradient_norm_le (nodeDriven Q child childPort S R w c l) Z
    ((nodeDriven_contDiff Q child childPort S hR hw c l hQ hc ho).differentiable (by norm_num) Z)).trans hg
  rw [funext (nodeDriven_lower_first_zero Q child childPort S R w c l Z i hprev hi)] at hs
  have hdiff : ContDiff ℝ 3 (fun x => child i x-nodeIncoming R w c Z i*childPort i x) :=
    (hc i).sub (contDiff_const.mul (ho i))
  have hd := (hdiff.differentiable (by norm_num) (lower F E Z)).hasGradientAt
  rw [(LatchChain.add_constant_hasGradientAt hd _).gradient] at hs
  exact hs

theorem node_first_zero_impossible (Q : F → ℝ) (child childPort : Fin 8 → F → ℝ) (S : ℝ)
    {R w : ℝ} (hw : 0 < w) (hscale : 16*w ≤ R) (c : Fin 8 → E) (hcent : ∀ i, ‖c i‖ = R) (l : ℝ)
    (hQ : ContDiff ℝ 3 Q) (hc : ∀ i, ContDiff ℝ 3 (child i)) (ho : ∀ i, ContDiff ℝ 3 (childPort i))
    (Z : Layer F E) (i : Fin 8)
    (hchild : ∀ d, 0 ≤ d → ∀ x, ‖gradient (fun z => child i z-d*childPort i z) x‖ ≤ 1 → childPort i x = 1)
    (hprev : ∀ j, j < i → nodePorts w c Z j = 1) (hi : nodePorts w c Z i = 0)
    (hg : ‖gradient (nodeDriven Q child childPort S R w c l) Z‖ ≤ 1) : False := by
  have hR : 0 < R := by linarith
  have hcg := node_first_zero_child_gradient Q child childPort S hR hw c l hQ hc ho Z i hprev hi hg
  have hB := (Localized.incoming_bounds hw hscale (c i) (parent F E Z i) (hcent i)).1
  have hop := hchild (nodeIncoming R w c Z i) (le_trans (by positivity) hB) (lower F E Z) hcg
  have hs := node_parent_gradient_le Q child childPort S hR hw c l hQ hc ho Z i hprev hg
  have hp0 := localized_port_gradient_zero w (c i) (parent F E Z i) hi
  rw [hi, hop, hp0] at hs
  simp only [sub_zero, mul_one, one_smul, smul_zero, add_zero] at hs
  rw [← localized_difference_gradient hR hw (c i) (parent F E Z i)] at hs
  have hdone := (Localized.small_gradient_opens_port hw R (c i) (parent F E Z i) hs).2
  change nodePorts w c Z i = 1 at hdone
  linarith

theorem node_first_transition_impossible (Q : F → ℝ) (child childPort : Fin 8 → F → ℝ)
    {A R w : ℝ} (hA : 0 ≤ A) (hw : 0 < w) (hscale : 16*w ≤ R)
    (c : Fin 8 → E) (hcent : ∀ i, ‖c i‖ = R) {l : ℝ} (hl : 0 ≤ l)
    (hQ : ContDiff ℝ 3 Q) (hc : ∀ i, ContDiff ℝ 3 (child i)) (ho : ∀ i, ContDiff ℝ 3 (childPort i))
    (Z : Layer F E) (i : Fin 8) (hprev : ∀ j, j < i → nodePorts w c Z j = 1)
    (hval : ∀ j, -A ≤ child j (lower F E Z)-Q (lower F E Z) ∧ child j (lower F E Z)-Q (lower F E Z) ≤ 0)
    (hop : ∀ j, childPort j (lower F E Z) ∈ Set.Icc (0:ℝ) 1)
    (hi0 : 0 < nodePorts w c Z i) (hi1 : nodePorts w c Z i < 1)
    (hg : ‖gradient (nodeDriven Q child childPort (A+768*R) R w c l) Z‖ ≤ 1) : False := by
  have hR : 0 < R := by linarith
  have he := nodePayload_interval Q child childPort (A := A) (C := 0) hw hscale c hcent Z
    (fun j => by simpa only [sub_zero] using hval j) hop
  have htail := FirstHeightSelector.ordered_tail 8 (nodePorts w c Z)
    (nodePayload Q child childPort (A+768*R) R w c Z) (show 0 ≤ A+768*R by positivity)
    i (nodePorts_bounds w c Z) hprev (fun j => by simpa only [sub_zero] using he j)
  have hζ : nodeTail Q child childPort (A+768*R) R w c Z i-
      nodePayload Q child childPort (A+768*R) R w c Z i-(if i = Fin.last 7 then l else 0) ≤ 0 := by
    change nodeTail Q child childPort (A+768*R) R w c Z i ≤ _ at htail
    split_ifs <;> linarith
  have hτ : (1-nodePorts w c Z i)*childPort i (lower F E Z) ≤ 1 := by
    have hp := nodePorts_bounds w c Z i
    have hh := mul_le_mul (show 1-nodePorts w c Z i ≤ 1 by linarith [hp.1])
      (hop i).2 (hop i).1 zero_le_one
    simpa only [mul_one] using hh
  have hlo : w < ‖parent F E Z i-c i‖ := by
    by_contra hh
    have hp := Localized.port_eq_one_of_norm_le hw (le_of_not_gt hh)
    change nodePorts w c Z i = 1 at hp
    linarith
  have hhi : ‖parent F E Z i-c i‖ < 2*w := by
    by_contra hh
    have hp := Localized.port_eq_zero_of_two_mul_le_norm hw (le_of_not_gt hh)
    change nodePorts w c Z i = 0 at hp
    linarith
  have hs := node_parent_gradient_le Q child childPort (A+768*R) hR hw c l hQ hc ho Z i hprev hg
  exact (not_lt_of_ge hs) (Localized.localized_transition_excludes_small_gradient hw R
    (c i) (parent F E Z i) hlo hhi hτ hζ)

theorem node_activation_at_bounded_lower (Q : F → ℝ) (child childPort : Fin 8 → F → ℝ)
    {A R w : ℝ} (hA : 0 ≤ A) (hw : 0 < w) (hscale : 16*w ≤ R)
    (c : Fin 8 → E) (hcent : ∀ i, ‖c i‖ = R) {l : ℝ} (hl : 0 ≤ l)
    (hQ : ContDiff ℝ 3 Q) (hc : ∀ i, ContDiff ℝ 3 (child i)) (ho : ∀ i, ContDiff ℝ 3 (childPort i))
    (hchild : ∀ i d, 0 ≤ d → ∀ x, ‖gradient (fun z => child i z-d*childPort i z) x‖ ≤ 1 → childPort i x = 1)
    (Z : Layer F E)
    (hval : ∀ j, -A ≤ child j (lower F E Z)-Q (lower F E Z) ∧ child j (lower F E Z)-Q (lower F E Z) ≤ 0)
    (hop : ∀ j, childPort j (lower F E Z) ∈ Set.Icc (0:ℝ) 1)
    (hg : ‖gradient (nodeDriven Q child childPort (A+768*R) R w c l) Z‖ ≤ 1) :
    ∀ i, nodePorts w c Z i = 1 := by
  intro i
  induction i using (measure (fun j : Fin 8 => j.val)).wf.induction with
  | h i ih =>
    have hprev : ∀ j, j < i → nodePorts w c Z j = 1 := fun j hj => ih j hj
    by_cases hi : nodePorts w c Z i = 1
    · exact hi
    · have hp := nodePorts_bounds w c Z i
      by_cases hz : nodePorts w c Z i = 0
      · exact (node_first_zero_impossible Q child childPort _ hw hscale c hcent l
          hQ hc ho Z i (hchild i) hprev hz hg).elim
      · exact (node_first_transition_impossible Q child childPort hA hw hscale c hcent hl
          hQ hc ho Z i hprev hval hop (lt_of_le_of_ne hp.1 (Ne.symm hz))
          (lt_of_le_of_ne hp.2 hi) hg).elim

end GradientHessian.HigherHierarchy
