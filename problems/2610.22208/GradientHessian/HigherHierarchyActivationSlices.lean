import GradientHessian.HigherHierarchyLocalization

/-! Exact lower and current-parent slices of the localized node. The
current incoming coefficient and completion gate use the same vector. -/

noncomputable section
namespace GradientHessian.HigherHierarchy

theorem select_eq_payload_first_zero (n : ℕ) (p e : Fin n → ℝ) (T : ℝ) (i : Fin n)
    (hprev : ∀ j, j < i → p j = 1) (hi : p i = 0) :
    FirstHeightSelector.select n p e T = e i := by
  have hu : Function.update p i 0 = p := by
    funext j
    by_cases hj : j = i
    · subst j; simp [hi]
    · simp [Function.update_of_ne hj]
  simpa [hu] using FirstHeightSelector.select_update_first n p e T i hprev 0

theorem select_update_payload_of_one (n : ℕ) (p e : Fin n → ℝ) (T : ℝ) (i : Fin n)
    (hi : p i = 1) (a : ℝ) :
    FirstHeightSelector.select n p (Function.update e i a) T = FirstHeightSelector.select n p e T := by
  simp only [FirstHeightSelector.select_eq_inner, InnerSelector.select_eq_weighted_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : j = i
  · subst j; simp [InnerSelector.weight, hi]
  · rw [Function.update_of_ne hj]

variable {F E : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def nodeDriven (Q : F → ℝ) (child childPort : Fin 8 → F → ℝ) (S R w : ℝ)
    (c : Fin 8 → E) (l : ℝ) (Z : Layer F E) : ℝ :=
  nodeScalar Q child childPort S R w c Z - l*nodePorts w c Z (Fin.last 7)

def nodeTail (Q : F → ℝ) (child childPort : Fin 8 → F → ℝ) (S R w : ℝ)
    (c : Fin 8 → E) (Z : Layer F E) (i : Fin 8) : ℝ :=
  FirstHeightSelector.select 8 (Function.update (nodePorts w c Z) i 1)
    (nodePayload Q child childPort S R w c Z) (-8*S)

def parentExpression (R w : ℝ) (c : E) (D o T l : ℝ) (x : E) : ℝ :=
  Localized.potential R w c x + (1-Localized.port w c x)*(D-Localized.incoming R w c x*o) +
    Localized.port w c x*T-l*Localized.port w c x

theorem nodePorts_replaceParent (w : ℝ) (c : Fin 8 → E) (Z : Layer F E) (i : Fin 8) (x : E) :
    nodePorts w c (replaceParent Z i x) = Function.update (nodePorts w c Z) i (Localized.port w (c i) x) := by
  funext j
  by_cases hj : j = i
  · subst j; simp [nodePorts]
  · simp [nodePorts, hj, Function.update_of_ne hj]

theorem nodePayload_replaceParent (Q : F → ℝ) (child childPort : Fin 8 → F → ℝ) (S R w : ℝ)
    (c : Fin 8 → E) (Z : Layer F E) (i : Fin 8) (x : E) :
    nodePayload Q child childPort S R w c (replaceParent Z i x) =
      Function.update (nodePayload Q child childPort S R w c Z) i
        (child i (lower F E Z)-Q (lower F E Z)-(i.val:ℝ)*S-Localized.incoming R w (c i) x*childPort i (lower F E Z)) := by
  funext j
  by_cases hj : j = i
  · subst j; simp [nodePayload, nodeIncoming]
  · simp [nodePayload, nodeIncoming, hj, Function.update_of_ne hj]

theorem nodeSelf_replaceParent (R w : ℝ) (c : Fin 8 → E) (Z : Layer F E) (i : Fin 8) (x : E) :
    nodeSelf R w c (replaceParent Z i x) = Localized.potential R w (c i) x +
      ∑ j ∈ Finset.univ.erase i, Localized.potential R w (c j) (parent F E Z j) := by
  unfold nodeSelf
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  simp only [parent_replaceParent, if_pos rfl]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [if_neg (Finset.ne_of_mem_erase hj)]

theorem nodeSelected_replaceParent (Q : F → ℝ) (child childPort : Fin 8 → F → ℝ) (S R w : ℝ)
    (c : Fin 8 → E) (Z : Layer F E) (i : Fin 8)
    (hprev : ∀ j, j < i → nodePorts w c Z j = 1) (x : E) :
    nodeSelected Q child childPort S R w c (replaceParent Z i x) =
      (1-Localized.port w (c i) x) *
        (child i (lower F E Z)-Q (lower F E Z)-(i.val:ℝ)*S-Localized.incoming R w (c i) x*childPort i (lower F E Z)) +
      Localized.port w (c i) x * nodeTail Q child childPort S R w c Z i := by
  rw [nodeSelected, nodePorts_replaceParent, nodePayload_replaceParent,
    FirstHeightSelector.select_update_first 8 _ _ _ i hprev]
  rw [select_update_payload_of_one 8 _ _ _ i (by simp)]
  simp only [Function.update_self, nodeTail]

theorem nodeDriven_parent_slice (Q : F → ℝ) (child childPort : Fin 8 → F → ℝ) (S R w : ℝ)
    (c : Fin 8 → E) (l : ℝ) (Z : Layer F E) (i : Fin 8)
    (hprev : ∀ j, j < i → nodePorts w c Z j = 1) :
    ∃ C : ℝ, ∀ x, nodeDriven Q child childPort S R w c l (replaceParent Z i x) =
      parentExpression R w (c i) (child i (lower F E Z)-Q (lower F E Z)-(i.val:ℝ)*S)
        (childPort i (lower F E Z)) (nodeTail Q child childPort S R w c Z i)
        (if i = Fin.last 7 then l else 0) x + C := by
  let C := Q (lower F E Z) + (∑ j ∈ Finset.univ.erase i, Localized.potential R w (c j) (parent F E Z j)) -
    (if i = Fin.last 7 then 0 else l*nodePorts w c Z (Fin.last 7))
  refine ⟨C, fun x => ?_⟩
  simp only [nodeDriven, nodeScalar, lower_replaceParent, nodeSelected_replaceParent Q child childPort S R w c Z i hprev,
    nodeSelf_replaceParent, nodePorts_replaceParent]
  dsimp only [parentExpression, C]
  by_cases hi : i = Fin.last 7
  · subst i; simp only [Function.update_self, ite_true]; ring
  · simp only [hi, ite_false, Function.update_of_ne (Ne.symm hi)]; ring

theorem nodeDriven_lower_first_zero (Q : F → ℝ) (child childPort : Fin 8 → F → ℝ) (S R w : ℝ)
    (c : Fin 8 → E) (l : ℝ) (Z : Layer F E) (i : Fin 8)
    (hprev : ∀ j, j < i → nodePorts w c Z j = 1) (hi : nodePorts w c Z i = 0) (x : F) :
    nodeDriven Q child childPort S R w c l (replaceLower Z x) =
      (child i x-nodeIncoming R w c Z i*childPort i x) +
      (-(i.val:ℝ)*S+nodeSelf R w c Z-l*nodePorts w c Z (Fin.last 7)) := by
  simp only [nodeDriven, nodeScalar, nodeSelected, nodePorts_replaceLower, lower_replaceLower]
  rw [select_eq_payload_first_zero 8 _ _ _ i hprev hi]
  simp only [nodePayload, nodeIncoming, nodeSelf, lower_replaceLower, parent_replaceLower]
  ring

theorem nodeDriven_contDiff (Q : F → ℝ) (child childPort : Fin 8 → F → ℝ) (S : ℝ)
    {R w : ℝ} (hR : 0 < R) (hw : 0 < w) (c : Fin 8 → E) (l : ℝ)
    (hQ : ContDiff ℝ 3 Q) (hc : ∀ i, ContDiff ℝ 3 (child i)) (ho : ∀ i, ContDiff ℝ 3 (childPort i)) :
    ContDiff ℝ 3 (nodeDriven Q child childPort S R w c l) :=
  (nodeScalar_contDiff Q child childPort S hR hw c hQ hc ho).sub
    (contDiff_const.mul (nodePorts_contDiff hR hw c (Fin.last 7)))

end GradientHessian.HigherHierarchy
