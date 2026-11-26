import GradientHessian.CensoredOracleDecomposition

/-! A finite coefficient view with explicit erasure of future subtrees,
undisclosed directions and marks, and optionally the selected matrix. -/

noncomputable section
namespace GradientHessian.CensoredOracle
universe u
open Classical HigherHierarchy CensoredHierarchy HierarchyParameters

variable {Y E : Type u} {H : ℕ → Type u} {m : ℕ}
variable [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [∀ h,NormedAddCommGroup (H h)] [∀ h,InnerProductSpace ℝ (H h)]

def view (keepMatrix : Bool) : (t : ℕ) → Plan m t → Parameters Y E H m t → Parameters Y E H m t
  | 0,p,θ =>
      (fun i => if i<p.1 then θ.1 i else if i=p.1 then
        (if keepMatrix then (θ.1 i).1 else 0,CensoredLeaf.view p.2.2 (θ.1 i).2) else 0,
       fun i => if i<p.1 ∨ p.2.1 i=true then θ.2 i else 0)
  | t+1,p,θ =>
      (fun i => if i<p.1 then θ.1 i else if i=p.1 then view keepMatrix t p.2.2 (θ.1 i) else 0,
       fun i => if i<p.1 ∨ p.2.1 i=true then θ.2 i else 0)

def SameKnown : (t : ℕ) → Plan m t → Parameters Y E H m t → Parameters Y E H m t → Prop
  | 0,p,θ,η =>
      (∀ i,i<p.1 → θ.1 i=η.1 i) ∧
      (∀ i,i<p.1 ∨ p.2.1 i=true → θ.2 i=η.2 i) ∧
      CensoredLeaf.view p.2.2 (θ.1 p.1).2=CensoredLeaf.view p.2.2 (η.1 p.1).2
  | t+1,p,θ,η =>
      (∀ i,i<p.1 → θ.1 i=η.1 i) ∧
      (∀ i,i<p.1 ∨ p.2.1 i=true → θ.2 i=η.2 i) ∧
      SameKnown t p.2.2 (θ.1 p.1) (η.1 p.1)

omit [InnerProductSpace ℝ E] [∀ h,InnerProductSpace ℝ (H h)] in
theorem sameKnown_view (keepMatrix : Bool) : ∀ t (p : Plan m t) (θ : Parameters Y E H m t),
    SameKnown t p θ (view keepMatrix t p θ) := by
  intro t
  induction t with
  | zero =>
    intro p θ
    refine ⟨?_,?_,?_⟩
    · intro i hi; simp only [view,if_pos hi]
    · intro i hi; simp only [view,if_pos hi]
    · simp only [view,lt_self_iff_false,if_false,if_true,CensoredLeaf.view_idempotent]
  | succ t ih =>
    intro p θ
    refine ⟨?_,?_,?_⟩
    · intro i hi; simp only [view,if_pos hi]
    · intro i hi; simp only [view,if_pos hi]
    · simpa only [view,lt_self_iff_false,if_false,if_true] using ih p.2.2 (θ.1 p.1)

omit [∀ h,InnerProductSpace ℝ (H h)] in
theorem view_continuous (keepMatrix : Bool) : ∀ t (p : Plan m t),
    Continuous (view (Y := Y) (E := E) (H := H) keepMatrix t p) := by
  intro t
  induction t with
  | zero =>
    intro p
    apply Continuous.prodMk
    · apply continuous_pi
      intro i
      simp only [view]
      by_cases hi : i<p.1
      · simp only [if_pos hi]; fun_prop
      · simp only [if_neg hi]
        by_cases he : i=p.1
        · simp only [if_pos he]
          apply Continuous.prodMk
          · split_ifs <;> fun_prop
          · exact (CensoredLeaf.view_contDiff p.2.2).continuous.comp (by fun_prop)
        · simp only [if_neg he]; fun_prop
    · apply continuous_pi
      intro i
      simp only [view]
      split_ifs <;> fun_prop
  | succ t ih =>
    intro p
    apply Continuous.prodMk
    · apply continuous_pi
      intro i
      simp only [view]
      split_ifs
      · fun_prop
      · exact (ih p.2.2).comp (by fun_prop)
      · fun_prop
    · apply continuous_pi
      intro i
      simp only [view]
      split_ifs <;> fun_prop

omit [∀ h,InnerProductSpace ℝ (H h)] in
theorem selectedMatrix_view (keepMatrix : Bool) : ∀ t (p : Plan m t) (θ : Parameters Y E H m t),
    selectedMatrix t p (decode t (view keepMatrix t p θ))=
      if keepMatrix then selectedMatrix t p (decode t θ) else 0 := by
  intro t
  induction t with
  | zero => intro p θ; simp [selectedMatrix,selectedLeaf,leafData,decode,view]
  | succ t ih => intro p θ; simpa [selectedMatrix,selectedLeaf,leafData,decode,view] using ih p.2.2 (θ.1 p.1)

theorem known_eq_of_sameKnown (K : ℝ) : ∀ t (p : Plan m t) (θ η : Parameters Y E H m t),
    SameKnown t p θ η → known K t p (decode t θ)=known K t p (decode t η) := by
  intro t
  induction t with
  | zero =>
    intro p θ η he
    have ha := CensoredLeaf.knownTerm_erasure p.2.2 he.2.2
    simp only [known,decode,ha]
    apply FrontierOracleScalar.scalar_erasure
    · intro i hi
      have h := he.1 i hi
      simp only [FirstHeight.children,congrArg Prod.fst h,congrArg (fun a => a.2.1) h,
        congrArg (fun a => a.2.2.1) h,congrArg (fun a => a.2.2.2) h]
    · intro i hi
      simp only [FirstHeight.childPorts,congrArg (fun a => a.2.2.2) (he.1 i hi)]
    · intro i hi
      simp only [he.2.1 i (Or.inl hi)]
    · intro i hi
      simp only [Inner.ports,he.2.1 i (Or.inl hi)]
    · funext i Z
      unfold CensoredFirstHeight.maskedSelf
      cases hi : p.2.1 i with
      | true => simp only [hi,if_true,he.2.1 i (Or.inr hi)]
      | false => simp only [hi,Bool.false_eq_true,if_false]
  | succ t ih =>
    intro p θ η he
    have ha := ih p.2.2 (θ.1 p.1) (η.1 p.1) he.2.2
    simp only [known,decode,ha]
    apply FrontierOracleScalar.scalar_erasure
    · intro i hi; rw [he.1 i hi]
    · intro i hi; rw [he.1 i hi]
    · intro i hi; simp only [nodeIncoming,centers,he.2.1 i (Or.inl hi)]
    · intro i hi; simp only [nodePorts,centers,he.2.1 i (Or.inl hi)]
    · funext i Z
      unfold CensoredHierarchy.maskedSelf
      cases hi : p.2.1 i with
      | true => simp only [hi,if_true,centers,he.2.1 i (Or.inr hi)]
      | false => simp only [hi,Bool.false_eq_true,if_false]

theorem weight_eq_of_sameKnown (K : ℝ) : ∀ t (p : Plan m t) (θ η : Parameters Y E H m t),
    SameKnown t p θ η → weight K t p (decode t θ)=weight K t p (decode t η) := by
  intro t
  induction t with
  | zero =>
    intro p θ η he
    funext Z
    apply FrontierOracleScalar.prefix_congr
    intro i hi
    simp only [Inner.ports,decode,he.2.1 i (Or.inl hi)]
  | succ t ih =>
    intro p θ η he
    funext Z
    have hp : CensoredLeaf.prefixWeight (nodePorts (width m t) (centers K (decode (t+1) θ)) Z) p.1=
        CensoredLeaf.prefixWeight (nodePorts (width m t) (centers K (decode (t+1) η)) Z) p.1 := by
      apply FrontierOracleScalar.prefix_congr
      intro i hi
      simp only [nodePorts,centers,decode,he.2.1 i (Or.inl hi)]
    simp only [weight]
    rw [hp]
    exact congrArg (fun x => _ * x)
      (congrFun (ih p.2.2 (θ.1 p.1) (η.1 p.1) he.2.2) _)

end GradientHessian.CensoredOracle
