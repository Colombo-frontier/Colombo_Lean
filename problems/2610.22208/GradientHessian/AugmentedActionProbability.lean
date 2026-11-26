import GradientHessian.AugmentedOriginalProbability

/-! Put the direction bounds on the literal finite action inventory at a
fixed root height, removing the factorization's auxiliary address casts. -/

noncomputable section
namespace GradientHessian.AugmentedDirectionFamilies
open Classical MeasureTheory Matrix LowRank HigherHierarchy HierarchyAddresses RawHierarchy
  FrontierState TaskState TaskSlots GeometricRepair ComparisonController ComparisonControllerReplay
  RawDirection AugmentedPolicy AugmentedVisibleQueries
open DirectionPolicyReplay (Point centerStop oldStop)

theorem prepend_surjective (depth : ℕ) (leaf : Leaf (0+depth+1)) :
    ∃ w : Word depth,∃ i : Fin 8,leafEquiv (0+depth) (prependSlot 0 depth w i)=leaf := by
  let w : Word depth := fun a => leaf ⟨a.val,by have := a.isLt; omega⟩
  let i : Fin 8 := leaf ⟨depth,by omega⟩
  refine ⟨w,i,?_⟩
  change leafWord (0+depth) (prependSlot 0 depth w i)=ofLex leaf
  funext a
  by_cases ha : a.val<depth
  · have he : (⟨a.val,ha⟩ : Fin depth).castLE (by omega)=a := Fin.ext rfl
    rw [← he,prependSlot_prefix]
    rfl
  · have he : a=(⟨depth,by omega⟩ : Fin (0+depth+1)) := Fin.ext (by change a.val=depth; have := a.isLt; omega)
    rw [he,prepend_last]
    rfl

variable {d n r J ell : ℕ} {E : Type} {H : ℕ → Type}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [∀ h,NormedAddCommGroup (H h)] [∀ h,InnerProductSpace ℝ (H h)]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] [Nontrivial E]
  [∀ h,MeasurableSpace (H h)] [∀ h,BorelSpace (H h)] [∀ h,FiniteDimensional ℝ (H h)] [∀ h,Nontrivial (H h)]
variable [∀ t,MeasurableSpace (Point d J E H t)] [∀ t,BorelSpace (Point d J E H t)]
  [∀ t,MeasurableSpace (DirectionPolicyReplay.Ordinary d J E H t)] [∀ t,BorelSpace (DirectionPolicyReplay.Ordinary d J E H t)]
  [∀ t,MeasurableSpace (DirectionPolicyReplay.Rich d J E H t)] [∀ t,BorelSpace (DirectionPolicyReplay.Rich d J E H t)]
variable {Seed S : Type*} [MeasurableSpace Seed] [MeasurableSpace S]
variable (P : Matrix (Fin d) (Fin d) ℝ) (B : Matrix (Fin d) (Fin r) ℝ) (fallback : Fin d → ℝ)
variable [IsProbabilityMeasure (ConditionedSource.sourceLaw (n := n) P J)] [NeZero r]
variable (σ : Measure Seed) [IsProbabilityMeasure σ]
variable (t : ℕ) (policy : Machine.Policy (Seed × Packet d J E H t ell) S (Point d J E H t) (Ordinary d J E H t ell) (Rich d J E H t ell))

theorem localized_action_probability (h : Fin t) (path : Word (t-(h.val+1))) (i : Fin 8)
    (hJ : 4≤J) (hP : IsOrthogonalProjector P) (hB : Bᵀ*B=1) (hPB : P*B=B)
    (hdim : 2≤Module.finrank ℝ (H h.val)) {K : ℝ} (hK : 16≤K) (N : ℕ) (hell : 0<ell) :
    ((RawHierarchy.law (n := n) (r := r) (J := J) (E := E) (H := H) P t).prod σ).real
      {x | originalRepair (ell := ell) P B fallback t (.localized h path i) policy K N x} ≤
        (8^(h.val+2)*(4096*J^2+1)*ell : ℕ)*
          (2*(6*width (4096*J^2) h.val/radius (4096*J^2) K h.val)^(Module.finrank ℝ (H h.val)-1)) := by
  rcases h with ⟨h,hh⟩
  dsimp only [Fin.val_mk] at path hdim ⊢
  obtain ⟨depth,ht⟩ := Nat.exists_eq_add_of_le (Nat.succ_le_of_lt hh)
  subst t
  let w : Word depth := fun a => path (Fin.cast (by omega : depth=h+1+depth-(h+1)) a)
  have hb := center_original_probability (n := n) (ell := ell) P B fallback σ h depth w i policy hJ hP hB hPB hdim hK N hell
  simpa only [centerFactorAction,w,Fin.eta] using hb

theorem old_action_probability (path : Word t) (i : Fin 8) (j : Fin (FirstHeight.depth (4096*J^2+1)+2))
    (hJ : 4≤J) (hP : IsOrthogonalProjector P) (hB : Bᵀ*B=1) (hPB : P*B=B)
    {K : ℝ} (hK : 0<K) (N : ℕ) (hell : 0<ell) :
    ((RawHierarchy.law (n := n) (r := r) (J := J) (E := E) (H := H) P t).prod σ).real
      {x | originalRepair (ell := ell) P B fallback t (.old path i j) policy K N x} ≤
        (8*(4096*J^2+1)*ell : ℕ)*(2*Real.exp (-(Module.finrank ℝ E:ℝ)/18432)) := by
  have hb : ∀ (w : Word (0+t))
      (Q : Machine.Policy (Seed × Packet d J E H (0+t) ell) S (Point d J E H (0+t)) (Ordinary d J E H (0+t) ell) (Rich d J E H (0+t) ell)),
      ((RawHierarchy.law (n := n) (r := r) (J := J) (E := E) (H := H) P (0+t)).prod σ).real
        {x | originalRepair (ell := ell) P B fallback (0+t) (.old w i j) Q K N x} ≤
          (8*(4096*J^2+1)*ell : ℕ)*(2*Real.exp (-(Module.finrank ℝ E:ℝ)/18432)) := by
    intro w Q
    let w' : Word t := fun a => w (Fin.cast (Nat.zero_add t).symm a)
    simpa only [oldFactorAction,w',Fin.eta] using
      old_original_probability (n := n) (ell := ell) P B fallback σ t w' i j Q hJ hP hB hPB hK N hell
  rw [Nat.zero_add] at hb
  exact hb path policy

theorem inner_action_probability (leaf : Leaf (t+1)) (j : Fin (4096*J^2+1)) (k : Fin (Inner.absoluteDepth+2))
    (hJ : 4≤J) (hP : IsOrthogonalProjector P) (hB : Bᵀ*B=1) (hPB : P*B=B)
    {K : ℝ} (hK : 0<K) (N : ℕ) (hell : 0<ell) :
    ((RawHierarchy.law (n := n) (r := r) (J := J) (E := E) (H := H) P t).prod σ).real
      {x | originalRepair (ell := ell) P B fallback t (.inner leaf j k) policy K N x} ≤
        ((4096*J^2+1)*ell : ℕ)*(2*Real.exp (-(Module.finrank ℝ E:ℝ)/18432)) := by
  have hb : ∀ (l : Leaf (0+t+1))
      (Q : Machine.Policy (Seed × Packet d J E H (0+t) ell) S (Point d J E H (0+t)) (Ordinary d J E H (0+t) ell) (Rich d J E H (0+t) ell)),
      ((RawHierarchy.law (n := n) (r := r) (J := J) (E := E) (H := H) P (0+t)).prod σ).real
        {x | originalRepair (ell := ell) P B fallback (0+t) (.inner l j k) Q K N x} ≤
          ((4096*J^2+1)*ell : ℕ)*(2*Real.exp (-(Module.finrank ℝ E:ℝ)/18432)) := by
    intro l Q
    obtain ⟨w,i,hi⟩ := prepend_surjective t l
    simpa only [innerFactorAction,hi] using
      inner_original_probability (n := n) (ell := ell) P B fallback σ t w i j k Q hJ hP hB hPB hK N hell
  rw [Nat.zero_add] at hb
  exact hb leaf policy

theorem mark_action_probability (leaf : Leaf (t+1)) (j : Fin (4096*J^2+1))
    (hJ : 4≤J) (hP : IsOrthogonalProjector P) (hB : Bᵀ*B=1) (hPB : P*B=B)
    {K : ℝ} (hK : 0<K) (N : ℕ) (hell : 0<ell) :
    ((RawHierarchy.law (n := n) (r := r) (J := J) (E := E) (H := H) P t).prod σ).real
      {x | originalRepair (ell := ell) P B fallback t (.futureMark leaf j) policy K N x} ≤
        ((4096*J^2+1)*ell : ℕ)*(2*Real.exp (-(1/8)*(1/3072:ℝ)^2*(r:ℝ))) := by
  letI := RawHierarchy.law_probability (n := n) (r := r) (J := J) (E := E) (H := H) P t
  have hm : ((RawHierarchy.law (n := n) (r := r) (J := J) (E := E) (H := H) P t).prod σ).real
      {x | originalRepair (ell := ell) P B fallback t (.futureMark leaf j) policy K N x} ≤
      ((RawHierarchy.law (n := n) (r := r) (J := J) (E := E) (H := H) P t).prod σ).real
        {x | AugmentedPolicy.hitBy P B fallback t policy K (blockMark leaf j) (AugmentedDisclosure.markStop leaf j)
          N ((N+1)*(8^(t+1)+4)) TaskState.initial x} := by
    apply measureReal_mono
    · intro x hx
      exact action_hitBy P B fallback t policy K N TaskState.initial (initial_ready hell) hell x (.futureMark leaf j)
        (blockMark leaf j) (by simp only [blockMark,decide_true]) hx
    · finiteness
  exact hm.trans (AugmentedMark.shadow_probability P B fallback t leaf j policy σ hJ hP hB hPB hK N
    ((N+1)*(8^(t+1)+4)) TaskState.initial (initial_ready hell) hell)

end GradientHessian.AugmentedDirectionFamilies


