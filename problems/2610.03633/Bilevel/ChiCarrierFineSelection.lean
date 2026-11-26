import Bilevel.ChiCarrierFineEnvelope

/-! The actual finite ancestor-selector operator, its exact linearity, and
joint fine-envelope propagation. Leaf estimates remain explicit here and
are discharged by construction-specific fine leaves in the next module. -/
noncomputable section
open scoped BigOperators
namespace Bilevel.ChiCarrier
open ChiBoundedChain ChiRecursive

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def selectFamily (m : ℕ) (D : Geometry E) (leaf : ℕ → List ℕ → Blocks m E → ℝ) :
    ℕ → ℕ → List ℕ → Blocks m E → ℝ
  | 0,j,I,x => leaf j I x
  | d+1,j,I,x => ∑ i : Fin ((D j I).n+1),jointSelector m j (D j I) i x*
      selectFamily m D leaf d (j+1) (child I i.val) x

theorem selectFamily_contDiff (m : ℕ) (D : Geometry E) (leaf : ℕ → List ℕ → Blocks m E → ℝ)
    (hleaf : ∀ j I,ContDiff ℝ 3 (leaf j I)) (d j : ℕ) (I : List ℕ) :
    ContDiff ℝ 3 (selectFamily m D leaf d j I) := by
  induction d generalizing j I with
  | zero => exact hleaf j I
  | succ d ih =>
    exact ContDiff.sum (fun i _ => (jointSelector_contDiff m j (D j I) i 3).mul (ih (j+1) (child I i.val)))

theorem selectFamily_sum {ι : Type*} [Fintype ι] (m : ℕ) (D : Geometry E)
    (leaf : ι → ℕ → List ℕ → Blocks m E → ℝ) (d j : ℕ) (I : List ℕ) (x : Blocks m E) :
    selectFamily m D (fun j I x => ∑ a : ι,leaf a j I x) d j I x=
      ∑ a : ι,selectFamily m D (leaf a) d j I x := by
  induction d generalizing j I with
  | zero => rfl
  | succ d ih =>
    simp only [selectFamily,ih,Finset.mul_sum]
    exact Finset.sum_comm

theorem selectFamily_sub (m : ℕ) (D : Geometry E)
    (f g : ℕ → List ℕ → Blocks m E → ℝ) (d j : ℕ) (I : List ℕ) (x : Blocks m E) :
    selectFamily m D (fun j I x => f j I x-g j I x) d j I x=
      selectFamily m D f d j I x-selectFamily m D g d j I x := by
  induction d generalizing j I with
  | zero => rfl
  | succ d ih => simp only [selectFamily,ih,mul_sub,Finset.sum_sub_distrib]

theorem selectFamily_congr_leaf (m : ℕ) (D : Geometry E)
    (f g : ℕ → List ℕ → Blocks m E → ℝ) (d j : ℕ) (I : List ℕ)
    (he : ∀ P,f (j+d) P=g (j+d) P) :
    selectFamily m D f d j I=selectFamily m D g d j I := by
  induction d generalizing j I with
  | zero => exact he I
  | succ d ih =>
    funext x
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    exact congrFun (ih (j+1) (child I i.val) (fun P => by simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using he P)) x

theorem jointCarrier_selectFamily (m : ℕ) (D : Geometry E) (d t j : ℕ) (I : List ℕ) :
    jointCarrier m D (d+t) j I t=
      selectFamily m D (fun j I => jointCarrier m D d j I 0) t j I := by
  induction t generalizing j I with
  | zero => rfl
  | succ t ih =>
    funext x
    change (∑ i : Fin ((D j I).n+1),jointSelector m j (D j I) i x*
      jointCarrier m D (d+t) (j+1) (child I i.val) t x)=_
    simp only [selectFamily]
    apply Finset.sum_congr rfl
    intro i _
    rw [ih]

def NodeJetAdmissible (D : Node E) : Prop :=
  0≤D.ell ∧ 0<D.width ∧ D.width≤D.radius ∧ 0<D.parentWidth ∧ D.parentWidth≤D.radius

/-- The leaf derivative premise is a recursive interface only. The
ancestor selectors, joint product rule, and absence of stage-count loss are
all proved from the actual node definitions. -/
theorem constructed_fine_selection_bound : ∃ Cs : ℝ,1≤Cs ∧
    ∀ (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
      (m : ℕ) (D : Geometry F), (∀ j I,NodeJetAdmissible (D j I)) →
      ∀ (leaf : ℕ → List ℕ → Blocks m F → ℝ), (∀ j I,ContDiff ℝ 3 (leaf j I)) →
      ∀ (T : ℕ) (Cb a M δ : ℝ),0≤Cb → 0≤a → 0≤M → 0<δ →
      (∀ j I,j<T → δ≤(D j I).width ∧ a≤M*(D j I).width) →
      (∀ I x q,q≤3 → ‖iteratedFDeriv ℝ q (leaf T I) x‖≤Cb*fineScale a M δ q) →
      ∀ (d j : ℕ),j+d=T → ∀ (I : List ℕ) (x : Blocks m F) (q : ℕ),q≤3 →
      ‖iteratedFDeriv ℝ q (selectFamily m D leaf d j I) x‖≤Cs^d*Cb*fineScale a M δ q := by
  obtain ⟨C,hC,hnode⟩ := constructed_joint_node_jets
  have hC0 : 0≤C := by linarith
  let Cs := 8*C
  have hCs : 1≤Cs := by unfold Cs;linarith
  have hCs0 : 0≤Cs := by linarith
  refine ⟨Cs,hCs,fun F _ _ _ m D hadm leaf hleaf T Cb a M δ hCb ha hM hδ hwidth hbase => ?_⟩
  intro d
  induction d with
  | zero =>
    intro j hj I x q hq
    have hjT : j=T := by omega
    subst j
    simpa only [selectFamily,pow_zero,one_mul] using hbase I x q hq
  | succ d ih =>
    intro j hj I x q hq
    have hd := hadm j I
    have hw := hwidth j I (by omega)
    have hS := fineScale_nonneg ha hM hδ.le q
    change ‖iteratedFDeriv ℝ q (fun y => ∑ i : Fin ((D j I).n+1),
      jointSelector m j (D j I) i y*selectFamily m D leaf d (j+1) (child I i.val) y) x‖≤_
    apply selected_products_jet_bound m j (D j I)
      (fun i => selectFamily m D leaf d (j+1) (child I i.val))
      (fun i => selectFamily_contDiff m D leaf hleaf d (j+1) (child I i.val)) x q hq _ (by positivity)
    intro i
    have hs := coarser_fine_product (jointSelector_contDiff m j (D j I) i 3)
      (selectFamily_contDiff m D leaf hleaf d (j+1) (child I i.val))
      C (Cs^d*Cb) a M δ (D j I).width hC0 (by positivity) ha hM hδ hd.2.1 hw.1 hw.2 x q hq
      (fun k hk => (hnode F (D j I) hd.1 hd.2.1 hd.2.2.1 hd.2.2.2.1 hd.2.2.2.2 m j i x k (by omega)).1)
      (fun k hk => ih (j+1) (by omega) (child I i.val) x k (by omega))
    convert hs using 1
    simp only [pow_succ,Cs]
    ring

end Bilevel.ChiCarrier
