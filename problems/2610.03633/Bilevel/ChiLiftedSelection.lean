import Bilevel.ChiCarrierFineSelection
import Bilevel.ChiLinearJetContraction

/-! Ancestor selectors on a heterogeneous ambient product. The projection
is a contraction; all mixed derivatives and one-child sparsity are retained. -/
noncomputable section
open scoped BigOperators
namespace Bilevel.ChiLiftedCarrier
open ChiBoundedChain ChiRecursive ChiCarrier
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

def selector (m j : ℕ) (D : Node E) (A : X →L[ℝ] Blocks m E) (i : Fin (D.n+1)) : X → ℝ :=
  jointSelector m j D i ∘ A

theorem selector_contDiff (m j : ℕ) (D : Node E) (A : X →L[ℝ] Blocks m E)
    (i : Fin (D.n+1)) (k : ℕ) : ContDiff ℝ k (selector m j D A i) :=
  (jointSelector_contDiff m j D i k).comp A.contDiff

theorem selector_jets_unique (m j : ℕ) (D : Node E) (A : X →L[ℝ] Blocks m E)
    (i l : Fin (D.n+1)) (x : X) (k q : ℕ) (hk : k≤3) (hq : q≤3)
    (hi : iteratedFDeriv ℝ k (selector m j D A i) x≠0)
    (hl : iteratedFDeriv ℝ q (selector m j D A l) x≠0) : i=l :=
  jointSelector_jets_unique m j D i l (A x) k q hk hq
    (linear_jet_nonzero A (jointSelector_contDiff m j D i 3) x k hk hi)
    (linear_jet_nonzero A (jointSelector_contDiff m j D l 3) x q hq hl)

theorem selected_product_jet_selector (m j : ℕ) (D : Node E) (A : X →L[ℝ] Blocks m E) (i : Fin (D.n+1))
    {f : X → ℝ} (hf : ContDiff ℝ 3 f) (x : X) (k : ℕ) (hk : k≤3)
    (hi : iteratedFDeriv ℝ k (fun y => selector m j D A i y*f y) x≠0) :
    ∃ q≤k,iteratedFDeriv ℝ q (selector m j D A i) x≠0 := by
  by_contra! hzero
  exact hi (ZeroChainResidualBounds.jet_mul_zero_left (selector_contDiff m j D A i 3) hf x k hk hzero)

theorem selected_products_jets_unique (m j : ℕ) (D : Node E) (A : X →L[ℝ] Blocks m E) (i l : Fin (D.n+1))
    {f g : X → ℝ} (hf : ContDiff ℝ 3 f) (hg : ContDiff ℝ 3 g)
    (x : X) (k q : ℕ) (hk : k≤3) (hq : q≤3)
    (hi : iteratedFDeriv ℝ k (fun y => selector m j D A i y*f y) x≠0)
    (hl : iteratedFDeriv ℝ q (fun y => selector m j D A l y*g y) x≠0) : i=l := by
  obtain ⟨a,ha,hai⟩ := selected_product_jet_selector m j D A i hf x k hk hi
  obtain ⟨b,hb,hbl⟩ := selected_product_jet_selector m j D A l hg x q hq hl
  exact selector_jets_unique m j D A i l x a b (by omega) (by omega) hai hbl

/-- Actual constructed selectors prevent a stage-count factor, even when the
selected functions depend jointly on all current and descendant blocks. -/
theorem selected_products_jet_bound (m j : ℕ) (D : Node E) (A : X →L[ℝ] Blocks m E)
    (f : Fin (D.n+1) → X → ℝ) (hf : ∀ i,ContDiff ℝ 3 (f i))
    (x : X) (k : ℕ) (hk : k≤3) (B : ℝ) (hB : 0≤B)
    (hb : ∀ i,‖iteratedFDeriv ℝ k (fun y => selector m j D A i y*f i y) x‖≤B) :
    ‖iteratedFDeriv ℝ k (fun y => ∑ i : Fin (D.n+1),selector m j D A i y*f i y) x‖≤B := by
  rw [iteratedFDeriv_sum (fun i _ => ((selector_contDiff m j D A i 3).mul (hf i)).of_le
    (show (k:WithTop ℕ∞)≤3 by exact_mod_cast hk))]
  simp only [Finset.sum_apply]
  apply norm_sum_le_of_exclusive _ B hB hb
  intro i l hil hi
  by_contra hl
  exact hil (selected_products_jets_unique m j D A i l (hf i) (hf l) x k k hk hk hi hl)

def selectFamily (m : ℕ) (D : Geometry E) (A : X →L[ℝ] Blocks m E) (leaf : ℕ → List ℕ → X → ℝ) :
    ℕ → ℕ → List ℕ → X → ℝ
  | 0,j,I,x => leaf j I x
  | d+1,j,I,x => ∑ i : Fin ((D j I).n+1),selector m j (D j I) A i x*
      selectFamily m D A leaf d (j+1) (child I i.val) x

theorem selectFamily_contDiff (m : ℕ) (D : Geometry E) (A : X →L[ℝ] Blocks m E) (leaf : ℕ → List ℕ → X → ℝ)
    (hleaf : ∀ j I,ContDiff ℝ 3 (leaf j I)) (d j : ℕ) (I : List ℕ) :
    ContDiff ℝ 3 (selectFamily m D A leaf d j I) := by
  induction d generalizing j I with
  | zero => exact hleaf j I
  | succ d ih =>
    exact ContDiff.sum (fun i _ => (selector_contDiff m j (D j I) A i 3).mul (ih (j+1) (child I i.val)))

theorem selectFamily_sum {ι : Type*} [Fintype ι] (m : ℕ) (D : Geometry E) (A : X →L[ℝ] Blocks m E)
    (leaf : ι → ℕ → List ℕ → X → ℝ) (d j : ℕ) (I : List ℕ) (x : X) :
    selectFamily m D A (fun j I x => ∑ a : ι,leaf a j I x) d j I x=
      ∑ a : ι,selectFamily m D A (leaf a) d j I x := by
  induction d generalizing j I with
  | zero => rfl
  | succ d ih =>
    simp only [selectFamily,ih,Finset.mul_sum]
    exact Finset.sum_comm

theorem selectFamily_sub (m : ℕ) (D : Geometry E) (A : X →L[ℝ] Blocks m E)
    (f g : ℕ → List ℕ → X → ℝ) (d j : ℕ) (I : List ℕ) (x : X) :
    selectFamily m D A (fun j I x => f j I x-g j I x) d j I x=
      selectFamily m D A f d j I x-selectFamily m D A g d j I x := by
  induction d generalizing j I with
  | zero => rfl
  | succ d ih => simp only [selectFamily,ih,mul_sub,Finset.sum_sub_distrib]

theorem selectFamily_congr_leaf (m : ℕ) (D : Geometry E) (A : X →L[ℝ] Blocks m E)
    (f g : ℕ → List ℕ → X → ℝ) (d j : ℕ) (I : List ℕ)
    (he : ∀ P,f (j+d) P=g (j+d) P) :
    selectFamily m D A f d j I=selectFamily m D A g d j I := by
  induction d generalizing j I with
  | zero => exact he I
  | succ d ih =>
    funext x
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    exact congrFun (ih (j+1) (child I i.val) (fun P => by simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using he P)) x

theorem constructed_fine_selection_bound : ∃ Cs : ℝ,1≤Cs ∧
    ∀ (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
      (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X]
      (m : ℕ) (D : Geometry F) (A : X →L[ℝ] Blocks m F),‖A‖≤1 → (∀ j I,NodeJetAdmissible (D j I)) →
      ∀ (leaf : ℕ → List ℕ → X → ℝ), (∀ j I,ContDiff ℝ 3 (leaf j I)) →
      ∀ (T : ℕ) (Cb a M δ : ℝ),0≤Cb → 0≤a → 0≤M → 0<δ →
      (∀ j I,j<T → δ≤(D j I).width ∧ a≤M*(D j I).width) →
      (∀ I x q,q≤3 → ‖iteratedFDeriv ℝ q (leaf T I) x‖≤Cb*fineScale a M δ q) →
      ∀ (d j : ℕ),j+d=T → ∀ (I : List ℕ) (x : X) (q : ℕ),q≤3 →
      ‖iteratedFDeriv ℝ q (selectFamily m D A leaf d j I) x‖≤Cs^d*Cb*fineScale a M δ q := by
  obtain ⟨C,hC,hnode⟩ := constructed_joint_node_jets
  have hC0 : 0≤C := by linarith
  let Cs := 8*C
  have hCs : 1≤Cs := by unfold Cs;linarith
  have hCs0 : 0≤Cs := by linarith
  refine ⟨Cs,hCs,fun F _ _ _ X _ _ m D A hA hadm leaf hleaf T Cb a M δ hCb ha hM hδ hwidth hbase => ?_⟩
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
      selector m j (D j I) A i y*selectFamily m D A leaf d (j+1) (child I i.val) y) x‖≤_
    apply selected_products_jet_bound m j (D j I) A
      (fun i => selectFamily m D A leaf d (j+1) (child I i.val))
      (fun i => selectFamily_contDiff m D A leaf hleaf d (j+1) (child I i.val)) x q hq _ (by positivity)
    intro i
    have hs := coarser_fine_product (selector_contDiff m j (D j I) A i 3)
      (selectFamily_contDiff m D A leaf hleaf d (j+1) (child I i.val))
      C (Cs^d*Cb) a M δ (D j I).width hC0 (by positivity) ha hM hδ hd.2.1 hw.1 hw.2 x q hq
      (fun k hk => (linear_jet_contraction A hA (jointSelector_contDiff m j (D j I) i 3) x k (by omega)).trans
        (hnode F (D j I) hd.1 hd.2.1 hd.2.2.1 hd.2.2.2.1 hd.2.2.2.2 m j i (A x) k (by omega)).1)
      (fun k hk => ih (j+1) (by omega) (child I i.val) x k (by omega))
    convert hs using 1
    simp only [pow_succ,Cs]
    ring

end Bilevel.ChiLiftedCarrier
