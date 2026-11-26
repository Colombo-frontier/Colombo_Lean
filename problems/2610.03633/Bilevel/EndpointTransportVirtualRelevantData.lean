import Bilevel.EndpointTransportVirtualFormula
import Bilevel.EndpointTransportUpperPrefix

/-! Physical hierarchy evaluators use ordinary arrays only strictly above
terminal depth. Terminal latent frame columns never enter observable data. -/
noncomputable section
set_option maxHeartbeats 1200000
open scoped BigOperators
namespace Bilevel.EndpointTransportResponse
open EndpointTransportMatrix ChiBoundedChain ChiRecursive ChiCarrier ChiOuter
  PrimitiveGeometry PartialLegendre ChiPrefixEvaluation ChiExtension ZeroChainSchedule

theorem virtualPhysicalCarrier_congr_ordinary {m n D : ℕ} (G : Geometry (Block D))
    (r rs : ℕ → List ℕ → ℕ)
    (C C' : ∀ j I,Fin ((G j I).n+1) → Block D)
    (S T : ∀ j I,Fin ((G j I).n+1) → Physical n D)
    (d j : ℕ) (I : List ℕ) (t : ℕ)
    (hC : ∀ k A,j≤k → k<j+d → C k A=C' k A)
    (x : HybridTangent (Blocks m (Block D)) n D) :
    virtualPhysicalCarrier G r rs C S T d j I t x=
      virtualPhysicalCarrier G r rs C' S T d j I t x := by
  induction d generalizing j I t with
  | zero => cases t <;> rfl
  | succ d ih =>
    cases t with
    | zero =>
      cases d with
      | zero => simp only [virtualPhysicalCarrier,if_pos rfl,if_true,hC j I le_rfl (by omega)]
      | succ d =>
        simp only [virtualPhysicalCarrier,show ¬(d+1=0) by omega,if_false,virtualCarrier,
          hC j I le_rfl (by omega)]
        congr 1
        apply Finset.sum_congr rfl
        intro i _
        rw [hC (j+1) (child I i.val) (by omega) (by omega)]
    | succ t =>
      simp only [virtualPhysicalCarrier,hC j I le_rfl (by omega)]
      apply Finset.sum_congr rfl
      intro i _
      congr 1
      exact ih (j+1) (child I i.val) t (fun k A hk hkd => hC k A (by omega) (by omega))

theorem virtualPhysicalSelect_congr_ordinary {m n D : ℕ} (G : Geometry (Block D))
    (r : ℕ → List ℕ → ℕ) (C C' : ∀ j I,Fin ((G j I).n+1) → Block D)
    (leaf : ℕ → List ℕ → Physical n D → ℝ) (d j : ℕ) (I : List ℕ)
    (hC : ∀ k A,j≤k → k<j+d → C k A=C' k A)
    (x : HybridTangent (Blocks m (Block D)) n D) :
    virtualPhysicalSelect G r C leaf d j I x=virtualPhysicalSelect G r C' leaf d j I x := by
  induction d generalizing j I with
  | zero => rfl
  | succ d ih =>
    simp only [virtualPhysicalSelect,hC j I le_rfl (by omega)]
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    exact ih (j+1) (child I i.val) (fun k A hk hkd => hC k A (by omega) (by omega))

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
theorem prefixPhysicalHierarchyExtension_congr_ordinary {J n D s : ℕ}
    (M : Node E) (G : Geometry (Block D)) (P : ChiFine.Parameters)
    (ci ri : Fin J → Fin s) (fi : Fin s) (ρ R : ℕ → ℝ) (dn : ℝ)
    (rM : ℕ) (r rs : ℕ → List ℕ → ℕ) (MC : Fin (M.n+1) → E)
    (C C' : ∀ j I,Fin ((G j I).n+1) → Block D)
    (S T : ∀ j I,Fin ((G j I).n+1) → Physical n D)
    (hC : ∀ k A,k<J → C k A=C' k A) :
    prefixPhysicalHierarchyExtension M G P ci ri fi ρ R dn rM r rs MC C S T=
      prefixPhysicalHierarchyExtension M G P ci ri fi ρ R dn rM r rs MC C' S T := by
  have hc (d j : ℕ) (I : List ℕ) (t : ℕ) (hdepth : j+d=J)
      (x : HybridTangent (Blocks J (Block D)) n D) :
      virtualPhysicalCoarseCarrier G P r rs C S T d j I t x=
        virtualPhysicalCoarseCarrier G P r rs C' S T d j I t x := by
    unfold virtualPhysicalCoarseCarrier virtualPhysicalFrontier
    rw [virtualPhysicalCarrier_congr_ordinary G r rs C C' S T d j I t (fun k A _ hk => hC k A (by omega)) x,
      virtualPhysicalSelect_congr_ordinary G r C C' _ d j I (fun k A _ hk => hC k A (by omega)) x]
  have hf (p : ℕ) (I : List ℕ) (x : HybridTangent (Blocks J (Block D)) n D) :
      virtualPhysicalFinePiece G P r rs C S T p J 0 I x=
        virtualPhysicalFinePiece G P r rs C' S T p J 0 I x := by
    exact virtualPhysicalSelect_congr_ordinary G r C C' _ J 0 I (fun k A _ hk => hC k A (by omega)) x
  funext z
  unfold prefixPhysicalHierarchyExtension prefixPhysicalOuterCoarse prefixPhysicalOuterFinePiece
  simp only [hc J 0 _ _ (by omega),hf]

omit [CompleteSpace E] in
theorem prefixPhysicalUpperBase_congr_ordinary {m n D : ℕ} (M : Node E) (ν : ℝ)
    (G : Geometry (Block D)) (J : ℕ) (hJ : 0<J) (ρ R : ℝ) (rM : ℕ) (r : ℕ → List ℕ → ℕ)
    (MC : Fin (M.n+1) → E) (C C' : ∀ j I,Fin ((G j I).n+1) → Block D)
    (T : ∀ j I,Fin ((G j I).n+1) → Physical n D)
    (hC : ∀ k A,k<J → C k A=C' k A) :
    prefixPhysicalUpperBase m M ν G J ρ R rM r MC C T=
      prefixPhysicalUpperBase m M ν G J ρ R rM r MC C' T := by
  funext z
  unfold prefixPhysicalUpperBase virtualOuterReleaseCorrection
  simp only [hC 0 _ hJ]
  congr 3
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  exact virtualPhysicalCarrier_congr_ordinary G r r C C' _ T J 0 [i.val] 0
    (fun k A _ hk => hC k A (by omega)) z.snd

end Bilevel.EndpointTransportResponse
