import Bilevel.ChiVirtualActiveInverseGerm
import Bilevel.ChiVirtualReplyEquality
import Bilevel.ChiReleasedFrontierSupport

/-! Quantitative strict blind margin at the actual nonlinear active inverse.
The bound follows from compact-normal comparison and old-space projection
geometry, leaving a uniform open neighborhood for virtual oracle equality. -/
noncomputable section
open scoped Topology
set_option maxHeartbeats 1200000
namespace Bilevel.ChiPrefixEvaluation
open ChiBoundedChain ChiRecursive ChiCarrier PrimitiveGeometry ChiExtension ZeroChainSchedule NearIdentityInverse ChiOuter ChiTreeProgress
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

variable {m : ℕ} (M : Node E) (D : Geometry F) (J : ℕ) (hm : J<m)
  (W V : Fin m → Submodule ℝ F) [∀ i,CompleteSpace (W i)]
  (hWV : ∀ i,W i≤V i) (r : ℕ → List ℕ → ℕ)
  (htree : TreeProjection D 0 J (by simpa using hm) W r)
  (hhp : ∀ t,t<J → ∀ P,0<(D (t+1) P).parentWidth)
  (hw : ∀ t,t<J → ∀ P,(D (t+1) P).width≤(D (t+1) P).parentWidth)
  (hfuture : ∀ t,t<J → ∀ P,∀ i : Fin ((D t P).n+1),r t P ≤ i.val →
    r (t+1) (child P i.val)≤(D (t+1) (child P i.val)).n)
  (c v : ℝ) (hc : 0<c) (hcs : c≤1/128) (hβ : 0<(D J []).width) (hv : 1≤v)
  (hell : ∀ P,0≤(D J P).ell) (hwidth : ∀ P,(D J P).width=(D J []).width)
  (hfinest : ∀ P,∀ k : Fin ((D J P).n+1),r J P ≤ k.val →
    (D J P).radius*‖(W ⟨J,hm⟩).orthogonalProjection ((D J P).frame (basis k))‖≤
      width c (D J []).width v (levels v)/8)
  (s : ℕ) (index radialIndex : Fin J → Fin s) (fineIndex : Fin s)
  (rad R : ℕ → ℝ) (dn : ℝ) (hR : ∀ i : Fin J,0<R (i.val+1))
  [CompleteSpace (normalKnown W s)] [CompleteSpace (normalKnown V s)]


include hm hWV htree hhp hw hfuture hcs hell hwidth hfinest hR in
theorem hierarchy_active_inverse_reply_eq_virtual
    (hmargin : ∀ j P (hj : j≤J),∀ k : Fin ((D j P).n+1),r j P≤k.val →
      (D j P).radius*‖(W ⟨j,by omega⟩).orthogonalProjection ((D j P).frame (basis k))‖≤(D j P).width/8)
    (hWlast : ∀ j P,j≤J → width c (D J []).width v (levels v)≤(D j P).width/128)
    (ha : ∀ z,‖iteratedFDeriv ℝ 2
      (hierarchyExtension m M D J c v hc hβ hv s index radialIndex fineIndex rad R dn) z‖≤1/12)
    (hi : ∀ z,‖iteratedFDeriv ℝ 2
      (hierarchyInactiveExtension m M D J c v hc hβ hv s index radialIndex fineIndex rad R dn) z‖≤1/12)
    (x : E)
    (u : normalKnown W s)
    (rM sM : ℕ) (a : ℕ → List ℕ → ℕ)
    (macroColumns : Fin (M.n+1) → E) (columns : ∀ j I,Fin ((D j I).n+1) → F)
    (hmPrefix : ∀ k : Fin (M.n+1),k.val<sM → macroColumns k=M.frame (basis k))
    (hprefix : ∀ j I,∀ k : Fin ((D j I).n+1),k.val<a j I → columns j I k=(D j I).frame (basis k))
    (hms : rM≤sM) (hra : ∀ j I,r j I≤a j I)
    (hmw : 0<M.width) (hmR : 0<M.radius)
    (hmacro : ∀ k : Fin (M.n+1),rM≤k.val → |M.coordinates x k|≤M.width/8)
    (hWM : width c (D J []).width v (levels v)≤M.width)
    (hafuture : ∀ t,t<J → ∀ I,∀ i : Fin ((D t I).n+1),a t I ≤ i.val →
      a (t+1) (child I i.val)≤(D (t+1) (child I i.val)).n)
    (hadvance : ∀ i : Fin (M.n+1),i.val≤rM → FrontierAdvance D r a J 0 [i.val])
    (hnewcols : ∀ P,∀ k : Fin ((D J P).n+1),k.val<a J P → (D J P).frame (basis k)∈V ⟨J,hm⟩)
    (hg : ContDiff ℝ 3 (virtualActive m M D J sM a macroColumns columns c v s index radialIndex fineIndex rad R dn))
    (ε : NNReal) (hε : ε<1)
    (hG : ∀ z,‖iteratedFDeriv ℝ 2
      (virtualActive m M D J sM a macroColumns columns c v s index radialIndex fineIndex rad R dn) z‖≤(ε:ℝ)) :
    let hf := hierarchyExtension_contDiff m M D J c v hc hβ hv s index radialIndex fineIndex rad R dn
      (fun i => (htree (i.val+1) [] (by omega) (by have := i.isLt;omega)).width_pos)
    let hsmall : (1/12:NNReal)<1 := by change (1/12:ℝ)<1;norm_num
    PartialLegendre.jointSolution (reassociated_gradient_lipschitz hf (1/12) ha) hsmall x (u:Full (Blocks m F) s)=
      PartialLegendre.jointSolution (reassociated_gradient_lipschitz hg ε hG) hε x (u:Full (Blocks m F) s) ∧
    ∀ (μ L : ℝ) (t : Blocks m F),
      gradient (fullExtensionLower (hierarchyExtension m M D J c v hc hβ hv s index radialIndex fineIndex rad R dn)
        hf (1/12) ha hsmall μ L) (pack (pack x t) (u:Full (Blocks m F) s))=
      gradient (fullExtensionLower (virtualActive m M D J sM a macroColumns columns c v s index radialIndex fineIndex rad R dn)
        hg ε hG hε μ L) (pack (pack x t) (u:Full (Blocks m F) s)) := by
  dsimp only
  have hf := hierarchyExtension_contDiff m M D J c v hc hβ hv s index radialIndex fineIndex rad R dn
    (fun i => (htree (i.val+1) [] (by omega) (by have := i.isLt;omega)).width_pos)
  have hfront := released_frontierKnown M D J r a (V ⟨J,hm⟩) rM x hmw hmacro hadvance hnewcols
  have hlocal := hierarchy_active_germ_at_inverse M D J hm W V hWV r htree hhp hw hfuture c v hc hcs hβ hv
    hell hwidth hfinest s index radialIndex fineIndex rad R dn hR hmargin hWlast ha hi x hfront u
    rM sM a macroColumns columns hmPrefix hprefix hms hra hmw hmR hmacro hWM hafuture hadvance
  constructor
  · exact (jointSolution_eq_of_extension_germ hf hg (1/12) ε (by change (1/12:ℝ)<1;norm_num)
      hε ha hG x (u:Full (Blocks m F) s) hlocal).1
  · intro μ L t
    exact fullExtensionLower_gradient_eq_of_extension_germ hf hg (1/12) ε
      (by change (1/12:ℝ)<1;norm_num) hε ha hG μ L (pack (pack x t) (u:Full (Blocks m F) s)) hlocal

end Bilevel.ChiPrefixEvaluation
