import Bilevel.ChiVirtualUpperGerm
import Bilevel.ChiCarrierProjectionBlind

/-! Full exact upper SFO reply from the old precoin disclosed data. The
actual query inclusion and projected hidden-column bounds discharge the
scalar germ. No initial frontier column or successful coin is required. -/
noncomputable section
namespace Bilevel.ChiPrefixEvaluation
open ChiBoundedChain ChiRecursive ChiCarrier PrimitiveGeometry ChiOuter ChiExtension
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

theorem actual_upper_full_reply_from_projections {m : ℕ} (M : Node E) (ν : ℝ) (D : Geometry F)
    (J : ℕ) (hJ : 0<J) (hm : J<m) (ρ R : ℝ) (rM : ℕ) (r : ℕ → List ℕ → ℕ)
    (macroColumns : Fin (M.n+1) → E) (columns : ∀ j I,Fin ((D j I).n+1) → F)
    (hmPrefix : ∀ k : Fin (M.n+1),k.val<rM → macroColumns k=M.frame (basis k))
    (hprefix : ∀ j I,∀ k : Fin ((D j I).n+1),k.val<r j I → columns j I k=(D j I).frame (basis k))
    (hmw : 0<M.width) (hh : ∀ j I,j≤J → 0<(D j I).width)
    (hhp : ∀ j I,j≤1 → 0<(D j I).parentWidth)
    (hw : ∀ j I,j≤1 → (D j I).width≤(D j I).parentWidth)
    (hmfuture : ∀ i : Fin (M.n+1),rM≤ i.val → r 0 [i.val]≤(D 0 [i.val]).n)
    (hfuture : ∀ I,∀ i : Fin ((D 0 I).n+1),r 0 I≤ i.val →
      r 1 (child I i.val)≤(D 1 (child I i.val)).n)
    (hmR : 0<M.radius) (hDR : ∀ j I,j≤J → 0<(D j I).radius)
    (WM : Submodule ℝ E) [CompleteSpace WM]
    (W : Fin m → Submodule ℝ F) [∀ i,CompleteSpace (W i)]
    (hmacro : ∀ k : Fin (M.n+1),rM≤k.val →
      M.radius*‖WM.orthogonalProjection (M.frame (basis k))‖≤M.width/8)
    (hinner : ∀ j I (hj : j≤J),∀ k : Fin ((D j I).n+1),r j I≤k.val →
      (D j I).radius*‖(W ⟨j,by omega⟩).orthogonalProjection ((D j I).frame (basis k))‖≤(D j I).width/8)
    (s : ℕ) (b : Normals s) (q : PartialLegendre.FullNormalVariables E (Blocks m F) (Normals s))
    (hqM : q.fst.fst∈WM) (hqW : q.snd.fst∈knownSpace W)
    (δ : ℝ) (hδ : 0<δ) (hδM : δ≤M.width/16) (hδD : ∀ j I,j≤J → δ≤(D j I).width/16) :
    gradient (ChiUpper.fullUpper (upperBase m M ν D J ρ R) b) q=
      gradient (ChiUpper.fullUpper (virtualUpperBase m M ν D J ρ R rM r macroColumns columns) b) q := by
  apply fullUpper_gradient_eq_of_base_germ b q
  apply actual_upperBase_eventuallyEq_virtual (δ:=δ) m M ν D J hJ ρ R rM r macroColumns columns
    hmPrefix hprefix hmw hh hhp hw hmfuture hfuture (ChiUpper.baseProjection q)
  · intro k hk
    have hb := (M.coordinate_projection_bound hmR WM ⟨q.fst.fst,hqM⟩ k).trans (hmacro k hk)
    change |M.coordinates q.fst.fst k|≤3*M.width/16
    linarith
  · intro j I hj k hk
    have hjm : j<m := lt_of_le_of_lt hj hm
    have hb := ((D j I).coordinate_projection_bound (hDR j I hj) (W ⟨j,hjm⟩)
      ⟨q.snd.fst ⟨j,hjm⟩,hqW ⟨j,hjm⟩⟩ k).trans (hinner j I hj k hk)
    change |(D j I).coordinates (block m j q.snd.fst) k|≤3*(D j I).width/16
    rw [block,dif_pos hjm,PiLp.proj_apply]
    have hwj := hh j I hj
    linarith
  · exact hmR
  · exact hDR
  · exact hδ
  · exact hδM
  · exact hδD

end Bilevel.ChiPrefixEvaluation
