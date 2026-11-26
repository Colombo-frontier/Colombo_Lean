import Bilevel.ChiVirtualUpperReply

/-! Complete-column evaluations recover the original functions everywhere.
This auxiliary representation is for the original random instance; it is
separate from the algorithm's partial disclosed store. -/
noncomputable section
open scoped BigOperators RealInnerProductSpace
namespace Bilevel.ChiPrefixEvaluation
open ChiBoundedChain ChiRecursive ChiCarrier PrimitiveGeometry ChiOuter
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def nodeColumns (D : Node E) : Fin (D.n+1) → E := fun k => D.frame (basis k)
def fullCounts (D : Geometry E) (j : ℕ) (I : List ℕ) : ℕ := (D j I).n+1
def fullColumns (D : Geometry E) : ColumnData D := fun j I => nodeColumns (D j I)

theorem readout_full (D : Node E) (u : E) :
    readout D.n (D.n+1) D.radius (nodeColumns D) u=D.coordinates u := by
  ext k
  rw [readout_apply,if_pos k.isLt]
  exact (coordinates_inner D.n D.radius D.frame u k).symm

theorem virtualH_full (D : Node E) (u : E) : virtualH D (D.n+1) (nodeColumns D) u=D.H u := by
  unfold virtualH Node.H
  rw [readout_full]

theorem virtualSelector_full (D : Node E) (i : Fin (D.n+1)) (u : E) :
    virtualSelector D (D.n+1) (nodeColumns D) i u=D.selector i u := by
  unfold virtualSelector Node.selector
  rw [readout_full]

theorem virtualResidual_full (D : Node E) (i : Fin (D.n+1)) (u : E) :
    virtualResidual D (D.n+1) (nodeColumns D) i u=D.residual i u := by
  unfold virtualResidual Node.residual
  rw [readout_full]

theorem virtualRelease_full (D : Node E) (u : E) :
    virtualRelease D (D.n+1) (nodeColumns D) u=D.release u := by
  unfold virtualRelease Node.release
  rw [readout_full]

theorem virtualOuterSelector_full (D : Node E) (i : Fin (D.n+1)) (u : E) :
    virtualOuterSelector D (D.n+1) (nodeColumns D) i u=wrappedSelector D i u := by
  unfold virtualOuterSelector wrappedSelector
  rw [readout_full]

theorem virtualPayload_full (D : Geometry E) (d j : ℕ) (I : List ℕ) (u : ℕ → E) :
    virtualPayload D (fullCounts D) (fullColumns D) d j I u=payloadValue D d j I u := by
  induction d generalizing j I with
  | zero => simp only [virtualPayload,payloadValue,fullCounts,fullColumns,virtualH_full]
  | succ d ih =>
    simp only [virtualPayload,payloadValue,fullCounts,fullColumns,virtualH_full,
      virtualResidual_full,virtualRelease_full,virtualSelector_full]
    simp only [ih]

theorem virtualCarrier_full (D : Geometry E) (d j : ℕ) (I : List ℕ) (k : ℕ) (u : ℕ → E) :
    virtualCarrier D (fullCounts D) (fullColumns D) d j I k u=selectedCarrier D d j I k u := by
  induction d generalizing j I k with
  | zero => cases k <;> simp only [virtualCarrier,selectedCarrier,fullCounts,fullColumns,virtualH_full]
  | succ d ih =>
    cases k <;> simp only [virtualCarrier,selectedCarrier,fullCounts,fullColumns,virtualH_full,
      virtualResidual_full,virtualRelease_full,virtualSelector_full]
    simp only [ih]

theorem virtualSelect_full (m : ℕ) (D : Geometry E) (leaf : ∀ j I,Space (D j I).n → ℝ)
    (d j : ℕ) (I : List ℕ) (x : Blocks m E) :
    virtualSelect D (fullCounts D) (fullColumns D) leaf d j I (padded x)=
      selectFamily m D (fun a B y => leaf a B ((D a B).coordinates (block m a y))) d j I x := by
  induction d generalizing j I with
  | zero => simp only [virtualSelect,selectFamily,fullCounts,fullColumns,readout_full,padded]
  | succ d ih =>
    simp only [virtualSelect,selectFamily,fullCounts,fullColumns,virtualSelector_full]
    simp only [ih,jointSelector,padded,Function.comp_apply]

end Bilevel.ChiPrefixEvaluation
