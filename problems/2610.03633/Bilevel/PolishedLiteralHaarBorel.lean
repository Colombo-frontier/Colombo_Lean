import Bilevel.PolishedLiteralRawMean

/-! Joint measurability of the actual fixed Haar mean and original SFO.
Full disclosed arrays give globally identical formulas, so all Borel
proofs use public raw scalar extensions, never hidden completions. -/
noncomputable section
open MeasureTheory
namespace Bilevel.PolishedLiteralActualObserver
open EuclideanGaussian ProjectionPosterior PrimitiveGeometry
set_option autoImplicit false
set_option maxHeartbeats 1800000
variable {dx du : ℕ} (P : PolishedLiteral.Parameters (X:=Space dx) (U:=Space du))
  (hx : P.macroNode.n+1≤dx) (hu : (P.macroNode.n+1)*(P.n+1)≤du)

abbrev HaarPoint := OrthogonalHaar.Group dx × OrthogonalHaar.Group du

def haarInstance (g : HaarPoint (dx:=dx) (du:=du)) :
    PolishedLiteral.Parameters (X:=Space dx) (U:=Space du) :=
  framedParameters P (HaarFrame.frame _ _ hx g.1) (HaarFrame.frame_orthonormal _ _ hx g.1)
    (HaarFrame.frame _ _ hu g.2) (HaarFrame.frame_orthonormal _ _ hu g.2)

def haarArrays (g : HaarPoint (dx:=dx) (du:=du)) : P.MacroColumns × P.MicroColumns :=
  (HaarFrame.frame _ _ hx g.1,blockColumns (S:=P.macroNode.n+1) (M:=P.n+1) (HaarFrame.frame _ _ hu g.2))

theorem haarArrays_measurable : Measurable (haarArrays P hx hu) :=
  ((HaarFrame.frame_measurable _ _ hx).comp measurable_fst).prodMk
    ((blockColumns_measurable (S:=P.macroNode.n+1) (M:=P.n+1)).comp
      ((HaarFrame.frame_measurable _ _ hu).comp measurable_snd))

theorem haar_outerMean_eq_raw (κ : ℝ) (g : HaarPoint (dx:=dx) (du:=du)) :
    (haarInstance P hx hu g).outerMean κ=rawOuterMean P κ (haarArrays P hx hu g).1 (haarArrays P hx hu g).2 := by
  have he := rawOuterMean_eq_outerMean (haarInstance P hx hu g) κ
    (haarArrays P hx hu g).1 (haarArrays P hx hu g).2
    (fun j => (PolishedTwoFrameBlocks.ofFrame_basis P.macroNode.n
      (HaarFrame.frame dx (P.macroNode.n+1) hx g.1) (HaarFrame.frame_orthonormal _ _ hx g.1) j).symm)
    (fun i j => (PolishedTwoFrameBlocks.microBlockFrame_basis (S:=P.macroNode.n+1) (n:=P.n)
      (HaarFrame.frame du ((P.macroNode.n+1)*(P.n+1)) hu g.2) (HaarFrame.frame_orthonormal _ _ hu g.2) i j).symm)
  exact he.symm

variable [MeasurableSpace (Joint (Space dx) (Space du))] [BorelSpace (Joint (Space dx) (Space du))]

def haarLoss (κ : ℝ) (z : HaarPoint (dx:=dx) (du:=du) × Joint (Space dx) (Space du)) : ℝ :=
  ‖gradient ((haarInstance P hx hu z.1).outerMean κ) z.2‖

theorem haarLoss_measurable (κ : ℝ) : Measurable (haarLoss P hx hu κ) := by
  have ht : Measurable (fun z : HaarPoint (dx:=dx) (du:=du) × Joint (Space dx) (Space du) =>
      (haarArrays P hx hu z.1,z.2)) := (haarArrays_measurable P hx hu).prodMap measurable_id
  have hm := (rawOuterMean_gradient_measurable P κ).comp ht
  have he : (fun z : HaarPoint (dx:=dx) (du:=du) × Joint (Space dx) (Space du) =>
      gradient ((haarInstance P hx hu z.1).outerMean κ) z.2)=
      (fun z => gradient (rawOuterMean P κ (haarArrays P hx hu z.1).1 (haarArrays P hx hu z.1).2) z.2) := by
    funext z
    rw [haar_outerMean_eq_raw]
  unfold haarLoss
  rw [show (fun z : HaarPoint (dx:=dx) (du:=du) × Joint (Space dx) (Space du) =>
      ‖gradient ((haarInstance P hx hu z.1).outerMean κ) z.2‖)=
      (fun z => ‖gradient (rawOuterMean P κ (haarArrays P hx hu z.1).1 (haarArrays P hx hu z.1).2) z.2‖)
    from congrArg (fun f => fun z => ‖f z‖) he]
  exact hm.norm

omit [MeasurableSpace (Joint (Space dx) (Space du))] [BorelSpace (Joint (Space dx) (Space du))] in
theorem prefixColumns_full {d K : ℕ} (V : Frame d K) : prefixColumns V K=V := by
  funext i
  exact if_pos i.isLt

omit [MeasurableSpace (Joint (Space dx) (Space du))] [BorelSpace (Joint (Space dx) (Space du))] in
theorem saturated_reply (U : Frame dx (P.macroNode.n+1)) (hU : Orthonormal ℝ U)
    (V : Frame du ((P.macroNode.n+1)*(P.n+1))) (hV : Orthonormal ℝ V)
    (τ p : ℝ) (hb : 0<P.macroNode.width) (hβ : 0<P.β) (hτ : 0<τ) (hτβ : τ≤P.β/4)
    (hτb : τ≤P.macroNode.width) (hδ : ∀ j,j<P.J → τ≤P.δ j)
    (coin : Bool) (q : QuerySpace (dx:=dx) (du:=du)) :
    originalReply P U hU V hV τ p coin q=
      rawCounterReply P τ p U V q ((P.macroNode.n+1)*(P.n+1)) coin := by
  let S := P.macroNode.n+1
  let M := P.n+1
  have hmx : (macroSchedule S M).count (S*M)=S := by simp [macroSchedule,S,M]
  have hmc : sourceCounts S M (S*M)=fun _ => M := by
    funext i
    simp only [sourceCounts,min_self]
    have hd : S*M/M=S := by dsimp [M];simp
    rw [hd,if_pos i.isLt]
  have hnext : S*M≤advance (S*M) coin := by unfold advance;omega
  have hmp : (macroSchedule S M).count (advance (S*M) coin)=S :=
    le_antisymm ((macroSchedule S M).bound _) (by
      have hh := (macroSchedule S M).monotone hnext
      rw [hmx] at hh
      exact hh)
  have hup : (microSchedule (S*M)).count (advance (S*M) coin)=S*M := min_eq_left hnext
  have hq : (framedParameters P U hU V hV).BlindBox ((macroSchedule S M).count (S*M))
      (sourceCounts S M (S*M)) τ q := by
    rw [hmx,hmc]
    constructor
    · intro j hj
      have hlt : j.val<S := j.isLt
      exact False.elim ((Nat.not_lt_of_ge hj) hlt)
    · intro i j hj
      have hlt : j.val<M := j.isLt
      exact False.elim ((Nat.not_lt_of_ge hj) hlt)
  have he := actual_counter_reply P U hU V hV (S*M) coin τ p hb hβ hτ hτβ hτb hδ q hq
  rw [hmp,hup,prefixColumns_full,prefixColumns_full] at he
  exact he

variable [MeasurableSpace (QuerySpace (dx:=dx) (du:=du))] [BorelSpace (QuerySpace (dx:=dx) (du:=du))]

def haarResponse (τ p : ℝ) (g : HaarPoint (dx:=dx) (du:=du))
    (q : QuerySpace (dx:=dx) (du:=du)) (coin : Bool) :=
  originalReply P (HaarFrame.frame _ _ hx g.1) (HaarFrame.frame_orthonormal _ _ hx g.1)
    (HaarFrame.frame _ _ hu g.2) (HaarFrame.frame_orthonormal _ _ hu g.2) τ p coin q

omit [MeasurableSpace (Joint (Space dx) (Space du))] [BorelSpace (Joint (Space dx) (Space du))] in
theorem haarResponse_measurable (τ p : ℝ) (hb : 0<P.macroNode.width) (hβ : 0<P.β)
    (hτ : 0<τ) (hτβ : τ≤P.β/4) (hτb : τ≤P.macroNode.width) (hδ : ∀ j,j<P.J → τ≤P.δ j) :
    Measurable (fun z : HaarPoint (dx:=dx) (du:=du) × (QuerySpace (dx:=dx) (du:=du) × Bool) =>
      haarResponse P hx hu τ p z.1 z.2.1 z.2.2) := by
  have ht : Measurable (fun z : HaarPoint (dx:=dx) (du:=du) × (QuerySpace (dx:=dx) (du:=du) × Bool) =>
      ((HaarFrame.frame _ _ hx z.1.1,HaarFrame.frame _ _ hu z.1.2),
        (z.2.1,(((P.macroNode.n+1)*(P.n+1)),z.2.2)))) :=
    (((HaarFrame.frame_measurable _ _ hx).comp (measurable_fst.comp measurable_fst)).prodMk
      ((HaarFrame.frame_measurable _ _ hu).comp (measurable_snd.comp measurable_fst))).prodMk
      ((measurable_fst.comp measurable_snd).prodMk (measurable_const.prodMk (measurable_snd.comp measurable_snd)))
  have hm := (rawCounterReply_measurable P τ p).comp ht
  have he : (fun z : HaarPoint (dx:=dx) (du:=du) × (QuerySpace (dx:=dx) (du:=du) × Bool) =>
      haarResponse P hx hu τ p z.1 z.2.1 z.2.2)=
      (fun z => rawCounterReply P τ p (HaarFrame.frame _ _ hx z.1.1) (HaarFrame.frame _ _ hu z.1.2)
        z.2.1 ((P.macroNode.n+1)*(P.n+1)) z.2.2) := by
    funext z
    exact saturated_reply P _ _ _ _ τ p hb hβ hτ hτβ hτb hδ _ _
  rw [he]
  exact hm

end Bilevel.PolishedLiteralActualObserver
