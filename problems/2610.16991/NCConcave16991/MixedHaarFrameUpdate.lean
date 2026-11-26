import NCConcave16991.MixedHaarFrameCandidate
import NCConcave16991.MixedHaarCanonicalCoordinates

/-! # A total measurable inverse-reveal update of canonical public frames -/

noncomputable section

namespace NCConcave16991.MixedHaar

open Set MeasureTheory

set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency true

attribute [local irreducible] prefixSpan tailIsometry tailOrthogonal householderOrthogonal frameHead frameTail
  Haar.orthogonalLinearIsometryEquiv

def frameUpdateActiveAt {k : ℕ} (r : Fin (k + 1)) (hr : r.val < k)
    (F G : Haar.OrthogonalGroup k) (x g : Space k) : FrameState k :=
  (nextRank r hr,
    F * tailOrthogonal r (householderOrthogonal (firstTailVector r hr - normalize (frameTail r F g))),
    G * tailOrthogonal r (householderOrthogonal (firstTailVector r hr - normalize (frameTail r G x))))

def frameUpdateAt {k : ℕ} (r : Fin (k + 1)) (F G : Haar.OrthogonalGroup k) (x g : Space k) : FrameState k :=
  if hr : r.val < k then
    if frameTail r G x = 0 then (r,F,G) else frameUpdateActiveAt r hr F G x g
  else (r,F,G)

def frameUpdate {k : ℕ} (s : FrameState k) (x g : Space k) : FrameState k := frameUpdateAt s.1 s.2.1 s.2.2 x g

theorem frameUpdateActiveAt_measurable {k : ℕ} (r : Fin (k + 1)) (hr : r.val < k) :
    Measurable (fun p : (Haar.OrthogonalGroup k × Haar.OrthogonalGroup k) × (Space k × Space k) ↦
      frameUpdateActiveAt r hr p.1.1 p.1.2 p.2.1 p.2.2) := by
  have hF : Measurable (fun p : (Haar.OrthogonalGroup k × Haar.OrthogonalGroup k) × (Space k × Space k) ↦ p.1.1) :=
    measurable_fst.comp measurable_fst
  have hG : Measurable (fun p : (Haar.OrthogonalGroup k × Haar.OrthogonalGroup k) × (Space k × Space k) ↦ p.1.2) :=
    measurable_snd.comp measurable_fst
  have hx : Measurable (fun p : (Haar.OrthogonalGroup k × Haar.OrthogonalGroup k) × (Space k × Space k) ↦ p.2.1) :=
    measurable_fst.comp measurable_snd
  have hg : Measurable (fun p : (Haar.OrthogonalGroup k × Haar.OrthogonalGroup k) × (Space k × Space k) ↦ p.2.2) :=
    measurable_snd.comp measurable_snd
  have hq := (frameTail_continuous r).measurable.comp (hG.prodMk hx)
  have hh := (frameTail_continuous r).measurable.comp (hF.prodMk hg)
  have h0 : Measurable (fun _ : (Haar.OrthogonalGroup k × Haar.OrthogonalGroup k) × (Space k × Space k) ↦
      firstTailVector r hr) := measurable_const
  have hθ := householderOrthogonal_measurable.comp (h0.sub (normalize_measurable.comp hh))
  have he := householderOrthogonal_measurable.comp (h0.sub (normalize_measurable.comp hq))
  exact measurable_const.prodMk ((hF.mul ((tailOrthogonal_measurable r).comp hθ)).prodMk
    (hG.mul ((tailOrthogonal_measurable r).comp he)))

theorem frameUpdateAt_measurable {k : ℕ} (r : Fin (k + 1)) :
    Measurable (fun p : (Haar.OrthogonalGroup k × Haar.OrthogonalGroup k) × (Space k × Space k) ↦
      frameUpdateAt r p.1.1 p.1.2 p.2.1 p.2.2) := by
  unfold frameUpdateAt
  by_cases hr : r.val < k
  · simp only [hr,ite_true]
    apply Measurable.ite
    · exact measurableSet_eq_fun ((frameTail_continuous r).measurable.comp
        ((measurable_snd.comp measurable_fst).prodMk (measurable_fst.comp measurable_snd))) measurable_const
    · exact measurable_const.prodMk ((measurable_fst.comp measurable_fst).prodMk (measurable_snd.comp measurable_fst))
    · exact frameUpdateActiveAt_measurable r hr
  · simp only [hr,ite_false]
    exact measurable_const.prodMk ((measurable_fst.comp measurable_fst).prodMk (measurable_snd.comp measurable_fst))

theorem frameUpdate_measurable {k : ℕ} :
    Measurable (fun p : FrameState k × (Space k × Space k) ↦ frameUpdate p.1 p.2.1 p.2.2) :=
  measurable_finite_indexed (fun p : FrameState k × (Space k × Space k) ↦ p.1.1)
    (measurable_fst.comp measurable_fst)
    (fun r p ↦ frameUpdateAt r p.1.2.1 p.1.2.2 p.2.1 p.2.2)
    (fun r ↦ (frameUpdateAt_measurable r).comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd))

theorem frameUpdateActiveAt_agrees_prefix {k : ℕ} (r : Fin (k + 1)) (hr : r.val < k)
    (F G : Haar.OrthogonalGroup k) (x g : Space k) (z : FrameTape k) (y : prefixSpan r) :
    Haar.orthogonalLinearIsometryEquiv (frameComplete (frameUpdateActiveAt r hr F G x g) z)
      (Haar.orthogonalLinearIsometryEquiv F (y : Space k)) = Haar.orthogonalLinearIsometryEquiv G (y : Space k) := by
  let y' : prefixSpan (nextRank r hr) := ⟨y.val,prefixSpan_mono r (nextRank r hr) (by change r.val ≤ r.val + 1; omega) y.property⟩
  have hh := frameComplete_prefix (frameUpdateActiveAt r hr F G x g) z y'
  change Haar.orthogonalLinearIsometryEquiv (frameComplete (frameUpdateActiveAt r hr F G x g) z)
    (Haar.orthogonalLinearIsometryEquiv (F * tailOrthogonal r _) y.val) =
      Haar.orthogonalLinearIsometryEquiv (G * tailOrthogonal r _) y.val at hh
  rw [Haar.action_mul,Haar.action_mul,tailOrthogonal_fixes_prefix,tailOrthogonal_fixes_prefix] at hh
  exact hh

theorem frameUpdate_agrees_prefix {k : ℕ} (s : FrameState k) (x g : Space k) (z : FrameTape k) (y : prefixSpan s.1) :
    Haar.orthogonalLinearIsometryEquiv (frameComplete (frameUpdate s x g) z)
      (Haar.orthogonalLinearIsometryEquiv s.2.1 (y : Space k)) = Haar.orthogonalLinearIsometryEquiv s.2.2 (y : Space k) := by
  unfold frameUpdate frameUpdateAt
  split_ifs
  · exact frameComplete_prefix s z y
  · exact frameUpdateActiveAt_agrees_prefix _ _ _ _ _ _ z y
  · exact frameComplete_prefix s z y

end NCConcave16991.MixedHaar
