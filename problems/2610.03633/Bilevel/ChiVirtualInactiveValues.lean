import Bilevel.ChiVirtualLinear
import Bilevel.ChiVirtualCoarseValues

/-! The fixed inactive atoms are evaluated using only old disclosed
prefixes. Their cancellation is retained before ancestor selection. -/
noncomputable section
set_option maxHeartbeats 1200000
open scoped BigOperators
namespace Bilevel.ChiPrefixEvaluation
open ChiBoundedChain ChiRecursive ChiCarrier ChiOuter PrimitiveGeometry ZeroChainSchedule
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

theorem actual_selectedInactivePiece_eq_virtual (m : ℕ) (D : Geometry F) (r : ℕ → List ℕ → ℕ)
    (columns : ∀ j I,Fin ((D j I).n+1) → F) (d j : ℕ) (I : List ℕ) (x : Blocks m F)
    (hprefix : ∀ k P,∀ a : Fin ((D k P).n+1),a.val<r k P → columns k P a=(D k P).frame (basis a))
    (hh : ∀ k P,j≤k → k≤j+d → 0<(D k P).width)
    (hblind : ∀ k P,j≤k → k<j+d → ∀ a : Fin ((D k P).n+1),
      r k P≤a.val → |(D k P).coordinates (block m k x) a|≤(D k P).width/4)
    (c θ : ℝ) (hc : 0<c) (hcs : c≤1/128) (hθ : 1≤θ)
    (hell : ∀ P,0≤(D (j+d) P).ell) (hwidth : ∀ P,(D (j+d) P).width=(D (j+d) []).width)
    (hz : ∀ P,∀ a : Fin ((D (j+d) P).n+1),r (j+d) P≤a.val →
      |(D (j+d) P).coordinates (block m (j+d) x) a|≤width c (D (j+d) []).width θ (levels θ)/8)
    (p : ℕ) (hp : p≤levels θ) :
    selectedInactivePiece m D d j I c θ (width c (D (j+d) []).width θ (levels θ)/8) p x=
      virtualSelect D r columns (inactiveLeaf D c θ (width c (D (j+d) []).width θ (levels θ)/8) p)
        d j I (padded x) := by
  apply actual_select_eq_virtual m D r columns
    (inactiveLeaf D c θ (width c (D (j+d) []).width θ (levels θ)/8) p) d j I x hprefix
    (fun k P hk hkd => hh k P hk (by omega)) hblind
  intro P
  have he : width c (D (j+d) []).width θ (levels θ)/8=width c (D (j+d) P).width θ (levels θ)/8 := by rw [hwidth P]
  rw [he]
  exact actual_inactiveLeaf_eq_virtual D r r columns c θ (j+d) P p (block m (j+d) x)
    (hprefix _ _) (hell P) (hh _ _ (by omega) le_rfl) hc hcs hθ hp le_rfl
    (fun a ha => by simpa only [hwidth P] using hz P a ha)

theorem outer_inactive_atom_eq (m : ℕ) (M : Node E) (D : Geometry F) (d : ℕ)
    (c θ τ : ℝ) (p : ℕ) (z : Joint E (Blocks m F)) :
    outerSelected m M (fun i => selectedInactivePiece m D d 0 [i.val] c θ τ p) z=
      outerFinePiece m M D d c θ p z-if p=levels θ then outerFineSignal m M D d τ z else 0 := by
  by_cases hp : p=levels θ
  · simp only [outerSelected,selectedInactivePiece_eq,if_pos hp,mul_sub,Finset.sum_sub_distrib,
      outerFinePiece,outerFineSignal]
  · simp only [outerSelected,selectedInactivePiece_eq,if_neg hp,sub_zero,outerFinePiece]

theorem actual_outerInactiveAtom_eq_virtual (m : ℕ) (M : Node E) (D : Geometry F) (J rM : ℕ)
    (r : ℕ → List ℕ → ℕ) (macroColumns : Fin (M.n+1) → E)
    (columns : ∀ j I,Fin ((D j I).n+1) → F)
    (hmPrefix : ∀ k : Fin (M.n+1),k.val<rM → macroColumns k=M.frame (basis k))
    (hprefix : ∀ j I,∀ k : Fin ((D j I).n+1),k.val<r j I → columns j I k=(D j I).frame (basis k))
    (hmw : 0<M.width) (hh : ∀ j I,j≤J → 0<(D j I).width) (z : Joint E (Blocks m F))
    (hmBlind : ∀ k : Fin (M.n+1),rM≤k.val → |M.coordinates z.fst k|≤M.width/4)
    (hblind : ∀ j I,j<J → ∀ k : Fin ((D j I).n+1),r j I≤k.val →
      |(D j I).coordinates (block m j z.snd) k|≤(D j I).width/4)
    (c θ : ℝ) (hc : 0<c) (hcs : c≤1/128) (hθ : 1≤θ)
    (hell : ∀ I,0≤(D J I).ell) (hwidth : ∀ I,(D J I).width=(D J []).width)
    (hz : ∀ I,∀ k : Fin ((D J I).n+1),r J I≤k.val →
      |(D J I).coordinates (block m J z.snd) k|≤width c (D J []).width θ (levels θ)/8)
    (p : ℕ) (hp : p≤levels θ) :
    outerFinePiece m M D J c θ p z-
      (if p=levels θ then outerFineSignal m M D J (width c (D J []).width θ (levels θ)/8) z else 0)=
      virtualOuterLeaf m M D rM r macroColumns columns (inactiveLeaf D c θ (width c (D J []).width θ (levels θ)/8) p) J z := by
  rw [← outer_inactive_atom_eq]
  unfold outerSelected virtualOuterLeaf
  apply Finset.sum_congr rfl
  intro i _
  change wrappedSelector M i z.fst*selectedInactivePiece m D J 0 [i.val] c θ _ p z.snd=_
  rw [actual_outerSelector_eq_virtual M rM macroColumns hmPrefix hmw i z.fst hmBlind]
  congr 1
  simpa only [Nat.zero_add] using actual_selectedInactivePiece_eq_virtual m D r columns J 0 [i.val] z.snd hprefix
    (fun j I _ hj => hh j I (by omega)) (fun j I _ hj => hblind j I (by omega)) c θ hc hcs hθ
    (by simpa only [Nat.zero_add] using hell) (by simpa only [Nat.zero_add] using hwidth)
    (by convert hz using 1; rw [Nat.zero_add]) p hp

end Bilevel.ChiPrefixEvaluation
