import Bilevel.PolishedLiteralPhysicalPieces
import Bilevel.PolishedLiteralCompensatedJets

/-! The actual joint selected hierarchy has at most three active resolution
jets. Both the unique macro index and the resolution annuli are derived
from the source functions. -/
noncomputable section
open scoped BigOperators
namespace Bilevel.PolishedLiteral
open ChiBoundedChain PrimitiveGeometry ZeroChainSchedule ZeroChainResidualBounds
namespace Parameters
variable {X U : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
variable (P : Parameters (X:=X) (U:=U))

def microActive (i : Fin (P.macroNode.n+1)) (u : U) : Finset ℕ := by
  classical
  exact (Finset.range (P.J+1)).filter (fun j => ∃ k : Fin 4,
    iteratedFDeriv ℝ k.val (P.microPiece i j) u≠0)

omit [CompleteSpace X] in
theorem micro_overlap (c θ : ℝ) (hc : 0<c) (hcs : c≤1/16) (hβ : 0<P.β) (hθ : 1≤θ)
    (hJ : P.J=levels θ) (hδ : P.δ=resolution c P.β θ)
    (i : Fin (P.macroNode.n+1)) (u : U) : (P.microActive i u).card≤3 := by
  let H : U → Space P.n := fun u => P.β⁻¹ • P.coordinates i u
  have hH : ContDiff ℝ 3 H := (P.coordinates_contDiff i).const_smul _
  have he (j : ℕ) : P.microPiece i j=PolishedLiteralCarry.carriedPiece P.n (levels θ)
      (resolution c 1 θ) (P.L*P.β^2) H j := P.microPiece_scaled c θ hc hβ hθ hJ hδ i j
  have hset : P.microActive i u=PolishedLiteralCarry.carriedActive P.n (levels θ)
      (resolution c 1 θ) (P.L*P.β^2) H u := by
    classical
    ext j
    simp only [microActive,PolishedLiteralCarry.carriedActive,Finset.mem_filter,hJ,he]
  rw [hset]
  exact PolishedLiteralCarry.at_most_three_carried_pieces P.n (levels θ) (resolution c 1 θ)
    (P.L*P.β^2) hH (fun j _ => resolution_pos c 1 θ hc (by norm_num) hθ j)
    (fun j _ => by simpa using resolution_small c 1 θ hc.le hcs (by norm_num) hθ j)
    (fun i j hij hj => resolutions_separated c 1 θ hc.le (by norm_num) hθ i j hij hj) u

theorem selectedPiece_nonzero_term (j : ℕ) (z : Joint X U) (k : ℕ) (hk : k≤3)
    (hn : iteratedFDeriv ℝ k (P.selectedPiece j) z≠0) :
    ∃ i : Fin (P.macroNode.n+1),iteratedFDeriv ℝ k (fun y : Joint X U =>
      jointSelector P.macroNode i y*P.microPiece i j y.snd) z≠0 := by
  classical
  by_contra! hz
  apply hn
  change iteratedFDeriv ℝ k (fun y : Joint X U => ∑ i : Fin (P.macroNode.n+1),
    jointSelector P.macroNode i y*(P.microPiece i j ∘ sndMap) y) z=0
  rw [iteratedFDeriv_sum (fun i _ => ((jointSelector_contDiff P.macroNode i).mul
    ((P.microPiece_contDiff i j).comp (sndMap (X:=X) (U:=U)).contDiff)).of_le
      (show (k:WithTop ℕ∞)≤3 by exact_mod_cast hk))]
  simp only [Finset.sum_apply]
  exact Finset.sum_eq_zero (fun i _ => hz i)

theorem selectedPiece_nonzero_factors (j : ℕ) (z : Joint X U) (k : ℕ) (hk : k≤3)
    (hn : iteratedFDeriv ℝ k (P.selectedPiece j) z≠0) :
    ∃ (i : Fin (P.macroNode.n+1)) (a b : ℕ),a≤k ∧ b≤k ∧
      iteratedFDeriv ℝ a (jointSelector (U:=U) P.macroNode i) z≠0 ∧
      iteratedFDeriv ℝ b (P.microPiece i j) z.snd≠0 := by
  obtain ⟨i,hi⟩ := P.selectedPiece_nonzero_term j z k hk hn
  have hga : ContDiff ℝ 3 (fun y : Joint X U => P.microPiece i j y.snd) :=
    (P.microPiece_contDiff i j).comp (sndMap (X:=X) (U:=U)).contDiff
  have hmacro : ∃ a≤k,iteratedFDeriv ℝ a (jointSelector (U:=U) P.macroNode i) z≠0 := by
    by_contra! hz
    exact hi (jet_mul_zero_left (jointSelector_contDiff P.macroNode i) hga z k hk hz)
  have hmicro : ∃ b≤k,iteratedFDeriv ℝ b (P.microPiece i j) z.snd≠0 := by
    by_contra! hz
    apply hi
    apply jet_mul_zero_right (jointSelector_contDiff P.macroNode i) hga z k hk
    intro q hq
    apply ZeroChainResidualJets.flat_jet_comp (sndMap (X:=X) (U:=U)).contDiff
      (P.microPiece_contDiff i j) z q (by omega)
    intro l hl
    rw [show sndMap z=z.snd from rfl,hz l (by omega),norm_zero]
  obtain ⟨a,ha,hna⟩ := hmacro
  obtain ⟨b,hb,hnb⟩ := hmicro
  exact ⟨i,a,b,ha,hb,hna,hnb⟩

theorem selectedPiece_overlap (c θ : ℝ) (hc : 0<c) (hcs : c≤1/16) (hβ : 0<P.β) (hθ : 1≤θ)
    (hJ : P.J=levels θ) (hδ : P.δ=resolution c P.β θ) (z : Joint X U) :
    (P.data.activePieces z).card≤3 := by
  classical
  let S := P.data.activePieces z
  by_cases hS : S.Nonempty
  · obtain ⟨j,hj⟩ := hS
    obtain ⟨hjrange,k,hk⟩ := Finset.mem_filter.mp hj
    obtain ⟨i,a,b,ha,hb,hia,_⟩ := P.selectedPiece_nonzero_factors j z k.val (by omega) hk
    have hsub : S⊆P.microActive i z.snd := by
      intro l hl
      obtain ⟨hlrange,q,hq⟩ := Finset.mem_filter.mp hl
      obtain ⟨i',a',b',ha',hb',hia',hib'⟩ := P.selectedPiece_nonzero_factors l z q.val (by omega) hq
      have he : i'=i := jointSelector_jets_unique P.macroNode i' i z a' a (by omega) (by omega) hia' hia
      subst i'
      exact Finset.mem_filter.mpr ⟨hlrange,⟨⟨b',by omega⟩,hib'⟩⟩
    exact (Finset.card_le_card hsub).trans (P.micro_overlap c θ hc hcs hβ hθ hJ hδ i z.snd)
  · have hzero : S=∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    change S.card≤3
    rw [hzero]
    norm_num

end Parameters
end Bilevel.PolishedLiteral
