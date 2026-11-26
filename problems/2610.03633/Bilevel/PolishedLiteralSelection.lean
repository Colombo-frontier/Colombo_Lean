import Bilevel.PolishedLiteralFormulas
import Bilevel.ChiOuterCarrierSelectors
import Bilevel.PolishedLiteralResidualBounds
import Bilevel.PolishedLiteralSelectorJets

/-! Joint macro--micro derivative selection for the literal exponential-profile additive family. The one-sided selector
jets remove the number of macro stages from all bounds through order three. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
open scoped BigOperators
namespace Bilevel.PolishedLiteral
open PrimitiveGeometry ChiRecursive ChiBoundedChain ChiCarrier
open ZeroChainResidualBounds ZeroChainResidualJets
variable {X U : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]

def fstMap : Joint X U →L[ℝ] X :=
  (ContinuousLinearMap.fst ℝ X U).comp (WithLp.prodContinuousLinearEquiv 2 ℝ X U).toContinuousLinearMap

def sndMap : Joint X U →L[ℝ] U :=
  (ContinuousLinearMap.snd ℝ X U).comp (WithLp.prodContinuousLinearEquiv 2 ℝ X U).toContinuousLinearMap

omit [CompleteSpace X] [CompleteSpace U] in
theorem fstMap_norm_le : ‖fstMap (X:=X) (U:=U)‖≤1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro z
  exact (WithLp.norm_fst_le X z).trans_eq (one_mul _).symm

omit [CompleteSpace X] [CompleteSpace U] in
theorem sndMap_norm_le : ‖sndMap (X:=X) (U:=U)‖≤1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro z
  exact (WithLp.norm_snd_le X z).trans_eq (one_mul _).symm

def jointSelector (M : Node X) (i : Fin (M.n+1)) (z : Joint X U) : ℝ :=
  PolishedLiteral.wrappedSelector M i z.fst

def selected (M : Node X) (f : Fin (M.n+1) → U → ℝ) (z : Joint X U) : ℝ :=
  ∑ i : Fin (M.n+1),jointSelector M i z*f i z.snd

omit [CompleteSpace U] in
theorem jointSelector_contDiff (M : Node X) (i : Fin (M.n+1)) :
    ContDiff ℝ 3 (jointSelector (U:=U) M i) :=
  (PolishedLiteral.wrappedSelector_contDiff M i 3).comp (fstMap (X:=X) (U:=U)).contDiff

omit [CompleteSpace U] in
theorem jointSelector_jets_unique (M : Node X) (i l : Fin (M.n+1)) (z : Joint X U)
    (k q : ℕ) (hk : k≤3) (hq : q≤3)
    (hi : iteratedFDeriv ℝ k (jointSelector M i) z≠0)
    (hl : iteratedFDeriv ℝ q (jointSelector M l) z≠0) : i=l := by
  have hlatent (a : Fin (M.n+1)) (s : ℕ) (hs : s≤3)
      (ha : iteratedFDeriv ℝ s (jointSelector M a) z≠0) :
      ∃ t≤s,iteratedFDeriv ℝ t (PolishedLiteral.selector M.n a) (M.width⁻¹ • M.coordinates z.fst)≠0 := by
    by_contra! hz
    apply ha
    have hc : ContDiff ℝ 3 (fun y : Joint X U => M.width⁻¹ • M.coordinates y.fst) :=
      ((M.coordinates_contDiff 3).comp (fstMap (X:=X) (U:=U)).contDiff).const_smul M.width⁻¹
    exact ZeroChainResidualJets.flat_jet_comp hc (PolishedLiteral.selector_contDiff M.n 3 a) z s hs
      (fun t ht => by rw [hz t ht,norm_zero])
  obtain ⟨a,ha,hai⟩ := hlatent i k hk hi
  obtain ⟨b,hb,hbl⟩ := hlatent l q hq hl
  exact PolishedLiteral.selector_all_jets_unique i l _ a b (by omega) (by omega) hai hbl

omit [CompleteSpace U] in
theorem selected_jet_bound (M : Node X) (f : Fin (M.n+1) → U → ℝ)
    (hf : ∀ i,ContDiff ℝ 3 (f i)) (z : Joint X U) (k : ℕ) (hk : k≤3)
    (B : ℝ) (hB : 0≤B)
    (hb : ∀ i,‖iteratedFDeriv ℝ k (fun y : Joint X U => jointSelector M i y*f i y.snd) z‖≤B) :
    ‖iteratedFDeriv ℝ k (selected M f) z‖≤B := by
  change ‖iteratedFDeriv ℝ k (fun y : Joint X U => ∑ i : Fin (M.n+1),
    jointSelector M i y*(f i ∘ sndMap) y) z‖≤B
  rw [iteratedFDeriv_sum (fun i _ => ((jointSelector_contDiff M i).mul
    ((hf i).comp (sndMap (X:=X) (U:=U)).contDiff)).of_le
      (show (k:WithTop ℕ∞)≤3 by exact_mod_cast hk))]
  simp only [Finset.sum_apply]
  apply ChiBoundedChain.norm_sum_le_of_exclusive _ B hB hb
  intro i l hil hi
  by_contra hl
  have hsel (a : Fin (M.n+1))
      (ha : iteratedFDeriv ℝ k (fun y : Joint X U => jointSelector M a y*f a y.snd) z≠0) :
      ∃ j≤k,iteratedFDeriv ℝ j (jointSelector M a) z≠0 := by
    by_contra! hz
    exact ha (jet_mul_zero_left (jointSelector_contDiff M a)
      ((hf a).comp (sndMap (X:=X) (U:=U)).contDiff) z k hk hz)
  obtain ⟨a,ha,hai⟩ := hsel i hi
  obtain ⟨b,hb,hbl⟩ := hsel l hl
  exact hil (jointSelector_jets_unique M i l z a b (by omega) (by omega) hai hbl)

theorem joint_selector_jet_bounds : ∃ Cs : ℝ,1≤Cs ∧
    ∀ (X U : Type*) [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
      [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
      (M : Node X),0<M.width → M.width≤M.radius → ∀ i (z : Joint X U) k,k≤3 →
      ‖iteratedFDeriv ℝ k (jointSelector M i) z‖≤Cs/M.width^k := by
  obtain ⟨B,hB,hraw⟩ := PolishedLiteral.selector_uniform_jets
  refine ⟨100000*B,by linarith,fun X U _ _ _ _ _ _ M hw hR i z k hk => ?_⟩
  apply (ChiOuter.contraction_jet_bound (fstMap (X:=X) (U:=U)) fstMap_norm_le
    (PolishedLiteral.wrappedSelector_contDiff M i 3) z k hk).trans
  have hh := scaled_radial_profile_jet_bound (PolishedLiteral.selector_contDiff M.n 3 i)
    B 1 M.width M.radius (by linarith) (by norm_num) hw hR (fun q hq y => hraw M.n i y q hq)
    M.frame z.fst k hk
  simpa only [PolishedLiteral.wrappedSelector,Node.coordinates,Function.comp_def,
    ZeroChainResidualScaled.scaled,one_mul,mul_one] using hh

theorem selected_residual_joint_jet_bounds : ∃ C : ℝ,1≤C ∧
    ∀ (X U : Type*) [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
      [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
      (P : Parameters (X:=X) (U:=U)),0≤P.L → 0<P.β → P.β≤P.radius →
      P.β≤P.macroNode.width → P.macroNode.width≤P.macroNode.radius →
      ∀ (z : Joint X U) k,k≤3 →
      ‖iteratedFDeriv ℝ k P.selectedResidual z‖≤C*P.L*P.β^2/P.β^k := by
  obtain ⟨Cs,hCs,hs⟩ := joint_selector_jet_bounds
  obtain ⟨Cr,hCr,hr⟩ := wrapped_residual_jet_bounds
  have hCs0 : 0≤Cs := by linarith
  have hCr0 : 0≤Cr := by linarith
  refine ⟨8*Cs*Cr,by nlinarith [mul_le_mul hCs hCr zero_le_one hCs0],?_⟩
  intro X U _ _ _ _ _ _ P hL hβ hR hβb hbR z k hk
  change ‖iteratedFDeriv ℝ k (selected P.macroNode P.microResidual) z‖≤_
  apply selected_jet_bound P.macroNode P.microResidual P.microResidual_contDiff z k hk _ (by positivity)
  intro i
  have hsel (q : ℕ) (hq : q≤k) : ‖iteratedFDeriv ℝ q (jointSelector P.macroNode i) z‖≤Cs/P.β^q :=
    (hs X U P.macroNode (hβ.trans_le hβb) hbR i z q (by omega)).trans
      (div_le_div_of_nonneg_left hCs0 (pow_pos hβ _) (pow_le_pow_left₀ hβ.le hβb _))
  have hres (q : ℕ) (hq : q≤k) :
      ‖iteratedFDeriv ℝ q (fun y : Joint X U => P.microResidual i y.snd) z‖≤(Cr*P.L*P.β^2)/P.β^q := by
    apply (ChiOuter.contraction_jet_bound (sndMap (X:=X) (U:=U)) sndMap_norm_le
      (P.microResidual_contDiff i) z q (by omega)).trans
    exact hr U P.n q P.L P.β P.radius (by omega) hL hβ hR (P.frames i) z.snd
  have hh := same_width_product_jets (jointSelector_contDiff P.macroNode i)
    ((P.microResidual_contDiff i).comp (sndMap (X:=X) (U:=U)).contDiff)
    Cs (Cr*P.L*P.β^2) P.β hCs0 (by positivity) hβ z k hk hsel hres
  convert hh using 1
  ring

end Bilevel.PolishedLiteral
