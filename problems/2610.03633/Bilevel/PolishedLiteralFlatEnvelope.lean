import Bilevel.PolishedLiteralPieceBounds
import Bilevel.PolishedLiteralSelection

/-! Actual zeroth/first joint envelopes of the source residual flattened at
an arbitrary physical resolution. These are the quantitative inputs for
the conservative original SFO, including macro derivatives. -/
noncomputable section
set_option maxHeartbeats 1200000
open scoped BigOperators
namespace Bilevel.PolishedLiteral
open PrimitiveGeometry ChiBoundedChain ZeroChainPotential ZeroChainResidualBounds

theorem wrapped_flat_c1_bounds : ∃ C : ℝ,1≤C ∧
    ∀ (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
      (n k : ℕ) (L β δ R : ℝ),k≤1 → 0≤L → 0<β → 0<δ → δ≤β/16 → β≤R →
      ∀ (V : Space n →ₗᵢ[ℝ] E) (u : E),
      ‖iteratedFDeriv ℝ k (fun y => flatResidual n L β δ (WrappedChain.coordinates n R V y)) u‖≤
        C*L*β^2/β^k := by
  obtain ⟨B,hB,hb⟩ := PolishedLiteralPieceBounds.normalized_bounds
  refine ⟨100000*B,by linarith,?_⟩
  intro E _ _ _ n k L β δ R hk hL hβ hδ hs hR V u
  have hδβ : 0<δ/β := div_pos hδ hβ
  have hδβs : δ/β≤1/16 := (div_le_iff₀ hβ).mpr (by linarith)
  have hf : ContDiff ℝ 3 (normalizedFlat n (δ/β)) := normalizedFlat_contDiff n (δ/β)
  have hraw (q : ℕ) (hq : q≤k) (z : Space n) :
      ‖iteratedFDeriv ℝ q (normalizedFlat n (δ/β)) z‖≤B := by
    have hq1 : q≤1 := hq.trans hk
    interval_cases q
    · simpa only [norm_iteratedFDeriv_zero,Real.norm_eq_abs,PolishedLiteralPieceBounds.Flat] using
        ((hb n).2 (δ/β) hδβ hδβs z).1
    · have ht := ((hb n).2 (δ/β) hδβ hδβs z).2.2 0
      simpa only [Fin.val_zero,zero_add,pow_zero,div_one,PolishedLiteralPieceBounds.Flat] using ht
  let f := ZeroChainResidualScaled.scaled (normalizedFlat n (δ/β)) (L*β^2) β
  have hfun : (fun y => flatResidual n L β δ (WrappedChain.coordinates n R V y))=
      f ∘ WrappedChain.coordinates n R V := by
    rw [flatResidual_scaled n L β δ hβ.ne' hδ.ne']
    rfl
  rw [hfun]
  have hfphys : ContDiff ℝ 3 f := ZeroChainResidualScaled.scaled_contDiff hf _ _
  interval_cases k
  · have ht := ZeroChainResidualScaled.scaled_jet_bound hf (L*β^2) β B (by positivity) hβ 0
      (by norm_num) (fun z => hraw 0 (by norm_num) z) (WrappedChain.coordinates n R V u)
    simp only [norm_iteratedFDeriv_zero,Function.comp_apply,pow_zero,div_one] at ht ⊢
    have hscale : B*L*β^2≤100000*B*L*β^2 := by nlinarith [mul_nonneg (mul_nonneg (by linarith : 0≤B) hL) (sq_nonneg β)]
    exact ht.trans (by nlinarith only [hscale])
  · have hF := ZeroChainResidualScaled.scaled_jet_bound hf (L*β^2) β B (by positivity) hβ 1
      (by norm_num) (fun z => hraw 1 (by norm_num) z) (WrappedChain.coordinates n R V u)
    have hcoord := ZeroChainWrappedResidual.coordinates_positive_jet_bound n R β hβ hR V u 1 (by norm_num) (by norm_num)
    have hdf := hfphys.differentiable (by norm_num) (WrappedChain.coordinates n R V u)
    have hdc := (ZeroChainWrappedResidual.coordinates_contDiff n R V).differentiable (by norm_num) u
    rw [← norm_iteratedFDeriv_fderiv (n:=0),norm_iteratedFDeriv_zero] at hF hcoord ⊢
    rw [fderiv_comp u hdf hdc]
    have ht := (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul hF hcoord (norm_nonneg _) (by positivity))
    simp only [pow_one] at ht ⊢
    apply ht.trans
    have hscale : 0≤B*L*β := by positivity
    have he : (B*(L*β^2)/β)*(24*β/β)=24*(B*L*β) := by field_simp;ring
    rw [he]
    have he' : 100000*B*L*β^2/β=100000*(B*L*β) := by field_simp;ring
    rw [he']
    linarith only [hscale]

namespace Parameters
variable {X U : Type*}
  [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
variable (P : Parameters (X:=X) (U:=U))

def microFlatResidual (δ : ℝ) (i : Fin (P.macroNode.n+1)) (u : U) : ℝ :=
  flatResidual P.n P.L P.β δ (P.coordinates i u)

def selectedFlatResidual (δ : ℝ) (z : Joint X U) : ℝ :=
  ∑ i : Fin (P.macroNode.n+1),wrappedSelector P.macroNode i z.fst*P.microFlatResidual δ i z.snd

def residualDifference (δ : ℝ) : Joint X U → ℝ := P.selectedResidual-P.selectedFlatResidual δ

omit [CompleteSpace X] in
theorem microFlatResidual_contDiff (δ : ℝ) (i : Fin (P.macroNode.n+1)) :
    ContDiff ℝ 3 (P.microFlatResidual δ i) :=
  (flatResidual_contDiff P.n P.L P.β δ).comp (P.coordinates_contDiff i)

theorem selectedFlatResidual_contDiff (δ : ℝ) : ContDiff ℝ 3 (P.selectedFlatResidual δ) :=
  ContDiff.sum (fun i _ => ((wrappedSelector_contDiff P.macroNode i 3).comp
    (fstMap (X:=X) (U:=U)).contDiff).mul ((P.microFlatResidual_contDiff δ i).comp
      (sndMap (X:=X) (U:=U)).contDiff))

theorem residualDifference_contDiff (δ : ℝ) : ContDiff ℝ 3 (P.residualDifference δ) :=
  P.selectedResidual_contDiff.sub (P.selectedFlatResidual_contDiff δ)

end Parameters

theorem selected_flat_joint_c1_bounds : ∃ C : ℝ,1≤C ∧
    ∀ (X U : Type*) [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
      [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
      (P : Parameters (X:=X) (U:=U)) (δ : ℝ),
      0≤P.L → 0<P.β → 0<δ → δ≤P.β/16 → P.β≤P.radius →
      P.β≤P.macroNode.width → P.macroNode.width≤P.macroNode.radius →
      ∀ (z : Joint X U) k,k≤1 →
      ‖iteratedFDeriv ℝ k (P.selectedFlatResidual δ) z‖≤C*P.L*P.β^2/P.β^k := by
  obtain ⟨Cs,hCs,hs⟩ := joint_selector_jet_bounds
  obtain ⟨Cr,hCr,hr⟩ := wrapped_flat_c1_bounds
  have hCs0 : 0≤Cs := by linarith
  have hCr0 : 0≤Cr := by linarith
  refine ⟨8*Cs*Cr,by nlinarith [mul_le_mul hCs hCr zero_le_one hCs0],?_⟩
  intro X U _ _ _ _ _ _ P δ hL hβ hδ hδs hR hβb hbR z k hk
  change ‖iteratedFDeriv ℝ k (selected P.macroNode (P.microFlatResidual δ)) z‖≤_
  apply selected_jet_bound P.macroNode (P.microFlatResidual δ) (P.microFlatResidual_contDiff δ) z k (by omega) _ (by positivity)
  intro i
  have hsel (q : ℕ) (hq : q≤k) :
      ‖iteratedFDeriv ℝ q (jointSelector P.macroNode i) z‖≤Cs/P.β^q :=
    (hs X U P.macroNode (hβ.trans_le hβb) hbR i z q (by omega)).trans
      (div_le_div_of_nonneg_left hCs0 (pow_pos hβ _) (pow_le_pow_left₀ hβ.le hβb _))
  have hres (q : ℕ) (hq : q≤k) :
      ‖iteratedFDeriv ℝ q (fun y : Joint X U => P.microFlatResidual δ i y.snd) z‖≤(Cr*P.L*P.β^2)/P.β^q := by
    apply (ChiOuter.contraction_jet_bound (sndMap (X:=X) (U:=U)) sndMap_norm_le
      (P.microFlatResidual_contDiff δ i) z q (by omega)).trans
    exact hr U P.n q P.L P.β δ P.radius (by omega) hL hβ hδ hδs hR (P.frames i) z.snd
  have ht := ChiCarrier.same_width_product_jets (jointSelector_contDiff P.macroNode i)
    ((P.microFlatResidual_contDiff δ i).comp (sndMap (X:=X) (U:=U)).contDiff)
    Cs (Cr*P.L*P.β^2) P.β hCs0 (by positivity) hβ z k (by omega) hsel hres
  convert ht using 1
  ring

theorem selected_flat_error_bound : ∃ C : ℝ,0<C ∧
    ∀ (X U : Type*) [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
      [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
      (P : Parameters (X:=X) (U:=U)) (δ : ℝ),0≤P.L → 0<P.β → 0<δ → δ≤P.β/16 →
      ∀ z : Joint X U,|P.residualDifference δ z|≤C*P.L*P.β*δ := by
  let C := Real.exp 1*(Real.exp 1*(2*Real.sqrt (Real.exp 1)))
  have hC : 0<C := by dsimp [C];positivity
  refine ⟨C,hC,?_⟩
  intro X U _ _ _ _ _ _ P δ hL hβ hδ hs z
  have hres (i : Fin (P.macroNode.n+1)) :
      |P.microResidual i z.snd-P.microFlatResidual δ i z.snd|≤
        (Real.exp 1*(2*Real.sqrt (Real.exp 1)))*P.L*P.β*δ :=
    source_flattening_error P.n P.L P.β δ hL hβ hδ hs (P.coordinates i z.snd)
  change |P.selectedResidual z-P.selectedFlatResidual δ z|≤_
  simp only [Parameters.selectedResidual,Parameters.selectedFlatResidual,← Finset.sum_sub_distrib,← mul_sub]
  calc
    _≤∑ i : Fin (P.macroNode.n+1),|wrappedSelector P.macroNode i z.fst*
        (P.microResidual i z.snd-P.microFlatResidual δ i z.snd)| := Finset.abs_sum_le_sum_abs _ _
    _≤∑ i : Fin (P.macroNode.n+1),wrappedSelector P.macroNode i z.fst*
        ((Real.exp 1*(2*Real.sqrt (Real.exp 1)))*P.L*P.β*δ) := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul,abs_of_nonneg (wrappedSelector_range P.macroNode i z.fst).1]
      exact mul_le_mul_of_nonneg_left (hres i) (wrappedSelector_range P.macroNode i z.fst).1
    _=(∑ i : Fin (P.macroNode.n+1),wrappedSelector P.macroNode i z.fst)*
        ((Real.exp 1*(2*Real.sqrt (Real.exp 1)))*P.L*P.β*δ) := (Finset.sum_mul ..).symm
    _≤Real.exp 1*((Real.exp 1*(2*Real.sqrt (Real.exp 1)))*P.L*P.β*δ) :=
      mul_le_mul_of_nonneg_right (selector_sum_le_exp_one P.macroNode.n _) (by positivity)
    _=C*P.L*P.β*δ := by dsimp only [C];ring

end Bilevel.PolishedLiteral
