import Bilevel.PolishedLiteralMicroPieceBudgets
import Bilevel.PolishedLiteralSelection

/-! Full joint (x,u) budgets of the actual selected multiscale pieces.
Macro derivatives preserve the fine resolution scale and introduce no
condition-number or macro-stage factor. -/
noncomputable section
set_option maxHeartbeats 1000000
namespace Bilevel.PolishedLiteral
open ChiBoundedChain PrimitiveGeometry ZeroChainSchedule ZeroChainResidualBounds

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem mixed_piece_product_jets {f g : E → ℝ} (hf : ContDiff ℝ 3 f) (hg : ContDiff ℝ 3 g)
    (Cs D β d : ℝ) (hCs : 0≤Cs) (hD : 0≤D) (hβ : 0<β) (hd : 0<d) (hdβ : d≤β)
    (z : E) (k : ℕ) (hk0 : 1≤k) (hk : k≤3)
    (hsel : ∀ l,l≤k → ‖iteratedFDeriv ℝ l f z‖≤Cs/β^l)
    (hval : |g z|≤D*β)
    (hpos : ∀ l,1≤l → l≤k → ‖iteratedFDeriv ℝ l g z‖≤D/d^(l-1)) :
    ‖iteratedFDeriv ℝ k (fun y => f y*g y) z‖≤8*Cs*D/d^(k-1) := by
  let B : ℕ → ℝ := fun l => if l=0 then D*β else D/d^(l-1)
  have hB (l : ℕ) : 0≤B l := by dsimp [B];split_ifs <;> positivity
  have hgj (l : ℕ) (hl : l≤k) : ‖iteratedFDeriv ℝ l g z‖≤B l := by
    by_cases hl0 : l=0
    · subst l
      simpa only [B,if_pos rfl,norm_iteratedFDeriv_zero,Real.norm_eq_abs] using hval
    · simpa only [B,if_neg hl0] using hpos l (by omega) hl
  have ht (l : ℕ) (hl : l≤k) : (Cs/β^l)*B (k-l)≤Cs*D/d^(k-1) := by
    by_cases hzero : k-l=0
    · have hlk : l=k := by omega
      subst l
      obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k≠0)
      simp only [B,Nat.sub_self,if_pos rfl,Nat.succ_sub_one]
      calc
        (Cs/β^(m+1))*(D*β)=Cs*D/β^m := by rw [pow_succ];field_simp;ring
        _≤Cs*D/d^m := div_le_div_of_nonneg_left (mul_nonneg hCs hD) (pow_pos hd _)
          (pow_le_pow_left₀ hd.le hdβ _)
    · have hq : 0<k-l := by omega
      simp only [B,if_neg hzero]
      have hs := div_le_div_of_nonneg_left hCs (pow_pos hd l) (pow_le_pow_left₀ hd.le hdβ l)
      have he : l+(k-l-1)=k-1 := by omega
      calc
        (Cs/β^l)*(D/d^(k-l-1))≤(Cs/d^l)*(D/d^(k-l-1)) :=
          mul_le_mul_of_nonneg_right hs (by positivity)
        _=Cs*D/d^(k-1) := by rw [div_mul_div_comm,← pow_add,he]
  have hh := jet_mul_bound hf hg z k hk (fun l => Cs/β^l) B (fun l => by positivity) hsel hgj
  apply hh.trans
  calc
    (∑ l ∈ Finset.range (k+1),(k.choose l:ℝ)*(Cs/β^l)*B (k-l))≤
        ∑ l ∈ Finset.range (k+1),(k.choose l:ℝ)*(Cs*D/d^(k-1)) := by
      apply Finset.sum_le_sum
      intro l hl
      have ht' := mul_le_mul_of_nonneg_left (ht l (by have := Finset.mem_range.mp hl;omega))
        (show 0≤(k.choose l:ℝ) by positivity)
      convert ht' using 1
      ring
    _≤8*Cs*D/d^(k-1) := by
      have hsum : (∑ l ∈ Finset.range (k+1),(k.choose l:ℝ))≤8 := by
        interval_cases k <;> norm_num [Finset.sum_range_succ]
      have ht := mul_le_mul_of_nonneg_right hsum
        (show 0≤Cs*D/d^(k-1) by positivity)
      rw [Finset.sum_mul] at ht
      convert ht using 1
      ring


/-- The manuscript's joint piece budgets, with no macro-stage count and
no extra factor of kappa. All assumptions specify source scales/widths. -/
theorem actual_selected_piece_budgets : ∃ C : ℝ,1≤C ∧
    ∀ (X U : Type*) [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
      [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
      (P : Parameters (X:=X) (U:=U)) (c θ : ℝ),
      0<c → c≤1/16 → 1≤θ → 0≤P.L → 0<P.β → P.β≤P.radius →
      P.β≤P.macroNode.width → P.macroNode.width≤P.macroNode.radius →
      P.J=levels θ → P.δ=resolution c P.β θ →
      ∀ j,j≤levels θ → ∀ z : Joint X U,
      |P.selectedPiece j z|≤C*(P.L*P.β^2)*θ^(-amplitudeExponent j) ∧
      ∀ k : Fin 3,‖iteratedFDeriv ℝ (k.val+1) (P.selectedPiece j) z‖≤
        C*(P.L*P.β^2)/(P.β*(pieceResolution c P.β θ j)^k.val) := by
  obtain ⟨Cs,hCs,hs⟩ := joint_selector_jet_bounds
  obtain ⟨Cm,hCm,hm⟩ := actual_micro_piece_budgets
  let C := Real.exp 1*Cm+8*Cs*Cm+1
  have hCs0 : 0≤Cs := by linarith
  have hCm0 : 0≤Cm := by linarith
  have heCm : 0≤Real.exp 1*Cm := by positivity
  have hpCm : 0≤8*Cs*Cm := by positivity
  have hC : 1≤C := by dsimp [C];linarith
  have hCe : Real.exp 1*Cm≤C := by dsimp [C];linarith
  have hCmixed : 8*Cs*Cm≤C := by dsimp [C];linarith
  refine ⟨C,hC,?_⟩
  intro X U _ _ _ _ _ _ P c θ hc hcs hθ hL hβ hR hβb hbR hJ hδ j hj z
  have hbm := hm X U P c θ hc hcs hθ hL hβ hR hJ hδ
  have hamp : 0≤amplitudeExponent j := by
    unfold amplitudeExponent
    split_ifs
    · exact le_rfl
    · exact aExponent_nonneg _
  have ht0 : 0≤θ^(-amplitudeExponent j) := Real.rpow_nonneg (by linarith) _
  have ht1 : θ^(-amplitudeExponent j)≤1 := Real.rpow_le_one_of_one_le_of_nonpos hθ (neg_nonpos.mpr hamp)
  let d := pieceResolution c P.β θ j
  have hd : 0<d := pieceResolution_pos c P.β θ hc hβ hθ j
  have hdβ : d≤P.β := (pieceResolution_le c P.β θ hc.le hβ.le hθ j hj).trans
    (by nlinarith [mul_le_mul_of_nonneg_right hcs hβ.le])
  have hsel (i : Fin (P.macroNode.n+1)) (q : ℕ) (hq : q≤3) :
      ‖iteratedFDeriv ℝ q (jointSelector (U:=U) P.macroNode i) z‖≤Cs/P.β^q :=
    (hs X U P.macroNode (hβ.trans_le hβb) hbR i z q hq).trans
      (div_le_div_of_nonneg_left hCs0 (pow_pos hβ _) (pow_le_pow_left₀ hβ.le hβb _))
  have htermval (i : Fin (P.macroNode.n+1)) :
      |jointSelector P.macroNode i z*P.microPiece i j z.snd|≤
        (Real.exp 1*Cm)*(P.L*P.β^2)*θ^(-amplitudeExponent j) := by
    change |wrappedSelector P.macroNode i z.fst*P.microPiece i j z.snd|≤_
    rw [abs_mul,abs_of_nonneg (wrappedSelector_range P.macroNode i z.fst).1]
    have ht := mul_le_mul (wrappedSelector_range P.macroNode i z.fst).2
      (hbm i j hj z.snd).1 (abs_nonneg _) (Real.exp_pos _).le
    exact ht.trans_eq (by ring)
  constructor
  · have ht := selected_jet_bound P.macroNode (fun i => P.microPiece i j)
      (fun i => P.microPiece_contDiff i j) z 0 (by norm_num)
      ((Real.exp 1*Cm)*(P.L*P.β^2)*θ^(-amplitudeExponent j)) (by positivity)
      (fun i => by simpa only [norm_iteratedFDeriv_zero,Real.norm_eq_abs] using htermval i)
    have hscale := mul_le_mul_of_nonneg_right hCe (mul_nonneg (mul_nonneg hL (sq_nonneg P.β)) ht0)
    change ‖iteratedFDeriv ℝ 0 (selected P.macroNode (fun i => P.microPiece i j)) z‖≤_ at ht
    simp only [norm_iteratedFDeriv_zero,Real.norm_eq_abs] at ht
    exact ht.trans (by nlinarith only [hscale])
  · intro k
    let D := Cm*(P.L*P.β)
    have hD : 0≤D := by dsimp [D];positivity
    have hproduct (i : Fin (P.macroNode.n+1)) :
        ‖iteratedFDeriv ℝ (k.val+1) (fun y : Joint X U =>
          jointSelector P.macroNode i y*P.microPiece i j y.snd) z‖≤8*Cs*D/d^k.val := by
      have hg : ContDiff ℝ 3 (fun y : Joint X U => P.microPiece i j y.snd) :=
        (P.microPiece_contDiff i j).comp (sndMap (X:=X) (U:=U)).contDiff
      have hv := (hbm i j hj z.snd).1
      have hv' : |P.microPiece i j z.snd|≤D*P.β := by
        have hbamp := mul_le_mul_of_nonneg_left ht1
          (show 0≤Cm*(P.L*P.β^2) by positivity)
        dsimp only [D]
        nlinarith only [hv,hbamp]
      have hp (q : ℕ) (hq0 : 1≤q) (hq : q≤k.val+1) :
          ‖iteratedFDeriv ℝ q (fun y : Joint X U => P.microPiece i j y.snd) z‖≤D/d^(q-1) := by
        have ht := ChiOuter.contraction_jet_bound (sndMap (X:=X) (U:=U)) sndMap_norm_le
          (P.microPiece_contDiff i j) z q (by omega)
        have hbq := (hbm i j hj z.snd).2 ⟨q-1,by omega⟩
        have heq : q-1+1=q := by omega
        dsimp only at hbq
        rw [heq] at hbq
        apply ht.trans (hbq.trans_eq ?_)
        dsimp only [D,d]
        field_simp
        ring
      have ht := mixed_piece_product_jets (jointSelector_contDiff P.macroNode i) hg
        Cs D P.β d hCs0 hD hβ hd hdβ z (k.val+1) (by omega) (by omega)
        (fun q hq => hsel i q (by omega)) hv' hp
      simpa only [Nat.add_sub_cancel] using ht
    have ht := selected_jet_bound P.macroNode (fun i => P.microPiece i j)
      (fun i => P.microPiece_contDiff i j) z (k.val+1) (by omega)
      (8*Cs*D/d^k.val) (by positivity) hproduct
    have hscale := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hCmixed (mul_nonneg hL hβ.le)) (pow_nonneg hd.le k.val)
    apply ht.trans
    dsimp only [D,d]
    convert hscale using 1 <;> field_simp
    all_goals ring

end Bilevel.PolishedLiteral
