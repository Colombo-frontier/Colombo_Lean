import Bilevel.ChiOuterCarrierFineCoupling

/-! A transparent product-rule interface for the fixed fine signal. The
separate source ledger will discharge the input jets for the actual signal. -/
noncomputable section
namespace Bilevel.ChiFine
open ChiCarrier CompensatedMean SmallGapLiftSupport
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem signal_extension_jets {f : E → ℝ} (hf : ContDiff ℝ 3 f)
    {B M W : ℝ} (hB : 0≤B) (hM : 0≤M) (hW : 0<W)
    (hb : ∀ x k,k≤3 → ‖iteratedFDeriv ℝ k f x‖≤B*fineScale (M*(W/8)) M (W/8) k)
    (y : LowerSpace E) :
    ‖iteratedFDeriv ℝ 1 (ChiCoarse.extension f W) y‖≤2*C*B*M*W ∧
    ‖iteratedFDeriv ℝ 2 (ChiCoarse.extension f W) y‖≤11*C*B*M ∧
    ‖iteratedFDeriv ℝ 3 (ChiCoarse.extension f W) y‖≤92*C*B*M/W := by
  have hC := C_pos
  have h0 : |f (uProj E y)|≤B*(M*(W/8)) := by
    simpa only [fineScale,norm_iteratedFDeriv_zero,Real.norm_eq_abs] using hb (uProj E y) 0 (by norm_num)
  have h1 : ‖iteratedFDeriv ℝ 1 f (uProj E y)‖≤B*M := by
    simpa only [fineScale,pow_zero,div_one] using hb (uProj E y) 1 (by norm_num)
  have h2 : ‖iteratedFDeriv ℝ 2 f (uProj E y)‖≤B*M/(W/8) := by
    exact (hb (uProj E y) 2 (by norm_num)).trans_eq (by simp only [fineScale,pow_one];ring)
  have h3 : ‖iteratedFDeriv ℝ 3 f (uProj E y)‖≤B*M/(W/8)^2 := by
    exact (hb (uProj E y) 3 (by norm_num)).trans_eq (by simp only [fineScale];ring)
  let D := ChiCoarse.singleData f hf W hW
  have hs1 := ChiCoarse.extension_first_jet hf hW (by positivity) (by positivity) y h0 h1
  have hs2 := D.couplingTerm_second_bound 0 (by simp [D,ChiCoarse.singleData]) y
    (B*(M*(W/8))) (B*M) (B*M/(W/8)) (by positivity) (by positivity) (by positivity) h0 h1 h2
  have hs3 := D.couplingTerm_third_bound 0 (by simp [D,ChiCoarse.singleData]) y
    (B*(M*(W/8))) (B*M) (B*M/(W/8)) (B*M/(W/8)^2)
    (by positivity) (by positivity) (by positivity) (by positivity) h0 h1 h2 h3
  change _≤C*(B*(M*(W/8))/W+2*(B*M)+(B*M/(W/8))*W) at hs2
  change _≤C*(B*(M*(W/8))/W^2+3*(B*M)/W+3*(B*M/(W/8))+(B*M/(W/8)^2)*W) at hs3
  have he2 : C*(B*(M*(W/8))/W+2*(B*M)+(B*M/(W/8))*W)=(81/8:ℝ)*C*B*M := by
    field_simp
    ring
  have he3 : C*(B*(M*(W/8))/W^2+3*(B*M)/W+3*(B*M/(W/8))+(B*M/(W/8)^2)*W)=
      (729/8:ℝ)*(C*B*M/W) := by field_simp;ring
  refine ⟨hs1.trans ?_,hs2.trans ?_,hs3.trans ?_⟩
  · nlinarith only [show 0≤C*B*M*W by positivity]
  · rw [he2]
    nlinarith only [show 0≤C*B*M by positivity]
  · rw [he3]
    calc
      _ ≤ 92*(C*B*M/W) := by nlinarith only [show 0≤C*B*M/W by positivity]
      _ = _ := by ring

theorem signal_normal_jets {f : E → ℝ} (hf : ContDiff ℝ 3 f)
    {B M W : ℝ} (hB : 0≤B) (hM : 0≤M) (hW : 0<W)
    (hb : ∀ x k,k≤3 → ‖iteratedFDeriv ℝ k f x‖≤B*fineScale (M*(W/8)) M (W/8) k)
    (s : ℕ) (i : Fin s) (z : ChiExtension.Full E s) :
    ‖iteratedFDeriv ℝ 1 (ChiExtension.normalTerm s i f W) z‖≤2*C*B*M*W ∧
    ‖iteratedFDeriv ℝ 2 (ChiExtension.normalTerm s i f W) z‖≤11*C*B*M ∧
    ‖iteratedFDeriv ℝ 3 (ChiExtension.normalTerm s i f W) z‖≤92*C*B*M/W := by
  have hs := signal_extension_jets hf hB hM hW hb (ChiExtension.normalSlice s i z)
  have hc (k : ℕ) (hk : k≤3) := ChiExtension.contraction_jet
    (ChiCoarse.extension_contDiff hf hW) (ChiExtension.normalSlice s i)
    (ChiExtension.normalSlice_norm_le (E:=E) s i) z k hk
  exact ⟨(hc 1 (by norm_num)).trans hs.1,(hc 2 (by norm_num)).trans hs.2.1,
    (hc 3 (by norm_num)).trans hs.2.2⟩

end Bilevel.ChiFine
