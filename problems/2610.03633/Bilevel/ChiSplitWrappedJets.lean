import Bilevel.ChiSplitPayloadJets
import Bilevel.ChiBoundedChainWrappedJets

/-! Complete split-payload jets after a bounded endpoint readout and full-vector
radial compression. All constants are independent of ambient dimension. -/
noncomputable section
namespace Bilevel.ChiSplitChain
open ChiBoundedChain RadialWrapper
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem readout_compress_jet_le {n : ℕ} (P : E →L[ℝ] Latent n) (hp : ‖P‖≤3)
    (R : ℝ) (u : E) (k : ℕ) (hk : k≤3) :
    ‖iteratedFDeriv ℝ k (P ∘ compress R) u‖≤3*‖iteratedFDeriv ℝ k (compress (E:=E) R) u‖ := by
  rw [P.iteratedFDeriv_comp_left (compress_contDiff R 3).contDiffAt
    (show (k:WithTop ℕ∞)≤3 by exact_mod_cast hk)]
  exact (P.norm_compContinuousMultilinearMap_le _).trans
    (mul_le_mul_of_nonneg_right hp (norm_nonneg _))

theorem readout_compress_jets {n : ℕ} (P : E →L[ℝ] Latent n) (hp : ‖P‖≤3)
    (R : ℝ) (hR : 0<R) (u : E) :
    ‖iteratedFDeriv ℝ 1 (P ∘ compress R) u‖≤3 ∧
    ‖iteratedFDeriv ℝ 2 (P ∘ compress R) u‖≤12/R ∧
    ‖iteratedFDeriv ℝ 3 (P ∘ compress R) u‖≤72/R^2 := by
  have h1 := readout_compress_jet_le P hp R u 1 (by norm_num)
  have h2 := readout_compress_jet_le P hp R u 2 (by norm_num)
  have h3 := readout_compress_jet_le P hp R u 3 (by norm_num)
  have hc1 : ‖iteratedFDeriv ℝ 1 (compress (E:=E) R) u‖≤1 := by
    rw [Composition.norm_first,(compress_hasFDerivAt R u).fderiv]
    exact compressDerivative_opNorm_le R hR u
  have hc2 : ‖iteratedFDeriv ℝ 2 (compress (E:=E) R) u‖≤4/R := by
    rw [← norm_iteratedFDeriv_fderiv (n:=1),← norm_iteratedFDeriv_fderiv (n:=0),norm_iteratedFDeriv_zero]
    exact second_derivative_norm R hR u
  have hc3 : ‖iteratedFDeriv ℝ 3 (compress (E:=E) R) u‖≤24/R^2 := by
    rw [← norm_iteratedFDeriv_fderiv (n:=2),← norm_iteratedFDeriv_fderiv (n:=1),
      ← norm_iteratedFDeriv_fderiv (n:=0),norm_iteratedFDeriv_zero]
    exact third_derivative_norm R hR u
  refine ⟨h1.trans (by linarith only [hc1]),h2.trans ?_,h3.trans ?_⟩
  · calc
      _≤3*(4/R) := mul_le_mul_of_nonneg_left hc2 (by norm_num)
      _=12/R := by ring
  · calc
      _≤3*(24/R^2) := mul_le_mul_of_nonneg_left hc3 (by norm_num)
      _=72/R^2 := by ring

theorem carried_split_jets {n : ℕ} (f : Latent n → ℝ) (hf : ContDiff ℝ 3 f)
    (P : E →L[ℝ] Latent n) (hp : ‖P‖≤3) (G M₂ M₃ R : ℝ)
    (hG : 0≤G) (hM₂ : 0≤M₂) (hM₃ : 0≤M₃) (hR : 0<R)
    (hfirst : ∀ z,‖iteratedFDeriv ℝ 1 f z‖≤G)
    (hsecond : ∀ z,‖iteratedFDeriv ℝ 2 f z‖≤M₂)
    (hthird : ∀ z,‖iteratedFDeriv ℝ 3 f z‖≤M₃) (u : E) :
    ‖iteratedFDeriv ℝ 1 (f ∘ P ∘ compress R) u‖≤3*G ∧
    ‖iteratedFDeriv ℝ 2 (f ∘ P ∘ compress R) u‖≤9*M₂+12*G/R ∧
    ‖iteratedFDeriv ℝ 3 (f ∘ P ∘ compress R) u‖≤27*M₃+108*M₂/R+72*G/R^2 := by
  have hc := P.contDiff.comp (compress_contDiff R 3)
  have hz := readout_compress_jets P hp R hR u
  have h1 := Composition.first_comp_bound (g:=f) u (hc.differentiable (by norm_num) u)
    (hf.differentiable (by norm_num) _)
  have h2 := Composition.second_comp_bound
    (hc.of_le (by exact_mod_cast (show (2:ℕ)≤3 by omega)))
    (hf.of_le (by exact_mod_cast (show (2:ℕ)≤3 by omega))) u
  have h3 := Composition.third_comp_bound hc hf u
  refine ⟨h1.trans ?_,h2.trans ?_,h3.trans ?_⟩
  · calc
      _≤G*3 := by gcongr; exact hfirst _; exact hz.1
      _=3*G := by ring
  · calc
      _≤M₂*3^2+G*(12/R) := by gcongr; exact hsecond _; exact hz.1; exact hfirst _; exact hz.2.1
      _=_ := by ring
  · calc
      _≤M₃*3^3+3*M₂*3*(12/R)+G*(72/R^2) := by
        gcongr
        · exact hthird _
        · exact hz.1
        · exact hsecond _
        · exact hz.1
        · exact hz.2.1
        · exact hfirst _
        · exact hz.2.2
      _=_ := by ring

end Bilevel.ChiSplitChain
