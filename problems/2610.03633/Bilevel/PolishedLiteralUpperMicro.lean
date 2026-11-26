import Bilevel.PolishedLiteralUpperRadial
import Bilevel.PolishedLiteralValueBounds
import Bilevel.PolishedLiteralMicro
import Bilevel.ChiBoundedChainReceiverJetBounds

/-! Actual value, first derivative and Hessian budgets of the literal
micro core. The receiver is exactly the positive receiver in the paper. -/
noncomputable section
set_option maxHeartbeats 1000000
namespace Bilevel.PolishedLiteral
open ChiBoundedChain ZeroChainPotential RadialWrapper

def rawCore (n : ℕ) (L β A ν b : ℝ) (z : Space n) : ℝ :=
  chain n L β z+positiveReceiver A ν (L*β) β b (z (Fin.last n))

theorem rawCore_contDiff (n k : ℕ) (L β A ν b : ℝ) :
    ContDiff ℝ k (rawCore n L β A ν b) :=
  (chain_contDiff n L β k).add ((positiveReceiver_contDiff A ν (L*β) β b k).comp
    (EuclideanSpace.proj (𝕜:=ℝ) (Fin.last n)).contDiff)

theorem rawCore_gradient (n : ℕ) (L β A ν b : ℝ) (z : Space n) :
    gradient (rawCore n L β A ν b) z=gradient (chain n L β) z+
      positiveReceiverSlope A ν (L*β) β b (z (Fin.last n)) • basis (Fin.last n) := by
  have he : rawCore n L β A ν b=microLatent n L β A ν (L*β) b 1 0 := by
    funext y
    simp only [rawCore,microLatent,one_mul,zero_mul,add_zero]
  rw [he,microLatent_gradient]
  simp only [one_smul,one_mul,releaseCoefficient,zero_mul,zero_div,add_zero]

theorem rawCore_gradient_bound (Cg : ℝ)
    (hchain : ∀ (n : ℕ) (L β : ℝ),0≤L → 0<β → ∀ z : Space n,
      ‖gradient (chain n L β) z‖≤Cg*(L*β)*Real.sqrt ((n:ℝ)+1))
    (n : ℕ) (L β A ν b : ℝ) (hL : 0≤L) (hβ : 0<β) (hA : 0≤A)
    (hν : 0≤ν) (hb : 0<b) (z : Space n) :
    ‖gradient (rawCore n L β A ν b) z‖≤
      Cg*(L*β)*Real.sqrt ((n:ℝ)+1)+A*(3*ν*b+L*β) := by
  rw [rawCore_gradient]
  have hd := positiveReceiverSlope_abs_bound A ν (L*β) β b (z (Fin.last n))
    hA hν (by positivity) hβ hb
  have ht : ‖positiveReceiverSlope A ν (L*β) β b (z (Fin.last n)) • basis (Fin.last n)‖≤
      A*(3*ν*b+L*β) := by
    simpa only [norm_smul,Real.norm_eq_abs,basis,EuclideanSpace.norm_single,norm_one,mul_one] using hd
  exact (norm_add_le _ _).trans (add_le_add (hchain n L β hL hβ z) ht)

theorem rawCore_second_uniform : ∃ Ch Dr : ℝ,0≤Ch ∧ 0≤Dr ∧
    ∀ (n : ℕ) (L β A ν b : ℝ),0<L → 0<β → 0≤A → 0≤ν → ν≤L → β≤b →
      ∀ z : Space n,‖iteratedFDeriv ℝ 2 (rawCore n L β A ν b) z‖≤(Ch+Dr*A)*L := by
  obtain ⟨Ch,hCh,hchain⟩ := Regularity.chain_jet_two_uniform
  obtain ⟨Dr,hDr,hd⟩ := ReceiverJets.receiver_source_derivatives
  refine ⟨Ch,Dr,hCh,hDr,fun n L β A ν b hL hβ hA hν hνL hβb z => ?_⟩
  have hb : 0<b := hβ.trans_le hβb
  let p := EuclideanSpace.proj (𝕜:=ℝ) (Fin.last n)
  have hpos := (hd A ν L β b β hA hν hL hβ hb hβ hνL hβb le_rfl (z (Fin.last n))).1
  have hp := ZeroChainResidualBounds.scalar_linear_jet_bound
    (positiveReceiver_contDiff A ν (L*β) β b 3) p
    (ZeroChainResidualBounds.projection_norm_le _) z 2 (by norm_num)
    (Dr*A*L) (by positivity) hpos
  change ‖iteratedFDeriv ℝ 2 (fun w => chain n L β w+(positiveReceiver A ν (L*β) β b ∘ p) w) z‖≤_
  have h23 : (2:WithTop ℕ∞)≤3 := by exact_mod_cast (show (2:ℕ)≤3 by omega)
  rw [iteratedFDeriv_add_apply' ((chain_contDiff n L β 3).of_le h23).contDiffAt
    (((positiveReceiver_contDiff A ν (L*β) β b 3).comp p.contDiff).of_le h23).contDiffAt]
  exact (norm_add_le _ _).trans ((add_le_add (hchain n L β hL.le hβ z) hp).trans_eq (by ring))

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem carried_first_second {n : ℕ} (f : Space n → ℝ) (hf : ContDiff ℝ 3 f)
    (G H R : ℝ) (hG : 0≤G) (hH : 0≤H) (hR : 0<R)
    (hg : ∀ z,‖gradient f z‖≤G) (hh : ∀ z,‖iteratedFDeriv ℝ 2 f z‖≤H)
    (V : Space n →ₗᵢ[ℝ] E) (u : E) :
    ‖iteratedFDeriv ℝ 1 (f ∘ WrappedChain.coordinates n R V) u‖≤G ∧
    ‖iteratedFDeriv ℝ 2 (f ∘ WrappedChain.coordinates n R V) u‖≤H+4*G/R := by
  have hc := ZeroChainWrappedResidual.coordinates_contDiff n R V
  have hz := frame_coordinates_jets n R hR V u
  have hfirst : ‖iteratedFDeriv ℝ 1 f (WrappedChain.coordinates n R V u)‖≤G := by
    rw [Composition.norm_first,← GradientJetBounds.gradient_norm_eq]
    exact hg _
  constructor
  · apply (Composition.first_comp_bound u (hc.differentiable (by norm_num) u)
      (hf.differentiable (by norm_num) _)).trans
    calc
      _ ≤ G*1 := by gcongr;exact hz.1
      _ = G := mul_one _
  · have h23 : (2:WithTop ℕ∞)≤3 := by exact_mod_cast (show (2:ℕ)≤3 by omega)
    apply (Composition.second_comp_bound (hc.of_le h23) (hf.of_le h23) u).trans
    calc
      _ ≤ H*1^2+G*(4/R) := by gcongr;exact hh _;exact hz.1;exact hz.2.1
      _ = H+4*G/R := by ring

theorem wrapped_core_first_second : ∃ Cg Ch Dr : ℝ,0≤Cg ∧ 0≤Ch ∧ 0≤Dr ∧
    ∀ (n : ℕ) (L β A ν b R : ℝ),0<L → 0<β → 0≤A → 0≤ν → ν≤L →
      β≤b → b≤R → β*Real.sqrt ((n:ℝ)+1)≤b →
      ∀ (V : Space n →ₗᵢ[ℝ] E) (u : E),
        ‖iteratedFDeriv ℝ 1 (rawCore n L β A ν b ∘ WrappedChain.coordinates n R V) u‖≤(Cg+4*A)*L*b ∧
        ‖iteratedFDeriv ℝ 2 (rawCore n L β A ν b ∘ WrappedChain.coordinates n R V) u‖≤
          (Ch+Dr*A+4*(Cg+4*A))*L := by
  obtain ⟨Cg,hCg,hg⟩ := chain_gradient_norm_uniform
  obtain ⟨Ch,Dr,hCh,hDr,hh⟩ := rawCore_second_uniform
  refine ⟨Cg,Ch,Dr,hCg,hCh,hDr,fun n L β A ν b R hL hβ hA hν hνL hβb hbR hwidth V u => ?_⟩
  have hb : 0<b := hβ.trans_le hβb
  have hR : 0<R := hb.trans_le hbR
  let G := (Cg+4*A)*L*b
  let H := (Ch+Dr*A)*L
  have hG : 0≤G := by dsimp [G];positivity
  have hH : 0≤H := by dsimp [H];positivity
  have hgrad (z : Space n) : ‖gradient (rawCore n L β A ν b) z‖≤G := by
    apply (rawCore_gradient_bound Cg hg n L β A ν b hL.le hβ hA hν hb z).trans
    have hchain := mul_le_mul_of_nonneg_left hwidth (mul_nonneg hCg hL.le)
    have hn := mul_le_mul_of_nonneg_right hνL hb.le
    have hβ' := mul_le_mul_of_nonneg_left hβb hL.le
    have hrec := mul_le_mul_of_nonneg_left (show 3*ν*b+L*β≤4*L*b by linarith) hA
    dsimp [G]
    nlinarith only [hchain,hrec]
  have ht := carried_first_second (rawCore n L β A ν b) (rawCore_contDiff n 3 L β A ν b)
    G H R hG hH hR hgrad (hh n L β A ν b hL hβ hA hν hνL hβb) V u
  have hratio : G/R≤(Cg+4*A)*L := (div_le_iff₀ hR).mpr
    (mul_le_mul_of_nonneg_left hbR (by positivity))
  refine ⟨ht.1,ht.2.trans ?_⟩
  rw [show 4*G/R=4*(G/R) by ring]
  dsimp only [H]
  nlinarith only [hratio]

theorem wrapped_core_value : ∃ C : ℝ,0≤C ∧
    ∀ (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
      (n : ℕ) (L β A ν b R Cr : ℝ),0<L → 0<β → 0≤A → 0≤ν → ν≤L →
      β≤b → 0<R → R≤Cr*b → β*Real.sqrt ((n:ℝ)+1)≤b →
      ∀ (V : Space n →ₗᵢ[ℝ] F) (u : F),
        |rawCore n L β A ν b (WrappedChain.coordinates n R V u)|≤
          (phi 0+C*Cr+12*A)*(L*b^2) := by
  obtain ⟨C,hC,hchain⟩ := chain_value_control
  refine ⟨C,hC,fun F _ _ _ n L β A ν b R Cr hL hβ hA hν hνL hβb hR hRb hwidth V u => ?_⟩
  let z := WrappedChain.coordinates n R V u
  have hb : 0<b := hβ.trans_le hβb
  have hz : ‖z‖≤R := (frame_adjoint_norm_le V _).trans (compress_norm_le_radius R hR u)
  have hc := hchain n L β hL.le hβ z
  have hrec := positiveReceiver_abs_bound A ν (L*β) β b (z (Fin.last n))
    hA hν (by positivity) hβ hb
  have hνb := mul_le_mul_of_nonneg_right hνL hb.le
  have hLb := mul_le_mul_of_nonneg_left hβb hL.le
  have hrec' := mul_le_mul_of_nonneg_left
    (show 3*ν*b+L*β≤4*L*b by linarith only [hνb,hLb]) (show 0≤A*(3*b) by positivity)
  have hs := mul_le_mul hwidth (hz.trans hRb) (norm_nonneg _) hb.le
  have hs' := mul_le_mul_of_nonneg_left hs (mul_nonneg hC hL.le)
  have hβsq : β^2≤b^2 := pow_le_pow_left₀ hβ.le hβb 2
  have hbase := mul_le_mul_of_nonneg_left hβsq (mul_nonneg hL.le (phi_nonneg 0))
  have habs := abs_add (chain n L β z) (positiveReceiver A ν (L*β) β b (z (Fin.last n)))
  change |rawCore n L β A ν b z|≤_
  dsimp only [rawCore]
  nlinarith only [hc,hrec,hrec',hs',hbase,habs]

end Bilevel.PolishedLiteral
