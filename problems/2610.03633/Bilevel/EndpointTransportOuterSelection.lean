import Bilevel.ChiOuterCarrierTransfer
import Bilevel.ChiLiftedLedger

/-! Actual one-sided macro selection on a heterogeneous ambient space.
The numerical bounds retain every mixed derivative and charge no factor
for the number of macro branches. -/
noncomputable section
open scoped BigOperators
namespace Bilevel.EndpointTransportResponse
open PrimitiveGeometry ChiBoundedChain ChiRecursive ChiCarrier ChiOuter
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

def macroLift (P : X →L[ℝ] E) : X →L[ℝ] Joint E (Blocks 0 ℝ) := packLinear.comp (P.prod 0)

omit [CompleteSpace E] in
theorem macroLift_norm (P : X →L[ℝ] E) (hP : ‖P‖≤1) : ‖macroLift P‖≤1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro x
  change ‖pack (P x) (0:Blocks 0 ℝ)‖≤1*‖x‖
  rw [norm_pack,norm_zero,zero_pow (by decide : (2:ℕ)≠0),add_zero,Real.sqrt_sq (norm_nonneg _)]
  exact (P.le_opNorm x).trans (mul_le_mul_of_nonneg_right hP (norm_nonneg _))

def macroSelector (M : Node E) (P : X →L[ℝ] E) (i : Fin (M.n+1)) : X → ℝ :=
  wrappedSelector M i ∘ P

theorem macroSelector_contDiff (M : Node E) (P : X →L[ℝ] E) (i : Fin (M.n+1)) :
    ContDiff ℝ 3 (macroSelector M P i) := (wrappedSelector_contDiff M i 3).comp P.contDiff

theorem macroSelector_jets_unique (M : Node E) (P : X →L[ℝ] E) (i l : Fin (M.n+1))
    (x : X) (k q : ℕ) (hk : k≤3) (hq : q≤3)
    (hi : iteratedFDeriv ℝ k (macroSelector M P i) x≠0)
    (hl : iteratedFDeriv ℝ q (macroSelector M P l) x≠0) : i=l :=
  jointOuterSelector_jets_unique (F:=ℝ) 0 M i l (macroLift P x) k q hk hq
    (linear_jet_nonzero (macroLift P) (jointOuterSelector_contDiff 0 M i) x k hk hi)
    (linear_jet_nonzero (macroLift P) (jointOuterSelector_contDiff 0 M l) x q hq hl)

def macroSelected (M : Node E) (P : X →L[ℝ] E) (f : Fin (M.n+1) → X → ℝ) (x : X) : ℝ :=
  ∑ i : Fin (M.n+1),macroSelector M P i x*f i x

theorem macroSelected_contDiff (M : Node E) (P : X →L[ℝ] E) (f : Fin (M.n+1) → X → ℝ)
    (hf : ∀ i,ContDiff ℝ 3 (f i)) : ContDiff ℝ 3 (macroSelected M P f) :=
  ContDiff.sum (fun i _ => (macroSelector_contDiff M P i).mul (hf i))

theorem macroSelected_sum_bound (M : Node E) (P : X →L[ℝ] E) (f : Fin (M.n+1) → X → ℝ)
    (hf : ∀ i,ContDiff ℝ 3 (f i)) (x : X) (k : ℕ) (hk : k≤3) (B : ℝ) (hB : 0≤B)
    (hb : ∀ i,‖iteratedFDeriv ℝ k (fun y => macroSelector M P i y*f i y) x‖≤B) :
    ‖iteratedFDeriv ℝ k (macroSelected M P f) x‖≤B := by
  rw [show macroSelected M P f=(fun y => ∑ i : Fin (M.n+1),macroSelector M P i y*f i y) from rfl,
    iteratedFDeriv_sum (fun i _ => ((macroSelector_contDiff M P i).mul (hf i)).of_le
      (show (k:WithTop ℕ∞)≤3 by exact_mod_cast hk))]
  simp only [Finset.sum_apply]
  apply norm_sum_le_of_exclusive _ B hB hb
  intro i l hil hi
  by_contra hl
  have hsel (a : Fin (M.n+1))
      (ha : iteratedFDeriv ℝ k (fun y => macroSelector M P a y*f a y) x≠0) :
      ∃ q≤k,iteratedFDeriv ℝ q (macroSelector M P a) x≠0 := by
    by_contra! hz
    exact ha (ZeroChainResidualBounds.jet_mul_zero_left (macroSelector_contDiff M P a) (hf a) x k hk hz)
  obtain ⟨a,ha,hai⟩ := hsel i hi
  obtain ⟨b,hb,hbl⟩ := hsel l hl
  exact hil (macroSelector_jets_unique M P i l x a b (by omega) (by omega) hai hbl)

theorem constructed_macro_carrier_step : ∃ Cs : ℝ,1≤Cs ∧
    ∀ (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
      (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X]
      (M : Node E) (P : X →L[ℝ] E),‖P‖≤1 → 0<M.width → M.width≤M.radius →
      ∀ (f : Fin (M.n+1) → X → ℝ),(∀ i,ContDiff ℝ 3 (f i)) →
      ∀ (B N ℓ h : ℝ),0≤B → 1≤N → 0≤ℓ → 0<h → h*Real.sqrt N≤M.width →
      ∀ (x : X) (k : ℕ),k≤3 →
      (∀ i q,q≤k → ‖iteratedFDeriv ℝ q (f i) x‖≤B*ledgerScale N ℓ h q) →
      ‖iteratedFDeriv ℝ k (macroSelected M P f) x‖≤Cs*B*ledgerScale N ℓ h k := by
  obtain ⟨C,hC,hs⟩ := constructed_outer_selector_jets
  have hC0 : 0≤C := by linarith
  refine ⟨8*C,by linarith,fun E _ _ _ X _ _ M P hP hh hhR f hf B N ℓ h hB hN hℓ hh0 hwidth x k hk hb => ?_⟩
  apply macroSelected_sum_bound M P f hf x k hk _
    (mul_nonneg (mul_nonneg (by positivity) hB) (ledgerScale_nonneg (by linarith) hℓ hh0.le k))
  intro i
  apply coarser_product_ledger (macroSelector_contDiff M P i) (hf i)
    C B N ℓ h M.width hC0 hB hN hℓ hh0 hh hwidth x k hk _ (hb i)
  intro q hq
  exact (linear_jet_contraction (macroLift P) (macroLift_norm P hP)
    (jointOuterSelector_contDiff (F:=ℝ) 0 M i) x q (by omega)).trans
      (hs E ℝ M hh hhR 0 i (macroLift P x) q (by omega))

theorem constructed_macro_fine_step : ∃ Cs : ℝ,1≤Cs ∧
    ∀ (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
      (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X]
      (M : Node E) (P : X →L[ℝ] E),‖P‖≤1 → 0<M.width → M.width≤M.radius →
      ∀ (f : Fin (M.n+1) → X → ℝ),(∀ i,ContDiff ℝ 3 (f i)) →
      ∀ (B a V δ : ℝ),0≤B → 0≤a → 0≤V → 0<δ → δ≤M.width → a≤V*M.width →
      ∀ (x : X) (k : ℕ),k≤3 →
      (∀ i q,q≤k → ‖iteratedFDeriv ℝ q (f i) x‖≤B*fineScale a V δ q) →
      ‖iteratedFDeriv ℝ k (macroSelected M P f) x‖≤Cs*B*fineScale a V δ k := by
  obtain ⟨C,hC,hs⟩ := constructed_outer_selector_jets
  have hC0 : 0≤C := by linarith
  refine ⟨8*C,by linarith,fun E _ _ _ X _ _ M P hP hh hhR f hf B a V δ hB ha hV hδ hδM haM x k hk hb => ?_⟩
  apply macroSelected_sum_bound M P f hf x k hk _
    (mul_nonneg (mul_nonneg (by positivity) hB) (fineScale_nonneg ha hV hδ.le k))
  intro i
  apply coarser_fine_product (macroSelector_contDiff M P i) (hf i)
    C B a V δ M.width hC0 hB ha hV hδ hh hδM haM x k hk _ (hb i)
  intro q hq
  exact (linear_jet_contraction (macroLift P) (macroLift_norm P hP)
    (jointOuterSelector_contDiff (F:=ℝ) 0 M i) x q (by omega)).trans
      (hs E ℝ M hh hhR 0 i (macroLift P x) q (by omega))

end Bilevel.EndpointTransportResponse
