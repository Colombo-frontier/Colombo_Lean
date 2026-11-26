import Bilevel.ChiCarrierSourceNode
import Bilevel.ChiCarrierReleaseJets

/-! The four-order carrier envelope is stable under multiplication by a
coarser selector. This isolates the elementary scale argument in the source. -/
noncomputable section
open scoped BigOperators
namespace Bilevel.ChiCarrier
open ChiBoundedChain ChiRecursive

theorem ledgerScale_step {N ℓ h d : ℝ} (hN : 1≤N) (hℓ : 0≤ℓ) (hh : 0<h)
    (hd : 0<d) (hwidth : h*Real.sqrt N≤d) (s : ℕ) (hs : s≤2) :
    ledgerScale N ℓ h s/d≤ledgerScale N ℓ h (s+1) := by
  have hN0 : 0≤N := by linarith
  have hsq := Real.sq_sqrt hN0
  have hsqrt : 1≤Real.sqrt N := Real.one_le_sqrt.mpr hN
  have hhd : h≤d := by nlinarith only [mul_le_mul_of_nonneg_left hsqrt hh.le,hwidth]
  interval_cases s
  · apply (div_le_iff₀ hd).mpr
    change N*ℓ*h^2≤(ℓ*h*Real.sqrt N)*d
    calc
      _ = (ℓ*h^2)*(Real.sqrt N)^2 := by rw [hsq];ring
      _ = (ℓ*h*Real.sqrt N)*(h*Real.sqrt N) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hwidth (by positivity)
  · apply (div_le_iff₀ hd).mpr
    change ℓ*h*Real.sqrt N≤ℓ*d
    nlinarith only [mul_le_mul_of_nonneg_left hwidth hℓ]
  · exact div_le_div_of_nonneg_left hℓ hh hhd

theorem ledgerScale_div_pow {N ℓ h d : ℝ} (hN : 1≤N) (hℓ : 0≤ℓ) (hh : 0<h)
    (hd : 0<d) (hwidth : h*Real.sqrt N≤d) (s q : ℕ) (hsq : s+q≤3) :
    ledgerScale N ℓ h s/d^q≤ledgerScale N ℓ h (s+q) := by
  induction q with
  | zero => simp
  | succ q ih =>
    calc
      _ = (ledgerScale N ℓ h s/d^q)/d := by rw [pow_succ];ring
      _ ≤ ledgerScale N ℓ h (s+q)/d := div_le_div_of_nonneg_right (ih (by omega)) hd.le
      _ ≤ _ := ledgerScale_step hN hℓ hh hd hwidth (s+q) (by omega)

theorem coarser_product_ledger {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {f g : X → ℝ} (hf : ContDiff ℝ 3 f) (hg : ContDiff ℝ 3 g)
    (Cs Cg N ℓ h d : ℝ) (hCs : 0≤Cs) (hCg : 0≤Cg) (hN : 1≤N) (hℓ : 0≤ℓ)
    (hh : 0<h) (hd : 0<d) (hwidth : h*Real.sqrt N≤d) (x : X) (k : ℕ) (hk : k≤3)
    (hsel : ∀ q,q≤k → ‖iteratedFDeriv ℝ q f x‖≤Cs/d^q)
    (hcore : ∀ q,q≤k → ‖iteratedFDeriv ℝ q g x‖≤Cg*ledgerScale N ℓ h q) :
    ‖iteratedFDeriv ℝ k (fun y => f y*g y) x‖≤8*Cs*Cg*ledgerScale N ℓ h k := by
  have hs := ZeroChainResidualBounds.jet_mul_bound hf hg x k hk
    (fun q => Cs/d^q) (fun q => Cg*ledgerScale N ℓ h q) (fun _ => by positivity) hsel hcore
  have hsum : (∑ q ∈ Finset.range (k+1),(k.choose q:ℝ))≤8 := by
    interval_cases k <;> norm_num [Finset.sum_range_succ]
  have hSk : 0≤ledgerScale N ℓ h k := ledgerScale_nonneg (by linarith) hℓ hh.le k
  calc
    _ ≤ ∑ q ∈ Finset.range (k+1),(k.choose q:ℝ)*(Cs/d^q)*(Cg*ledgerScale N ℓ h (k-q)) := hs
    _ ≤ ∑ q ∈ Finset.range (k+1),(k.choose q:ℝ)*(Cs*Cg*ledgerScale N ℓ h k) := by
      apply Finset.sum_le_sum
      intro q hq
      have hqk : q≤k := by have := Finset.mem_range.mp hq;omega
      have hscale := ledgerScale_div_pow hN hℓ hh hd hwidth (k-q) q (by omega)
      have he : k-q+q=k := Nat.sub_add_cancel hqk
      rw [he] at hscale
      have hh' := mul_le_mul_of_nonneg_left hscale (show 0≤(k.choose q:ℝ)*(Cs*Cg) by positivity)
      convert hh' using 1 <;> ring
    _ = (∑ q ∈ Finset.range (k+1),(k.choose q:ℝ))*(Cs*Cg*ledgerScale N ℓ h k) :=
      (Finset.sum_mul ..).symm
    _ ≤ 8*(Cs*Cg*ledgerScale N ℓ h k) := mul_le_mul_of_nonneg_right hsum (by positivity)
    _ = _ := by ring

/-- A genuine recursive transfer step: all selector derivative and overlap
premises are discharged by the actual node construction. Bounds on children
are the induction hypothesis, kept explicit at this intermediate lemma. -/
theorem constructed_selected_ledger_step : ∃ Cs : ℝ,1≤Cs ∧
    ∀ (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
      (D : Node F),0≤D.ell → 0<D.width → D.width≤D.radius → 0<D.parentWidth → D.parentWidth≤D.radius →
      ∀ (m j : ℕ) (f : Fin (D.n+1) → Blocks m F → ℝ),
      (∀ i,ContDiff ℝ 3 (f i)) → ∀ (Cg N ℓ h : ℝ),0≤Cg → 1≤N → 0≤ℓ → 0<h →
      h*Real.sqrt N≤D.width → ∀ (x : Blocks m F) (k : ℕ),k≤3 →
      (∀ i q,q≤k → ‖iteratedFDeriv ℝ q (f i) x‖≤Cg*ledgerScale N ℓ h q) →
      ‖iteratedFDeriv ℝ k (fun y => ∑ i : Fin (D.n+1),jointSelector m j D i y*f i y) x‖≤
        Cs*Cg*ledgerScale N ℓ h k := by
  obtain ⟨C,hC,hb⟩ := constructed_joint_node_jets
  have hC0 : 0≤C := by linarith
  refine ⟨8*C,by linarith,fun F _ _ _ D hell hh hhR hhp hhpR m j f hf Cg N ℓ h hCg hN hℓ hwidth0
    hwidth x k hk hcore => ?_⟩
  apply selected_products_jet_bound m j D f hf x k hk _
    (mul_nonneg (mul_nonneg (by positivity) hCg) (ledgerScale_nonneg (by linarith) hℓ hwidth0.le k))
  intro i
  exact coarser_product_ledger (jointSelector_contDiff m j D i 3) (hf i)
    C Cg N ℓ h D.width hC0 hCg hN hℓ hwidth0 hh hwidth x k hk
    (fun q hq => (hb F D hell hh hhR hhp hhpR m j i x q (by omega)).1)
    (fun q hq => hcore i q hq)

end Bilevel.ChiCarrier
