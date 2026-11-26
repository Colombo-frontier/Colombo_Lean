import MinimaxAudit.Gate

/-!
Complete scalar jets and exact local transcript hiding for the manuscript's
actual gated scalar potential. The ambient space may carry any equivalent
finite-dimensional norm; no Euclidean diameter or smoothness bound is asserted
by this module. A strict interior plateau is used here, so a randomized proof
can take a slightly smaller slab threshold without altering its n^3 log n order.
-/
open Set Filter
open scoped Topology
namespace MinimaxAudit

abbrev ScalarJet (p : ℕ) (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  (k : Fin (p + 1)) → ContinuousMultilinearMap ℝ (fun _ : Fin k.1 => E) ℝ

noncomputable def exactScalarJet {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (p : ℕ) (f : E → ℝ) (z : E) : ScalarJet p E :=
  fun k => iteratedFDeriv ℝ k.1 f z

/-- All returned tensor orders, including order zero, agree under local equality. -/
theorem exactScalarJet_eq_of_eventuallyEq {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f g : E → ℝ} {z : E}
    (h : f =ᶠ[𝓝 z] g) (p : ℕ) : exactScalarJet p f z = exactScalarJet p g z := by
  funext k
  exact (h.iteratedFDeriv ℝ k.1).self_of_nhds

section Modules
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem scalarGate_module_eventually_zero (profile : GateProfile) {tau : ℝ}
    (htau : 0 < tau) (A B : E →L[ℝ] ℝ) {z : E}
    (h : |A z| + |B z| < tau / 2) :
    (fun w => scalarGate profile tau (A w) (B w)) =ᶠ[𝓝 z] (fun _ => 0) := by
  have hc : Continuous (fun w => |A w| + |B w|) := A.continuous.abs.add B.continuous.abs
  have he : ∀ᶠ w in 𝓝 z, |A w| + |B w| < tau / 2 :=
    hc.continuousAt.eventually (gt_mem_nhds h)
  filter_upwards [he] with w hw
  exact scalarGate_zero_core profile htau hw.le

theorem doubleGate_module_eventually_zero (profile : GateProfile) {tau : ℝ}
    (htau : 0 < tau) (A : E →L[ℝ] ℝ) {z : E} (h : |A z| < tau / 2) :
    (fun w => doubleGate profile tau (A w)) =ᶠ[𝓝 z] (fun _ => 0) := by
  have he : ∀ᶠ w in 𝓝 z, |A w| < tau / 2 :=
    A.continuous.abs.continuousAt.eventually (gt_mem_nhds h)
  filter_upwards [he] with w hw
  exact doubleGate_zero_core profile htau hw.le

/-- Paper chain of length n+1: module i uses a_i and b_(i+1). -/
noncomputable def chainPotential {n : ℕ} (profile : GateProfile)
    (tau lam c q : ℝ) (base : E → ℝ) (A B : Fin (n + 1) → E →L[ℝ] ℝ)
    (z : E) : ℝ :=
  lam * (base z - c * B 0 z - q *
    (∑ i : Fin n, scalarGate profile tau (A i.castSucc z) (B i.succ z)) -
    q * doubleGate profile tau (A (Fin.last n) z))

/-- Exact round truncation, without any unreturned coefficient data. -/
noncomputable def truncatedChainPotential {n : ℕ} (profile : GateProfile)
    (tau lam c q : ℝ) (base : E → ℝ) (A B : Fin (n + 1) → E →L[ℝ] ℝ)
    (revealed : Finset (Fin n)) (z : E) : ℝ :=
  lam * (base z - c * B 0 z - q *
    (∑ i ∈ revealed, scalarGate profile tau (A i.castSucc z) (B i.succ z)))

theorem chainPotential_eventually_eq_truncated {n : ℕ} (profile : GateProfile)
    {tau : ℝ} (htau : 0 < tau) (lam c q : ℝ) (base : E → ℝ)
    (A B : Fin (n + 1) → E →L[ℝ] ℝ) (revealed : Finset (Fin n)) {z : E}
    (hmodules : ∀ i : Fin n, i ∉ revealed →
      |A i.castSucc z| + |B i.succ z| < tau / 2)
    (hterminal : |A (Fin.last n) z| < tau / 2) :
    chainPotential profile tau lam c q base A B =ᶠ[𝓝 z]
      truncatedChainPotential profile tau lam c q base A B revealed := by
  have hm : ∀ i : Fin n, ∀ᶠ w in 𝓝 z,
      i ∉ revealed → scalarGate profile tau (A i.castSucc w) (B i.succ w) = 0 := by
    intro i
    by_cases hi : i ∈ revealed
    · exact Filter.Eventually.of_forall (fun _ hni => (hni hi).elim)
    · exact (scalarGate_module_eventually_zero profile htau
        (A i.castSucc) (B i.succ) (hmodules i hi)).mono (fun _ hw _ => hw)
  have hall : ∀ᶠ w in 𝓝 z, ∀ i : Fin n,
      i ∉ revealed → scalarGate profile tau (A i.castSucc w) (B i.succ w) = 0 :=
    Filter.eventually_all.mpr hm
  have ht := doubleGate_module_eventually_zero profile htau (A (Fin.last n)) hterminal
  filter_upwards [hall, ht] with w hw htw
  have hsum : (∑ i : Fin n, scalarGate profile tau (A i.castSucc w) (B i.succ w)) =
      ∑ i ∈ revealed, scalarGate profile tau (A i.castSucc w) (B i.succ w) := by
    symm
    exact Finset.sum_subset (Finset.subset_univ revealed) (fun i _ hi => hw i hi)
  simp [chainPotential, truncatedChainPotential, hsum, htw]

/-- Complete scalar jet equality for the concrete omitted-gate construction. -/
theorem chainPotential_exact_jet_eq_truncated {n : ℕ} (profile : GateProfile)
    {tau : ℝ} (htau : 0 < tau) (lam c q : ℝ) (base : E → ℝ)
    (A B : Fin (n + 1) → E →L[ℝ] ℝ) (revealed : Finset (Fin n)) {z : E}
    (hmodules : ∀ i : Fin n, i ∉ revealed →
      |A i.castSucc z| + |B i.succ z| < tau / 2)
    (hterminal : |A (Fin.last n) z| < tau / 2) (p : ℕ) :
    exactScalarJet p (chainPotential profile tau lam c q base A B) z =
      exactScalarJet p (truncatedChainPotential profile tau lam c q base A B revealed) z :=
  exactScalarJet_eq_of_eventuallyEq
    (chainPotential_eventually_eq_truncated profile htau lam c q base A B revealed
      hmodules hterminal) p

end Modules
end MinimaxAudit
