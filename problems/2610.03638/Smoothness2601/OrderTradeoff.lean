import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Real.Archimedean
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The order--accuracy tradeoff of 2601.tex

The order cap is `WithTop ℕ`; top means that every positive integer order is
available. These are proofs about the actual infimum in eq:Ddefinition, not
statements about a minimax complexity or oracle execution.
-/

noncomputable section
namespace Smoothness2601
open Set Filter
open scoped Topology

def availableOrders (p : WithTop ℕ) : Set ℕ :=
  {r | 1 ≤ r ∧ (r : WithTop ℕ) ≤ p}

def orderTerm (β ε : ℝ) (r : ℕ) : ℝ :=
  (r : ℝ) ^ β * ε ^ (-1 / (r : ℝ))

def orderTradeoff (p : WithTop ℕ) (β ε : ℝ) : ℝ :=
  sInf (orderTerm β ε '' availableOrders p)

theorem availableOrders_nonempty {p : WithTop ℕ} (hp : 1 ≤ p) :
    (availableOrders p).Nonempty := ⟨1, by simpa [availableOrders] using hp⟩

theorem orderTerm_pos {β ε : ℝ} {r : ℕ} (hε : 0 < ε) (hr : 1 ≤ r) :
    0 < orderTerm β ε r := by
  unfold orderTerm
  exact mul_pos (Real.rpow_pos_of_pos (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hr)) _)
    (Real.rpow_pos_of_pos hε _)

theorem orderTerms_bddBelow (p : WithTop ℕ) (β : ℝ) {ε : ℝ} (hε : 0 < ε) :
    BddBelow (orderTerm β ε '' availableOrders p) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨r, hr, rfl⟩
  exact (orderTerm_pos hε hr.1).le

theorem orderTradeoff_le_term {p : WithTop ℕ} {β ε : ℝ} (hε : 0 < ε)
    {r : ℕ} (hr : r ∈ availableOrders p) :
    orderTradeoff p β ε ≤ orderTerm β ε r :=
  csInf_le (orderTerms_bddBelow p β hε) ⟨r, hr, rfl⟩

theorem le_orderTradeoff {p : WithTop ℕ} {β ε a : ℝ} (hp : 1 ≤ p)
    (ha : ∀ r ∈ availableOrders p, a ≤ orderTerm β ε r) :
    a ≤ orderTradeoff p β ε := by
  apply le_csInf ((availableOrders_nonempty hp).image _)
  rintro _ ⟨r, hr, rfl⟩
  exact ha r hr

theorem orderTerm_one_le {β ε : ℝ} {r : ℕ} (hβ : 0 ≤ β) (hε : 0 < ε)
    (hε1 : ε ≤ 1) (hr : 1 ≤ r) : 1 ≤ orderTerm β ε r := by
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have h1 : 1 ≤ (r : ℝ) ^ β := Real.one_le_rpow hr1 hβ
  have h2 : 1 ≤ ε ^ (-1 / (r : ℝ)) := by
    simpa using Real.rpow_le_rpow_of_exponent_ge hε hε1
      (show -1 / (r : ℝ) ≤ 0 from div_nonpos_of_nonpos_of_nonneg (by norm_num) (Nat.cast_nonneg r))
  exact one_le_mul_of_one_le_of_one_le h1 h2

theorem orderTradeoff_one_le {p : WithTop ℕ} {β ε : ℝ} (hp : 1 ≤ p)
    (hβ : 0 ≤ β) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    1 ≤ orderTradeoff p β ε :=
  le_orderTradeoff hp fun _ hr => orderTerm_one_le hβ hε hε1 hr.1

theorem orderTradeoff_le_inv {p : WithTop ℕ} {β ε : ℝ} (hp : 1 ≤ p)
    (hε : 0 < ε) : orderTradeoff p β ε ≤ ε⁻¹ := by
  simpa [orderTerm, Real.rpow_neg_one] using
    orderTradeoff_le_term (β := β) hε (r := 1) (by simpa [availableOrders] using hp)

theorem orderTradeoff_antitone_order {p q : WithTop ℕ} {β ε : ℝ}
    (hp : 1 ≤ p) (hpq : p ≤ q) (hε : 0 < ε) :
    orderTradeoff q β ε ≤ orderTradeoff p β ε := by
  apply le_orderTradeoff hp
  intro r hr
  exact orderTradeoff_le_term hε ⟨hr.1, hr.2.trans hpq⟩

theorem orderTerm_antitone_accuracy {β ε δ : ℝ} {r : ℕ}
    (hε : 0 < ε) (hεδ : ε ≤ δ) : orderTerm β δ r ≤ orderTerm β ε r := by
  apply mul_le_mul_of_nonneg_left
  · exact Real.rpow_le_rpow_of_exponent_nonpos hε hεδ
      (div_nonpos_of_nonpos_of_nonneg (by norm_num) (Nat.cast_nonneg r))
  · exact Real.rpow_nonneg (Nat.cast_nonneg r) β

theorem orderTradeoff_antitone_accuracy {p : WithTop ℕ} {β ε δ : ℝ}
    (hp : 1 ≤ p) (hε : 0 < ε) (hεδ : ε ≤ δ) :
    orderTradeoff p β δ ≤ orderTradeoff p β ε := by
  apply le_orderTradeoff hp
  intro r hr
  exact (orderTradeoff_le_term (hε.trans_le hεδ) hr).trans
    (orderTerm_antitone_accuracy hε hεδ)

theorem orderTerm_zero_antitone {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    {r s : ℕ} (hr : 1 ≤ r) (hrs : r ≤ s) : orderTerm 0 ε s ≤ orderTerm 0 ε r := by
  simp only [orderTerm, Real.rpow_zero, one_mul]
  apply Real.rpow_le_rpow_of_exponent_ge hε hε1
  have hr0 : (0 : ℝ) < r := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hr)
  have hrs' : (r : ℝ) ≤ s := by exact_mod_cast hrs
  have hinv := one_div_le_one_div_of_le hr0 hrs'
  simpa only [neg_div] using neg_le_neg hinv

/-- The finite-order exponential-envelope infimum is attained at the largest order. -/
theorem orderTradeoff_finite_zero {p : ℕ} (hp : 1 ≤ p) {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) :
    orderTradeoff (p : WithTop ℕ) 0 ε = ε ^ (-1 / (p : ℝ)) := by
  have hp' : (1 : WithTop ℕ) ≤ p := by exact_mod_cast hp
  apply le_antisymm
  · simpa [orderTerm] using orderTradeoff_le_term (β := 0) hε (r := p) ⟨hp, le_rfl⟩
  · apply le_orderTradeoff hp'
    intro r hr
    simpa [orderTerm] using orderTerm_zero_antitone hε hε1 hr.1 (by exact_mod_cast hr.2)

theorem orderTerm_zero_tendsto_one {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => orderTerm 0 ε (n + 1)) atTop (𝓝 1) := by
  have h := tendsto_one_div_add_atTop_nhds_zero_nat.neg
  have ht := (tendsto_const_nhds (x := ε)).rpow h (Or.inl (ne_of_gt hε))
  simpa [orderTerm, Nat.cast_add, Nat.cast_one, neg_div] using ht

/-- The infinite exponential envelope has infimum one, without an infinite stencil. -/
theorem orderTradeoff_infinite_zero {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    orderTradeoff ⊤ 0 ε = 1 := by
  apply le_antisymm
  · apply ge_of_tendsto (orderTerm_zero_tendsto_one hε)
    exact Filter.Eventually.of_forall fun n => orderTradeoff_le_term hε ⟨by omega, le_top⟩
  · exact orderTradeoff_one_le le_top le_rfl hε hε1

/-- For strictly subunit accuracy, every finite-order term exceeds the infinite infimum. -/
theorem orderTerm_zero_gt_one {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    {r : ℕ} (hr : 1 ≤ r) : 1 < orderTerm 0 ε r := by
  simp only [orderTerm, Real.rpow_zero, one_mul]
  have hr0 : (0 : ℝ) < r := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hr)
  simpa using Real.rpow_lt_rpow_of_exponent_gt hε hε1
    (show -1 / (r : ℝ) < 0 from div_neg_of_neg_of_pos (by norm_num) hr0)

theorem orderTerm_scale_lower {β ε a : ℝ} {r : ℕ} (hε : 0 < ε)
    (ha : 1 ≤ a) (hr : 1 ≤ r) :
    a⁻¹ * orderTerm β ε r ≤ orderTerm β (a * ε) r := by
  have ha0 : 0 < a := zero_lt_one.trans_le ha
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hr0 : (0 : ℝ) < r := zero_lt_one.trans_le hr1
  have hi : (1 : ℝ) / r ≤ 1 := (div_le_one hr0).2 hr1
  have he : (-1 : ℝ) ≤ -1 / (r : ℝ) := by simpa only [neg_div] using neg_le_neg hi
  have hb : a⁻¹ ≤ a ^ (-1 / (r : ℝ)) := by
    simpa only [Real.rpow_neg_one] using Real.rpow_le_rpow_of_exponent_le ha he
  unfold orderTerm
  rw [Real.mul_rpow ha0.le hε.le]
  nlinarith [mul_le_mul_of_nonneg_right hb
    (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg r) β)
      (Real.rpow_nonneg hε.le (-1 / (r : ℝ))))]

/-- Scaling accuracy by a fixed factor changes the infimum by at most that factor,
uniformly in finite and infinite order, including nonattained infima. -/
theorem orderTradeoff_scale {p : WithTop ℕ} {β ε a : ℝ} (hp : 1 ≤ p)
    (hε : 0 < ε) (ha : 1 ≤ a) :
    a⁻¹ * orderTradeoff p β ε ≤ orderTradeoff p β (a * ε) ∧
      orderTradeoff p β (a * ε) ≤ orderTradeoff p β ε := by
  constructor
  · apply le_orderTradeoff hp
    intro r hr
    exact (mul_le_mul_of_nonneg_left (orderTradeoff_le_term hε hr)
      (inv_nonneg.mpr (zero_le_one.trans ha))).trans (orderTerm_scale_lower hε ha hr.1)
  · exact orderTradeoff_antitone_accuracy hp hε (by nlinarith)

def logOrderTerm (β t r : ℝ) : ℝ := β * Real.log r + t / r

theorem orderTerm_eq_exp {β ε : ℝ} {r : ℕ} (hε : 0 < ε) (hr : 1 ≤ r) :
    orderTerm β ε r = Real.exp (logOrderTerm β (Real.log (1 / ε)) r) := by
  have hr0 : (0 : ℝ) < r := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hr)
  rw [orderTerm, Real.rpow_def_of_pos hr0, Real.rpow_def_of_pos hε, ← Real.exp_add]
  congr 1
  simp only [logOrderTerm, one_div, Real.log_inv]
  ring

/-- The continuous logarithmic objective has its global minimum at t/β. -/
theorem logOrderTerm_global_minimum {β t r : ℝ} (hβ : 0 < β) (ht : 0 < t)
    (hr : 0 < r) :
    β * Real.log (t / β) + β ≤ logOrderTerm β t r := by
  have hratio : 0 < (t / β) / r := div_pos (div_pos ht hβ) hr
  have hlog := Real.log_le_sub_one_of_pos hratio
  rw [Real.log_div (ne_of_gt (div_pos ht hβ)) (ne_of_gt hr)] at hlog
  have h := mul_le_mul_of_nonneg_left hlog hβ.le
  have hid : β * ((t / β) / r - 1) = t / r - β := by field_simp; ring
  rw [hid] at h
  unfold logOrderTerm
  nlinarith

/-- Before t/β the continuous logarithmic objective decreases. -/
theorem logOrderTerm_antitone_before_minimum {β t r s : ℝ} (hβ : 0 ≤ β)
    (hr : 0 < r) (hrs : r ≤ s) (hs : β * s ≤ t) :
    logOrderTerm β t s ≤ logOrderTerm β t r := by
  have hs0 := hr.trans_le hrs
  have hlog := Real.log_le_sub_one_of_pos (div_pos hs0 hr)
  rw [Real.log_div (ne_of_gt hs0) (ne_of_gt hr)] at hlog
  have h := mul_le_mul_of_nonneg_left hlog hβ
  have hgap : 0 ≤ s - r := sub_nonneg.mpr hrs
  have hprod := mul_nonneg (sub_nonneg.mpr hs) hgap
  have hdiv : β * (s / r - 1) ≤ t / r - t / s := by
    have hid : t / r - t / s = t * (s - r) / (r * s) := by field_simp; ring
    rw [hid]
    apply (le_div_iff₀ (mul_pos hr hs0)).2
    have hid' : β * (s / r - 1) * (r * s) = β * s * (s - r) := by field_simp; ring
    rw [hid']
    nlinarith
  unfold logOrderTerm
  linarith

/-- Integer orders below the continuous optimum attain their minimum at the cap. -/
theorem orderTradeoff_finite_before_minimum {p : ℕ} (hp : 1 ≤ p) {β ε : ℝ}
    (hβ : 0 ≤ β) (hε : 0 < ε) (hphase : β * p ≤ Real.log (1 / ε)) :
    orderTradeoff (p : WithTop ℕ) β ε = orderTerm β ε p := by
  apply le_antisymm (orderTradeoff_le_term hε ⟨hp, le_rfl⟩)
  apply le_orderTradeoff (by exact_mod_cast hp)
  intro r hr
  rw [orderTerm_eq_exp hε hp, orderTerm_eq_exp hε hr.1]
  apply Real.exp_le_exp.mpr
  exact logOrderTerm_antitone_before_minimum hβ (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hr.1))
    (by exact_mod_cast (show r ≤ p by exact_mod_cast hr.2)) hphase

theorem orderTerm_eq_rpow_mul_exp {β ε : ℝ} {r : ℕ} (hε : 0 < ε) (hr : 1 ≤ r) :
    orderTerm β ε r = (r : ℝ) ^ β * Real.exp (Real.log (1 / ε) / r) := by
  rw [orderTerm_eq_exp hε hr, logOrderTerm, Real.exp_add]
  rw [mul_comm β, ← Real.rpow_def_of_pos (show (0 : ℝ) < r by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hr))]

/-- A uniform lower bound from the continuous minimum, valid even if it is
outside the available integer orders. -/
theorem orderTradeoff_phase_lower {p : WithTop ℕ} {β ε : ℝ} (hp : 1 ≤ p)
    (hβ : 0 < β) (hε : 0 < ε) (ht : 0 < Real.log (1 / ε)) :
    (Real.log (1 / ε) / β) ^ β * Real.exp β ≤ orderTradeoff p β ε := by
  apply le_orderTradeoff hp
  intro r hr
  rw [orderTerm_eq_exp hε hr.1, Real.rpow_def_of_pos (div_pos ht hβ), ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  simpa only [mul_comm (Real.log _) β] using
    logOrderTerm_global_minimum hβ ht (show (0 : ℝ) < r by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hr.1))

/-- Rounding t/β upward costs at most 2^β once t/β ≥ 1. -/
theorem orderTerm_ceil_phase_upper {β ε : ℝ} (hβ : 0 < β) (hε : 0 < ε)
    (hphase : 1 ≤ Real.log (1 / ε) / β) :
    orderTerm β ε ⌈Real.log (1 / ε) / β⌉₊ ≤
      (2 : ℝ) ^ β * ((Real.log (1 / ε) / β) ^ β * Real.exp β) := by
  let t := Real.log (1 / ε)
  let k : ℕ := ⌈t / β⌉₊
  have htβ : 0 < t / β := zero_lt_one.trans_le hphase
  have hk1 : 1 ≤ k := by
    have h := hphase.trans (Nat.le_ceil (t / β))
    exact_mod_cast h
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk1)
  have hklo : t / β ≤ k := Nat.le_ceil _
  have hkhi : (k : ℝ) ≤ 2 * (t / β) := by
    have h := Nat.ceil_lt_add_one htβ.le
    dsimp [k]
    linarith
  change orderTerm β ε k ≤ _
  rw [orderTerm_eq_rpow_mul_exp hε hk1]
  have hpow : (k : ℝ) ^ β ≤ (2 * (t / β)) ^ β :=
    Real.rpow_le_rpow (Nat.cast_nonneg k) hkhi hβ.le
  have hexp : Real.exp (t / k) ≤ Real.exp β := by
    apply Real.exp_le_exp.mpr
    apply (div_le_iff₀ hk0).2
    have h := (div_le_iff₀ hβ).mp hklo
    nlinarith
  calc
    (k : ℝ) ^ β * Real.exp (t / k) ≤ (2 * (t / β)) ^ β * Real.exp β :=
      mul_le_mul hpow hexp (Real.exp_pos _).le (Real.rpow_nonneg (by positivity) _)
    _ = 2 ^ β * ((t / β) ^ β * Real.exp β) := by rw [Real.mul_rpow (by norm_num) htβ.le]; ring

/-- The infinite-order positive-β endpoint has the explicit two-sided
comparison with exp(β) (log(1/ε)/β)^β. -/
theorem orderTradeoff_infinite_phase {β ε : ℝ} (hβ : 0 < β) (hε : 0 < ε)
    (hphase : 1 ≤ Real.log (1 / ε) / β) :
    (Real.log (1 / ε) / β) ^ β * Real.exp β ≤ orderTradeoff ⊤ β ε ∧
      orderTradeoff ⊤ β ε ≤
        (2 : ℝ) ^ β * ((Real.log (1 / ε) / β) ^ β * Real.exp β) := by
  have htβ : 0 < Real.log (1 / ε) / β := zero_lt_one.trans_le hphase
  have ht : 0 < Real.log (1 / ε) := by
    have h := (le_div_iff₀ hβ).mp hphase
    linarith
  constructor
  · exact orderTradeoff_phase_lower le_top hβ hε ht
  · apply (orderTradeoff_le_term hε (r := ⌈Real.log (1 / ε) / β⌉₊) ⟨?_, le_top⟩).trans
      (orderTerm_ceil_phase_upper hβ hε hphase)
    exact_mod_cast (hphase.trans (Nat.le_ceil _))

theorem orderTradeoff_finite_phase {p : ℕ} {β ε : ℝ} (hβ : 0 < β) (hε : 0 < ε)
    (hphase : 1 ≤ Real.log (1 / ε) / β) (hp : Real.log (1 / ε) / β ≤ p) :
    (Real.log (1 / ε) / β) ^ β * Real.exp β ≤ orderTradeoff (p : WithTop ℕ) β ε ∧
      orderTradeoff (p : WithTop ℕ) β ε ≤
        (2 : ℝ) ^ β * ((Real.log (1 / ε) / β) ^ β * Real.exp β) := by
  have hp1 : 1 ≤ p := by exact_mod_cast hphase.trans hp
  have ht : 0 < Real.log (1 / ε) := by
    have h := (le_div_iff₀ hβ).mp hphase
    linarith
  constructor
  · exact orderTradeoff_phase_lower (by exact_mod_cast hp1) hβ hε ht
  · apply (orderTradeoff_le_term hε (r := ⌈Real.log (1 / ε) / β⌉₊) ⟨?_, ?_⟩).trans
      (orderTerm_ceil_phase_upper hβ hε hphase)
    · exact_mod_cast (hphase.trans (Nat.le_ceil _))
    · exact_mod_cast (Nat.ceil_le.mpr hp)

/-- The explicit finite-order rate expression in the exponential envelope. -/
theorem orderTradeoff_finite_zero_rate {p : ℕ} (hp : 1 ≤ p) {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ε ^ (-4 : ℝ) * orderTradeoff (p : WithTop ℕ) 0 ε ^ 2 =
      ε ^ (-4 - 2 / (p : ℝ)) := by
  rw [orderTradeoff_finite_zero hp hε hε1, ← Real.rpow_natCast, ← Real.rpow_mul hε.le,
    ← Real.rpow_add hε]
  congr 1
  norm_num
  ring

/-- A finite order of size at most 2 log(1/ε) suffices for the infinite
exponential-envelope endpoint; no infinite differentiation rule is required. -/
theorem orderTerm_zero_log_ceil {ε : ℝ} (hε : 0 < ε)
    (ht : 1 ≤ Real.log (1 / ε)) :
    orderTerm 0 ε ⌈Real.log (1 / ε)⌉₊ ≤ Real.exp 1 ∧
      (⌈Real.log (1 / ε)⌉₊ : ℝ) ≤ 2 * Real.log (1 / ε) := by
  have hk1 : 1 ≤ ⌈Real.log (1 / ε)⌉₊ := by exact_mod_cast ht.trans (Nat.le_ceil _)
  have hk0 : (0 : ℝ) < ⌈Real.log (1 / ε)⌉₊ := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk1)
  constructor
  · rw [orderTerm_eq_rpow_mul_exp hε hk1, Real.rpow_zero, one_mul]
    exact Real.exp_le_exp.mpr ((div_le_one hk0).mpr (Nat.le_ceil _))
  · have h := Nat.ceil_lt_add_one (zero_le_one.trans ht)
    linarith

def sineWidth (p : WithTop ℕ) (β ε K : ℝ) : ℝ := K / orderTradeoff p β ε

/-- The uniform width interval in eq:main-width-bound. -/
theorem sineWidth_bounds {p : WithTop ℕ} {β ε K : ℝ} (hp : 1 ≤ p)
    (hβ : 0 ≤ β) (hε : 0 < ε) (hε1 : ε ≤ 1) (hK : 0 < K) :
    K * ε ≤ sineWidth p β ε K ∧ sineWidth p β ε K ≤ K := by
  have hD := orderTradeoff_one_le hp hβ hε hε1
  have hDpos := zero_lt_one.trans_le hD
  have hDu := orderTradeoff_le_inv (β := β) hp hε
  have hs : ε * orderTradeoff p β ε ≤ 1 := by
    simpa only [mul_inv_cancel₀ (ne_of_gt hε)] using mul_le_mul_of_nonneg_left hDu hε.le
  constructor
  · unfold sineWidth
    apply (le_div_iff₀ hDpos).2
    nlinarith [mul_le_mul_of_nonneg_left hs hK.le]
  · unfold sineWidth
    apply (div_le_iff₀ hDpos).2
    nlinarith

theorem orderTerm_pow_order {β ε : ℝ} {r : ℕ} (hε : 0 < ε) (hr : 1 ≤ r) :
    orderTerm β ε r ^ r = ((r : ℝ) ^ β) ^ r / ε := by
  have hr0 : (0 : ℝ) < r := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hr)
  rw [orderTerm, mul_pow]
  have hpow : (ε ^ (-1 / (r : ℝ))) ^ r = ε⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hε.le]
    have he : (-1 / (r : ℝ)) * r = -1 := by field_simp
    rw [he, Real.rpow_neg_one]
  rw [hpow, div_eq_mul_inv]

/-- Every prescribed derivative order satisfies the width bound using the
same K, including when the cap is infinite. -/
theorem sineWidth_derivative_budget {p : WithTop ℕ} {β ε K : ℝ} {r : ℕ}
    (hp : 1 ≤ p) (hβ : 0 ≤ β) (hε : 0 < ε) (hε1 : ε ≤ 1) (hK : 0 < K)
    (hr : r ∈ availableOrders p) :
    ε * (sineWidth p β ε K)⁻¹ ^ r ≤ ((r : ℝ) ^ β / K) ^ r := by
  have hD := orderTradeoff_one_le hp hβ hε hε1
  have hpow : orderTradeoff p β ε ^ r ≤ orderTerm β ε r ^ r :=
    pow_le_pow_left₀ (zero_le_one.trans hD) (orderTradeoff_le_term hε hr) _
  rw [orderTerm_pow_order hε hr.1] at hpow
  have hmul : ε * orderTradeoff p β ε ^ r ≤ ((r : ℝ) ^ β) ^ r := by
    have h := mul_le_mul_of_nonneg_left hpow hε.le
    field_simp at h ⊢
    nlinarith
  unfold sineWidth
  rw [inv_div, div_pow, div_pow, ← mul_div_assoc]
  exact div_le_div_of_nonneg_right hmul (pow_nonneg hK.le _)

end Smoothness2601
