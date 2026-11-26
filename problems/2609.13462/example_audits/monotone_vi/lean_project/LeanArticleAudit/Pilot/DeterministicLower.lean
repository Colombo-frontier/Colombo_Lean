import LeanArticleAudit.Pilot.Residual
import Mathlib.Analysis.Normed.Module.Normalize

/-!
# Deterministic resisting-oracle lower bound: transcript core

This file isolates the exact-jet statement used in `thm:det`.  The truncated
answer at stage `t` contains the first `t` links of the hidden chain.  If all
not-yet-revealed input directions are orthogonal to the current query, then
the complete jets (not merely directional products) of the truncated and
final operators coincide through every order.

The online choice of the frame for an arbitrary strategy tree is deliberately
kept separate from this analytic transcript lemma.
-/

open Set Filter
open scoped RealInnerProductSpace Topology

namespace LeanArticleAudit.Pilot

section OrthogonalChoice

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- A finite family with fewer entries than the ambient dimension has a unit
vector orthogonal to every member.  This is the one-step dimension-counting
lemma used at each resisting-oracle round. -/
theorem exists_unit_orthogonal_fin {k : ℕ} (u : Fin k → E)
    (hk : k < Module.finrank ℝ E) :
    ∃ w : E, ‖w‖ = 1 ∧ ∀ i, inner ℝ w (u i) = 0 := by
  classical
  let S : Submodule ℝ E := Submodule.span ℝ (Set.range u)
  have hfin : Module.finrank ℝ S ≤ k := by
    calc
      Module.finrank ℝ S ≤ (Set.range u).toFinset.card :=
        finrank_span_le_card (Set.range u)
      _ ≤ Fintype.card (Fin k) := by
        rw [Set.toFinset_card]
        exact Fintype.card_range_le u
      _ = k := Fintype.card_fin k
  have hpos : 0 < Module.finrank ℝ Sᗮ := by
    have hadd := S.finrank_add_finrank_orthogonal
    omega
  have hne : Sᗮ ≠ ⊥ := by
    intro hbot
    have : Module.finrank ℝ Sᗮ = 0 := Submodule.finrank_eq_zero.mpr hbot
    omega
  letI : Nontrivial Sᗮ := Submodule.nontrivial_iff_ne_bot.mpr hne
  obtain ⟨z, hz⟩ : ∃ z : Sᗮ, z ≠ 0 := exists_ne 0
  refine ⟨NormedSpace.normalize (z : E), NormedSpace.norm_normalize ?_, ?_⟩
  · exact Subtype.coe_ne_coe.mpr hz
  · intro i
    have hzorth : inner ℝ (z : E) (u i) = 0 :=
      Submodule.inner_left_of_mem_orthogonal
        (Submodule.subset_span
          (show u i ∈ Set.range u from ⟨i, rfl⟩)) z.2
    rw [NormedSpace.normalize, real_inner_smul_left, hzorth, mul_zero]

/-- The form used in the paper: one can avoid all previous frame vectors and
all queries seen so far whenever their total count is below the dimension. -/
theorem exists_unit_orthogonal_two_fin {r s : ℕ} (a : Fin r → E) (b : Fin s → E)
    (hrs : r + s < Module.finrank ℝ E) :
    ∃ w : E, ‖w‖ = 1 ∧
      (∀ i, inner ℝ w (a i) = 0) ∧ (∀ j, inner ℝ w (b j) = 0) := by
  obtain ⟨w, hw, horth⟩ := exists_unit_orthogonal_fin (Fin.append a b) hrs
  refine ⟨w, hw, ?_, ?_⟩
  · intro i
    simpa using horth (Fin.castAdd s i)
  · intro j
    simpa using horth (Fin.natAdd r j)

/-- Appending a unit vector perpendicular to a finite orthonormal family
preserves orthonormality. -/
theorem orthonormal_fin_snoc {k : ℕ} (u : Fin k → E) (w : E)
    (hu : Orthonormal ℝ u) (hw : ‖w‖ = 1)
    (hwu : ∀ i, inner ℝ w (u i) = 0) :
    Orthonormal ℝ (Fin.append u (fun _ : Fin 1 => w)) := by
  constructor
  · intro i
    refine Fin.addCases (fun i' => ?_) (fun _ => ?_) i
    · simpa using hu.1 i'
    · simpa using hw
  · intro i j
    revert j
    refine Fin.addCases (fun i' => ?_) (fun i' => ?_) i <;>
      intro j <;> revert j <;>
      refine Fin.addCases (fun j' => ?_) (fun j' => ?_)
    · intro hij
      simpa using hu.2 (fun h => hij (congrArg (Fin.castAdd 1) h))
    · intro _hij
      simpa [real_inner_comm] using hwu i'
    · intro _hij
      simpa using hwu j'
    · have hij' : i' = j' := Subsingleton.elim _ _
      intro hij
      exact (hij (by subst j'; rfl)).elim

/-- Extend an orthonormal prefix to a prescribed finite length.  Every new
vector avoids the fixed query history, and the final vector also avoids the
terminal output.  The extra factor two in the ambient dimension is exactly
the resisting-oracle dimension count. -/
theorem exists_orthonormal_completion_avoiding
    (N k t : ℕ) (hkN : k ≤ N) (htk : t ≤ k)
    (u : Fin k → E) (z : Fin t → E) (y : E)
    (hu : Orthonormal ℝ u)
    (hdim : 2 * N + 2 ≤ Module.finrank ℝ E) :
    ∃ v : Fin (N + 1) → E,
      Orthonormal ℝ v ∧
      (∀ i : Fin k, v (Fin.castLE (by omega) i) = u i) ∧
      (∀ i : Fin (N + 1), k ≤ i.1 → ∀ j : Fin t,
        inner ℝ (v i) (z j) = 0) ∧
      inner ℝ (v (Fin.last N)) y = 0 := by
  induction hgap : N - k using Nat.strong_induction_on generalizing k u with
  | h gap ih =>
      by_cases hk : k = N
      · subst k
        let zy : Fin (t + 1) → E := Fin.append z (fun _ : Fin 1 => y)
        have hcount : N + (t + 1) < Module.finrank ℝ E := by omega
        obtain ⟨w, hw, hwu, hwzy⟩ :=
          exists_unit_orthogonal_two_fin u zy hcount
        let v : Fin (N + 1) → E := Fin.append u (fun _ : Fin 1 => w)
        have hv : Orthonormal ℝ v := orthonormal_fin_snoc u w hu hw hwu
        refine ⟨v, hv, ?_, ?_, ?_⟩
        · intro i
          exact Fin.append_left _ _ i
        · intro i hi j
          have hval : i.1 = N := Nat.le_antisymm (Nat.le_of_lt_succ i.2) hi
          have hilast : i = Fin.last N := Fin.ext hval
          rw [hilast]
          have hwz : inner ℝ w (z j) = 0 := by
            have := hwzy (Fin.castAdd 1 j)
            simpa [zy] using this
          have vlast : v (Fin.last N) = w := by
            change Fin.append u (fun _ : Fin 1 => w) (Fin.last N) = w
            rw [show Fin.last N = Fin.natAdd N (0 : Fin 1) from Fin.ext rfl,
              Fin.append_right]
          rw [vlast]
          exact hwz
        · have hwy : inner ℝ w y = 0 := by
            have := hwzy (Fin.natAdd t (0 : Fin 1))
            simpa [zy] using this
          have vlast : v (Fin.last N) = w := by
            change Fin.append u (fun _ : Fin 1 => w) (Fin.last N) = w
            rw [show Fin.last N = Fin.natAdd N (0 : Fin 1) from Fin.ext rfl,
              Fin.append_right]
          rw [vlast]
          exact hwy
      · have hklt : k < N := lt_of_le_of_ne hkN hk
        have hcount : k + t < Module.finrank ℝ E := by omega
        obtain ⟨w, hw, hwu, hwz⟩ :=
          exists_unit_orthogonal_two_fin u z hcount
        let u' : Fin (k + 1) → E := Fin.append u (fun _ : Fin 1 => w)
        have hu' : Orthonormal ℝ u' := orthonormal_fin_snoc u w hu hw hwu
        have hgaplt : N - (k + 1) < gap := by omega
        obtain ⟨v, hv, hvu', hvz, hvy⟩ :=
          ih (N - (k + 1)) hgaplt (k + 1) (by omega) (by omega) u' hu' rfl
        refine ⟨v, hv, ?_, ?_, hvy⟩
        · intro i
          have hleft := Fin.append_left u (fun _ : Fin 1 => w) i
          rw [← hleft]
          exact hvu' (Fin.castAdd 1 i)
        · intro i hik j
          by_cases hieq : i.1 = k
          · have hi : i = Fin.castLE (by omega) (Fin.last k) :=
              Fin.ext (by simpa using hieq)
            have hwzj := hwz j
            let ilast : Fin (k + 1) := Fin.natAdd k (0 : Fin 1)
            have hlast : Fin.last k = ilast := Fin.ext rfl
            rw [hi, hlast, hvu' ilast]
            change inner ℝ (u' ilast) (z j) = 0
            rw [show u' ilast = w from
              Fin.append_right u (fun _ : Fin 1 => w) (0 : Fin 1)]
            exact hwzj
          · exact hvz i (by omega) j

end OrthogonalChoice

section Truncation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Pad a prefix by zero.  A stage-`t` truncated answer only inspects this
prefix, so the padding is computationally irrelevant. -/
noncomputable def prefixPadFrame (N t : ℕ) (ht : t ≤ N)
    (u : Fin (t + 1) → E) : Fin (N + 1) → E :=
  fun i => if hi : i.1 < t + 1 then u ⟨i.1, hi⟩ else 0

@[simp] theorem prefixPadFrame_prefix (N t : ℕ) (ht : t ≤ N)
    (u : Fin (t + 1) → E) (i : Fin (t + 1)) :
    prefixPadFrame N t ht u (Fin.castLE (by omega) i) = u i := by
  simp [prefixPadFrame, i.2]

/-- The hidden map truncated after the first `t` chain links.  Values `t>N`
are harmless and give the full map. -/
noncomputable def truncatedHiddenMap (profile : GateProfile) (R : ℝ) (N t : ℕ)
    (v : Fin (N + 1) → E) (x : E) : E :=
  hiddenC R N • v ⟨0, Nat.zero_lt_succ N⟩ +
    hiddenQ N • ∑ i : Fin N, if i.1 < t then
      gate profile (hiddenTau R N) (inner ℝ (v i.castSucc) x) • v i.succ else 0

/-- The stage-`t` truncated map depends only on frame entries `0,...,t`. -/
theorem truncatedHiddenMap_congr_prefix (profile : GateProfile) (R : ℝ)
    (N t : ℕ) (ht : t ≤ N) (v w : Fin (N + 1) → E)
    (hvw : ∀ i : Fin (t + 1),
      v (Fin.castLE (by omega) i) = w (Fin.castLE (by omega) i)) :
    truncatedHiddenMap profile R N t v = truncatedHiddenMap profile R N t w := by
  funext x
  simp only [truncatedHiddenMap]
  have hzero : v ⟨0, Nat.zero_lt_succ N⟩ = w ⟨0, Nat.zero_lt_succ N⟩ := by
    simpa using hvw ⟨0, Nat.zero_lt_succ t⟩
  rw [hzero]
  congr 2
  apply Finset.sum_congr rfl
  intro i _hi
  by_cases hit : i.1 < t
  · simp only [if_pos hit]
    have hin : v i.castSucc = w i.castSucc := by
      let j : Fin (t + 1) := ⟨i.1, by omega⟩
      have hidx : Fin.castLE (by omega) j = i.castSucc := Fin.ext rfl
      rw [← hidx]
      exact hvw j
    have hout : v i.succ = w i.succ := by
      let j : Fin (t + 1) := ⟨i.1 + 1, by omega⟩
      have hidx : Fin.castLE (by omega) j = i.succ := Fin.ext rfl
      rw [← hidx]
      exact hvw j
    rw [hin, hout]
  · simp [hit]

/-- The stage-`t` operator answered by the resisting oracle. -/
noncomputable def truncatedHiddenOperator (p : ℕ) (profile : GateProfile)
    (Lp R : ℝ) (N t : ℕ) (v : Fin (N + 1) → E) (x : E) : E :=
  hiddenLambda p profile Lp R N • (x - truncatedHiddenMap profile R N t v x)

theorem truncatedHiddenOperator_congr_prefix (p : ℕ)
    (profile : GateProfile) (Lp R : ℝ) (N t : ℕ) (ht : t ≤ N)
    (v w : Fin (N + 1) → E)
    (hvw : ∀ i : Fin (t + 1),
      v (Fin.castLE (by omega) i) = w (Fin.castLE (by omega) i)) :
    truncatedHiddenOperator p profile Lp R N t v =
      truncatedHiddenOperator p profile Lp R N t w := by
  funext x
  simp only [truncatedHiddenOperator]
  rw [truncatedHiddenMap_congr_prefix profile R N t ht v w hvw]

@[simp] theorem truncatedHiddenMap_of_ge (profile : GateProfile) (R : ℝ)
    (N t : ℕ) (ht : N ≤ t) (v : Fin (N + 1) → E) :
    truncatedHiddenMap profile R N t v = hiddenMap profile R N v := by
  funext x
  simp only [truncatedHiddenMap, hiddenMap]
  congr 2
  apply Finset.sum_congr rfl
  intro i _hi
  simp [lt_of_lt_of_le i.2 ht]

/-- At a point orthogonal to every unrevealed input direction, the full and
truncated hidden maps agree on a neighborhood.  This is the mathematical
reason an exact full-tensor oracle cannot see future links. -/
theorem truncatedHiddenMap_eventuallyEq (profile : GateProfile) {R : ℝ}
    (hR : 0 < R) (N t : ℕ) (v : Fin (N + 1) → E) (x : E)
    (horth : ∀ i : Fin N, t ≤ i.1 → inner ℝ (v i.castSucc) x = 0) :
    truncatedHiddenMap profile R N t v =ᶠ[𝓝 x]
      hiddenMap profile R N v := by
  have htau : 0 < hiddenTau R N := hiddenTau_pos hR N
  have hcoord (i : Fin N) (hi : t ≤ i.1) :
      ∀ᶠ y in 𝓝 x, |inner ℝ (v i.castSucc) y| ≤ hiddenTau R N / 2 := by
    have hcont : Continuous (fun y : E ↦ inner ℝ (v i.castSucc) y) :=
      (innerSL ℝ (v i.castSucc)).continuous
    have hopen : Set.Iio (hiddenTau R N / 2) ∈ 𝓝 (0 : ℝ) := by
      exact Iio_mem_nhds (by positivity)
    have hev : ∀ᶠ y in 𝓝 x,
        |inner ℝ (v i.castSucc) y| < hiddenTau R N / 2 := by
      have habscont : Continuous (fun y : E ↦ |inner ℝ (v i.castSucc) y|) :=
        hcont.abs
      have hlim := habscont.continuousAt (x := x)
      have hopen' : Set.Iio (hiddenTau R N / 2) ∈
          𝓝 |inner ℝ (v i.castSucc) x| := by
        simpa [horth i hi] using hopen
      exact hlim.eventually hopen'
    exact hev.mono fun _ hy ↦ hy.le
  have hall : ∀ᶠ y in 𝓝 x, ∀ i : Fin N, t ≤ i.1 →
      |inner ℝ (v i.castSucc) y| ≤ hiddenTau R N / 2 := by
    apply Filter.eventually_all.2
    intro i
    by_cases hi : t ≤ i.1
    · exact (hcoord i hi).mono fun _ hy _ ↦ hy
    · exact Filter.Eventually.of_forall fun _ hit ↦ (hi hit).elim
  filter_upwards [hall] with y hy
  simp only [truncatedHiddenMap, hiddenMap]
  congr 2
  apply Finset.sum_congr rfl
  intro i _hi
  by_cases hit : i.1 < t
  · simp [hit]
  · have hzero := gate_zero_core profile htau (hy i (Nat.le_of_not_gt hit))
    rw [if_neg hit, hzero, zero_smul]

/-- Exact equality of every iterated Fréchet derivative at the query. -/
theorem truncatedHiddenMap_iteratedFDeriv_eq (profile : GateProfile) {R : ℝ}
    (hR : 0 < R) (N t n : ℕ) (v : Fin (N + 1) → E) (x : E)
    (horth : ∀ i : Fin N, t ≤ i.1 → inner ℝ (v i.castSucc) x = 0) :
    iteratedFDeriv ℝ n (truncatedHiddenMap profile R N t v) x =
      iteratedFDeriv ℝ n (hiddenMap profile R N v) x := by
  exact ((truncatedHiddenMap_eventuallyEq profile hR N t v x horth).iteratedFDeriv ℝ n).self_of_nhds

/-- Exact equality of every iterated Fréchet derivative of the stage and
final operators. -/
theorem truncatedHiddenOperator_iteratedFDeriv_eq (p : ℕ)
    (profile : GateProfile) (Lp : ℝ) {R : ℝ} (hR : 0 < R)
    (N t n : ℕ) (v : Fin (N + 1) → E) (x : E)
    (horth : ∀ i : Fin N, t ≤ i.1 → inner ℝ (v i.castSucc) x = 0) :
    iteratedFDeriv ℝ n (truncatedHiddenOperator p profile Lp R N t v) x =
      iteratedFDeriv ℝ n (hiddenOperator p profile Lp R N v) x := by
  have hevent := truncatedHiddenMap_eventuallyEq profile hR N t v x horth
  have hfun : (fun y : E ↦ hiddenLambda p profile Lp R N •
      (y - truncatedHiddenMap profile R N t v y)) =ᶠ[𝓝 x]
      (fun y : E ↦ hiddenLambda p profile Lp R N •
      (y - hiddenMap profile R N v y)) := by
    filter_upwards [hevent] with y hy
    rw [hy]
  change iteratedFDeriv ℝ n
      (fun y : E ↦ hiddenLambda p profile Lp R N •
        (y - truncatedHiddenMap profile R N t v y)) x = _
  change _ = iteratedFDeriv ℝ n
      (fun y : E ↦ hiddenLambda p profile Lp R N •
        (y - hiddenMap profile R N v y)) x
  exact (hfun.iteratedFDeriv ℝ n).self_of_nhds

/-- Equality of the complete order-`p` exact jets returned to the policy. -/
theorem truncatedHiddenOperator_exactJet_eq (p : ℕ)
    (profile : GateProfile) (Lp : ℝ) {R : ℝ} (hR : 0 < R)
    (N t : ℕ) (v : Fin (N + 1) → E) (x : E)
    (horth : ∀ i : Fin N, t ≤ i.1 → inner ℝ (v i.castSucc) x = 0) :
    exactJet p (truncatedHiddenOperator p profile Lp R N t v) x =
      exactJet p (hiddenOperator p profile Lp R N v) x := by
  funext j
  exact truncatedHiddenOperator_iteratedFDeriv_eq p profile Lp hR N t j.1 v x horth

/-- The same transcript identity in the audited symmetric-jet subtype.  The
symmetry witnesses themselves are proof-irrelevant; equality is determined by
the complete multilinear tensors. -/
theorem truncatedHiddenOperator_symmetricExactJet_eq (p : ℕ)
    (profile : GateProfile) (Lp : ℝ) {R : ℝ} (hR : 0 < R)
    (N t : ℕ) (v : Fin (N + 1) → E) (x : E)
    (horth : ∀ i : Fin N, t ≤ i.1 → inner ℝ (v i.castSucc) x = 0)
    (hstage : ∀ (j : Fin p) (σ : Equiv.Perm (Fin j.1)),
      ContinuousMultilinearMap.domDomCongr σ
        (iteratedFDeriv ℝ j.1
          (truncatedHiddenOperator p profile Lp R N t v) x) =
        iteratedFDeriv ℝ j.1
          (truncatedHiddenOperator p profile Lp R N t v) x)
    (hfinal : ∀ (j : Fin p) (σ : Equiv.Perm (Fin j.1)),
      ContinuousMultilinearMap.domDomCongr σ
        (iteratedFDeriv ℝ j.1
          (hiddenOperator p profile Lp R N v) x) =
        iteratedFDeriv ℝ j.1 (hiddenOperator p profile Lp R N v) x) :
    exactSymmetricJetOf E p
        (truncatedHiddenOperator p profile Lp R N t v) x hstage =
      exactSymmetricJetOf E p
        (hiddenOperator p profile Lp R N v) x hfinal := by
  funext j
  apply Subtype.ext
  exact truncatedHiddenOperator_iteratedFDeriv_eq p profile Lp hR N t j.1 v x horth

end Truncation

section TranscriptContract

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Finite data contract produced by the online resisting construction.
`query t` is the stage-`t` query (zero-based); triangular orthogonality says
all not-yet-revealed input directions are invisible there. -/
structure ResistingTranscript (N : ℕ) (v : Fin (N + 1) → E) where
  query : Fin N → E
  output : E
  query_future_orthogonal : ∀ t : Fin N, ∀ i : Fin N,
    t.1 ≤ i.1 → inner ℝ (v i.castSucc) (query t) = 0
  output_last_orthogonal : inner ℝ (v (Fin.last N)) output = 0

/-- Every stage answer in a resisting transcript is exactly the answer of the
single final hidden operator. -/
theorem ResistingTranscript.all_exactJets_match {N p : ℕ}
    (profile : GateProfile) (Lp : ℝ) {R : ℝ} (hR : 0 < R)
    (v : Fin (N + 1) → E) (tr : ResistingTranscript N v) (t : Fin N) :
    exactJet p (truncatedHiddenOperator p profile Lp R N t.1 v) (tr.query t) =
      exactJet p (hiddenOperator p profile Lp R N v) (tr.query t) := by
  exact truncatedHiddenOperator_exactJet_eq p profile Lp hR N t.1 v (tr.query t)
    (tr.query_future_orthogonal t)

/-- The terminal output lies in the hidden slab required by `lem:residual`. -/
theorem ResistingTranscript.output_in_hidden_slab {N : ℕ} {R : ℝ}
    (hR : 0 < R) (v : Fin (N + 1) → E) (tr : ResistingTranscript N v) :
    |inner ℝ (v (Fin.last N)) tr.output| ≤ hiddenTau R N / 2 := by
  rw [tr.output_last_orthogonal, abs_zero]
  exact div_nonneg (hiddenTau_pos hR N).le (by norm_num)

/-- Dimension arithmetic for a zero-based online round: `t` old directions
plus `t+1` queries occupy at most `2t+1` dimensions. -/
theorem resisting_query_count_lt {N d t : ℕ} (hd : 2 * N + 2 ≤ d)
    (ht : t ≤ N) : 2 * t + 1 < d := by omega

/-- At the terminal extension there are `N` old directions, `N` queries and
one arbitrary output to avoid. -/
theorem resisting_terminal_count_lt {N d : ℕ} (hd : 2 * N + 2 ≤ d) :
    2 * N + 1 < d := by omega

end TranscriptContract

section PolicyReplay

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

namespace DeterministicPolicy

/-- Execute a strategy against the stage-dependent truncated answers.  This
is the formal counterpart of the paper's resisting-oracle simulation. -/
noncomputable def runTruncated (p : ℕ) (profile : GateProfile) (Lp R : ℝ)
    (N t : ℕ) (v : Fin (N + 1) → E) :
    {budget : ℕ} → DeterministicPolicy (Metric.closedBall (0 : E) R)
      (ExactJet E p) budget → Metric.closedBall (0 : E) R
  | _, .done output => output
  | _, @DeterministicPolicy.query _ _ _ _ queryPoint next =>
      runTruncated p profile Lp R N (t + 1) v
        (next (exactJet p
          (truncatedHiddenOperator p profile Lp R N t v) queryPoint.1))

/-- Along the simulated path, every current query is orthogonal to every
not-yet-revealed input direction. -/
def IsTriangularTruncatedRun (p : ℕ) (profile : GateProfile) (Lp R : ℝ)
    (N t : ℕ) (v : Fin (N + 1) → E) :
    {budget : ℕ} → DeterministicPolicy (Metric.closedBall (0 : E) R)
      (ExactJet E p) budget → Prop
  | _, .done _ => True
  | _, @DeterministicPolicy.query _ _ _ _ queryPoint next =>
      (∀ i : Fin N, t ≤ i.1 → inner ℝ (v i.castSucc) queryPoint.1 = 0) ∧
      IsTriangularTruncatedRun p profile Lp R N (t + 1) v
        (next (exactJet p
          (truncatedHiddenOperator p profile Lp R N t v) queryPoint.1))

/-- Strong online invariant for the resisting-oracle construction.  Besides
the transcript condition it records that every still-unselected direction
will avoid every query already made. -/
theorem exists_resisting_extension (p : ℕ) (profile : GateProfile)
    (Lp R : ℝ) (N t : ℕ) (htN0 : t ≤ N)
    (hdim : 2 * N + 2 ≤ Module.finrank ℝ E)
    (u : Fin t → E) (z : Fin t → E) (hu : Orthonormal ℝ u) :
    {budget : ℕ} → (policy : DeterministicPolicy
      (Metric.closedBall (0 : E) R) (ExactJet E p) budget) →
      t + budget ≤ N →
      ∃ v : Fin (N + 1) → E,
        Orthonormal ℝ v ∧
        (∀ i : Fin t, v (Fin.castLE (by omega) i) = u i) ∧
        (∀ i : Fin (N + 1), t ≤ i.1 → ∀ j : Fin t,
          inner ℝ (v i) (z j) = 0) ∧
        IsTriangularTruncatedRun p profile Lp R N t v policy ∧
        inner ℝ (v (Fin.last N))
          (runTruncated p profile Lp R N t v policy).1 = 0
  | _, .done output, htN => by
      obtain ⟨v, hv, hvu, hvz, hvout⟩ :=
        exists_orthonormal_completion_avoiding N t t (by omega) le_rfl
          u z output.1 hu hdim
      exact ⟨v, hv, hvu, hvz, by simp [IsTriangularTruncatedRun], by
        simpa [runTruncated] using hvout⟩
  | b + 1, @DeterministicPolicy.query _ _ _ _ queryPoint next, htN => by
      let z' : Fin (t + 1) → E :=
        Fin.append z (fun _ : Fin 1 => queryPoint.1)
      have hcount : t + (t + 1) < Module.finrank ℝ E := by omega
      obtain ⟨w, hw, hwu, hwz'⟩ :=
        exists_unit_orthogonal_two_fin u z' hcount
      let u' : Fin (t + 1) → E := Fin.append u (fun _ : Fin 1 => w)
      have hu' : Orthonormal ℝ u' := orthonormal_fin_snoc u w hu hw hwu
      let fake : Fin (N + 1) → E := prefixPadFrame N t (by omega) u'
      let answer : ExactJet E p := exactJet p
        (truncatedHiddenOperator p profile Lp R N t fake) queryPoint.1
      obtain ⟨v, hv, hvu', hvz', htri, hout⟩ :=
        exists_resisting_extension p profile Lp R N (t + 1) (by omega) hdim
          u' z' hu' (next answer) (by omega)
      have hprefix : ∀ i : Fin (t + 1),
          fake (Fin.castLE (by omega) i) =
            v (Fin.castLE (by omega) i) := by
        intro i
        rw [show fake (Fin.castLE (by omega) i) = u' i from
          prefixPadFrame_prefix N t (by omega) u' i]
        exact (hvu' i).symm
      have hop : truncatedHiddenOperator p profile Lp R N t fake =
          truncatedHiddenOperator p profile Lp R N t v :=
        truncatedHiddenOperator_congr_prefix p profile Lp R N t (by omega)
          fake v hprefix
      have hans : answer = exactJet p
          (truncatedHiddenOperator p profile Lp R N t v) queryPoint.1 := by
        simp only [answer]
        rw [hop]
      have hwt : inner ℝ w queryPoint.1 = 0 := by
        have := hwz' (Fin.natAdd t (0 : Fin 1))
        simpa [z'] using this
      have hwz : ∀ j : Fin t, inner ℝ w (z j) = 0 := by
        intro j
        have := hwz' (Fin.castAdd 1 j)
        simpa [z'] using this
      refine ⟨v, hv, ?_, ?_, ?_, ?_⟩
      · intro i
        have hleft := Fin.append_left u (fun _ : Fin 1 => w) i
        rw [← hleft]
        exact hvu' (Fin.castAdd 1 i)
      · intro i hit j
        by_cases hieq : i.1 = t
        · have hi : i = Fin.castLE (by omega) (Fin.last t) :=
            Fin.ext (by simpa using hieq)
          let ilast : Fin (t + 1) := Fin.natAdd t (0 : Fin 1)
          have hlast : Fin.last t = ilast := Fin.ext rfl
          rw [hi, hlast, hvu' ilast]
          change inner ℝ (u' ilast) (z j) = 0
          rw [show u' ilast = w from
            Fin.append_right u (fun _ : Fin 1 => w) (0 : Fin 1)]
          exact hwz j
        · simpa [z'] using hvz' i (by omega) (Fin.castAdd 1 j)
      · constructor
        · intro i hi
          by_cases hieq : i.1 = t
          · have hiFin : i.castSucc = Fin.castLE (by omega) (Fin.last t) :=
              Fin.ext (by simpa using hieq)
            let ilast : Fin (t + 1) := Fin.natAdd t (0 : Fin 1)
            have hlast : Fin.last t = ilast := Fin.ext rfl
            rw [hiFin, hlast, hvu' ilast]
            change inner ℝ (u' ilast) queryPoint.1 = 0
            rw [show u' ilast = w from
              Fin.append_right u (fun _ : Fin 1 => w) (0 : Fin 1)]
            exact hwt
          · have hfuture : t + 1 ≤ i.1 := by omega
            have := hvz' i.castSucc hfuture (Fin.natAdd t (0 : Fin 1))
            simpa [z'] using this
        · rw [← hans]
          exact htri
      · simp only [runTruncated]
        rw [← hans]
        exact hout

/-- Exact full-jet agreement implies that replay against the single final
operator has exactly the same leaf output as the online simulation. -/
theorem run_hiddenOperator_eq_runTruncated (p : ℕ) (profile : GateProfile)
    (Lp : ℝ) {R : ℝ} (hR : 0 < R) (N t : ℕ)
    (v : Fin (N + 1) → E) {budget : ℕ}
    (policy : DeterministicPolicy (Metric.closedBall (0 : E) R)
      (ExactJet E p) budget)
    (htri : IsTriangularTruncatedRun p profile Lp R N t v policy) :
    policy.run (exactJet p (hiddenOperator p profile Lp R N v)) =
      runTruncated p profile Lp R N t v policy := by
  induction policy generalizing t with
  | done output => simp [run, runTruncated]
  | @query budget queryPoint next ih =>
      have hjet := truncatedHiddenOperator_exactJet_eq p profile Lp hR N t v
        queryPoint.1 htri.1
      simp only [run, runTruncated]
      rw [← hjet]
      apply ih
      exact htri.2

/-- The exact semantic certificate that the online linear-algebra construction
must produce for `thm:det`. -/
def IsDeterministicResistingFrame (p : ℕ) (profile : GateProfile) (Lp R : ℝ)
    (N : ℕ) (v : Fin (N + 1) → E) {budget : ℕ}
    (policy : DeterministicPolicy (Metric.closedBall (0 : E) R)
      (ExactJet E p) budget) : Prop :=
  Orthonormal ℝ v ∧
  IsTriangularTruncatedRun p profile Lp R N 0 v policy ∧
  inner ℝ (v (Fin.last N))
    (runTruncated p profile Lp R N 0 v policy).1 = 0

/-- The online resisting construction exists for every deterministic policy
whose query budget is at most `N`. -/
theorem exists_deterministic_resisting_frame (p : ℕ) (profile : GateProfile)
    (Lp R : ℝ) (N : ℕ) {budget : ℕ} (hbudget : budget ≤ N)
    (hdim : 2 * N + 2 ≤ Module.finrank ℝ E)
    (policy : DeterministicPolicy (Metric.closedBall (0 : E) R)
      (ExactJet E p) budget) :
    ∃ v : Fin (N + 1) → E,
      IsDeterministicResistingFrame p profile Lp R N v policy := by
  let emptyFrame : Fin 0 → E := fun i => Fin.elim0 i
  let emptyHistory : Fin 0 → E := fun i => Fin.elim0 i
  have hempty : Orthonormal ℝ emptyFrame := Orthonormal.of_isEmpty _
  obtain ⟨v, hv, _hvempty, _hvhistory, htri, hout⟩ :=
    exists_resisting_extension p profile Lp R N 0 (Nat.zero_le _) hdim
      emptyFrame emptyHistory hempty policy (by simpa using hbudget)
  exact ⟨v, hv, htri, hout⟩

/-- A resisting-frame certificate guarantees both exact replay and the hidden
final-coordinate condition for the algorithm's arbitrary feasible output. -/
theorem deterministic_resisting_frame_replay_and_slab (p : ℕ)
    (profile : GateProfile) (Lp : ℝ) {R : ℝ} (hR : 0 < R) (N : ℕ)
    (v : Fin (N + 1) → E) {budget : ℕ}
    (policy : DeterministicPolicy (Metric.closedBall (0 : E) R)
      (ExactJet E p) budget)
    (hw : IsDeterministicResistingFrame p profile Lp R N v policy) :
    policy.run (exactJet p (hiddenOperator p profile Lp R N v)) =
        runTruncated p profile Lp R N 0 v policy ∧
      |inner ℝ (v (Fin.last N))
        (policy.run (exactJet p (hiddenOperator p profile Lp R N v))).1| ≤
          hiddenTau R N / 2 := by
  have hreplay := run_hiddenOperator_eq_runTruncated p profile Lp hR N 0 v policy hw.2.1
  refine ⟨hreplay, ?_⟩
  rw [hreplay, hw.2.2, abs_zero]
  exact div_nonneg (hiddenTau_pos hR N).le (by norm_num)

end DeterministicPolicy

end PolicyReplay

section ConditionalHeadline

/-- Conditional, non-vacuously named audit boundary for `thm:det`.

Everything after the causal online construction is kernel checked here.  The
premise `IsDeterministicResistingFrame` is intentionally visible: proving its
existence for every policy is the remaining strategy-tree recursion, and this
claim must not be confused with the unconditional theorem in the article. -/
def ConditionalDeterministicLowerClaim : Prop :=
  ∀ (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [Nontrivial E],
    ∀ (p : ℕ) (hp : 2 ≤ p) (profile : GateProfile)
      (Lp R : ℝ) (hLp : 0 < Lp) (hR : 0 < R)
      (N : ℕ) (hN : 1 ≤ N) (budget : ℕ) (_hbudget : budget ≤ N)
      (_hdim : 2 * N + 2 ≤ Module.finrank ℝ E)
      (policy : DeterministicPolicy (Metric.closedBall (0 : E) R)
        (ExactJet E p) budget) (v : Fin (N + 1) → E),
      DeterministicPolicy.IsDeterministicResistingFrame
          p profile Lp R N v policy →
        IsAdmissibleOperator (ballVIData (E := E) p hp Lp hLp R hR)
            (hiddenOperator p profile Lp R N v) ∧
        hiddenResidualClosedForm p profile Lp R N ≤
          tangentResidual (ballVIData (E := E) p hp Lp hLp R hR)
            (hiddenOperator p profile Lp R N v)
            (policy.run (exactJet p
              (hiddenOperator p profile Lp R N v))).1

/-- Kernel-checked conditional endpoint of the deterministic lower-bound
chain: exact transcript replay plus `lem:residual` gives the advertised hard
residual for the arbitrary feasible policy output. -/
theorem conditionalDeterministicLowerClaim_proof :
    ConditionalDeterministicLowerClaim := by
  intro E _ _ _ _ p hp profile Lp R hLp hR N hN budget _hbudget _hdim policy v hw
  have hslab :=
    (DeterministicPolicy.deterministic_resisting_frame_replay_and_slab
      p profile Lp hR N v policy hw).2
  refine ⟨hiddenOperator_admissible p hp profile hLp hR hN v hw.1, ?_⟩
  rcases hiddenResidualClaim_proof E p hp profile Lp R hLp hR N hN v hw.1
      _ (policy.run (exactJet p (hiddenOperator p profile Lp R N v))).2 hslab with
    ⟨hlower, hscale⟩
  rw [← hscale]
  exact hlower

/-- Unconditional deterministic lower-bound statement audited from
`thm:det`: every feasible exact-jet policy with at most `N` calls admits one
operator in the class on which its returned point has the stated residual. -/
def DeterministicLowerClaim : Prop :=
  ∀ (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [Nontrivial E],
    ∀ (p : ℕ) (hp : 2 ≤ p) (profile : GateProfile)
      (Lp R : ℝ) (hLp : 0 < Lp) (hR : 0 < R)
      (N : ℕ) (hN : 1 ≤ N) (budget : ℕ) (hbudget : budget ≤ N)
      (hdim : 2 * N + 2 ≤ Module.finrank ℝ E)
      (policy : DeterministicPolicy (Metric.closedBall (0 : E) R)
        (ExactJet E p) budget),
      ∃ v : Fin (N + 1) → E,
        Orthonormal ℝ v ∧
        IsAdmissibleOperator (ballVIData (E := E) p hp Lp hLp R hR)
          (hiddenOperator p profile Lp R N v) ∧
        hiddenResidualClosedForm p profile Lp R N ≤
          tangentResidual (ballVIData (E := E) p hp Lp hLp R hR)
            (hiddenOperator p profile Lp R N v)
            (policy.run (exactJet p
              (hiddenOperator p profile Lp R N v))).1

/-- Kernel-checked unconditional deterministic endpoint. -/
theorem deterministicLowerClaim_proof : DeterministicLowerClaim := by
  intro E _ _ _ _ p hp profile Lp R hLp hR N hN budget hbudget hdim policy
  obtain ⟨v, hv⟩ :=
    DeterministicPolicy.exists_deterministic_resisting_frame
      p profile Lp R N hbudget hdim policy
  refine ⟨v, hv.1, ?_⟩
  exact conditionalDeterministicLowerClaim_proof E p hp profile Lp R hLp hR
    N hN budget hbudget hdim policy v hv

end ConditionalHeadline

end LeanArticleAudit.Pilot
