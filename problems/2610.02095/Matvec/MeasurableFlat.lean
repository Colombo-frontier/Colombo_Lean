import Matvec.MeasurableSimulation

/-!
# Ordinary single-call form of the measurable two-call compiler

The flattening below is itself a measurable fixed-horizon `Policy`, not just
a family of deterministic program trees. It uses exactly `2 * T` available
source replies and preserves the compiled output on every oracle and seed.
-/

namespace Matvec.MeasurableSimulation
open MeasureTheory

universe u v w s

namespace PairedPolicy

variable {Q : Type u} {R : Type v} {O : Type w} {Seed : Type s}
  [MeasurableSpace Q] [MeasurableSpace R] [MeasurableSpace O] [MeasurableSpace Seed]
  {T : ℕ}

/-- Read the first `k` consecutive response pairs from a longer transcript. -/
def pairPrefix (k j : ℕ) (h : Fin j → R) (hk : 2 * k ≤ j) : Fin k → R × R :=
  fun i => (h ⟨2 * i.val, by omega⟩, h ⟨2 * i.val + 1, by omega⟩)

theorem measurable_pairPrefix (k j : ℕ) (hk : 2 * k ≤ j) :
    Measurable (fun h : Fin j → R => pairPrefix k j h hk) := by
  apply measurable_pi_lambda
  intro i
  exact (measurable_pi_apply _).prodMk (measurable_pi_apply _)

omit [MeasurableSpace R] in
theorem pairPrefix_snoc (k j : ℕ) (h : Fin j → R) (r : R)
    (hk : 2 * k ≤ j) (hk' : 2 * k ≤ j + 1) :
    pairPrefix k (j + 1) (Fin.snoc h r) hk' = pairPrefix k j h hk := by
  ext i : 1
  have h₀ : 2 * i.val < j := by omega
  have h₁ : 2 * i.val + 1 < j := by omega
  simp [pairPrefix, Fin.snoc, h₀, h₁]

omit [MeasurableSpace R] in
theorem pairPrefix_two_snoc (j : ℕ) (h : Fin (2 * j) → R) (r₁ r₂ : R) :
    pairPrefix (j + 1) (2 * j + 1 + 1) (Fin.snoc (Fin.snoc h r₁) r₂) (by omega) =
      Fin.snoc (pairPrefix j (2 * j) h (by omega)) (r₁, r₂) := by
  ext i : 1
  refine Fin.lastCases ?_ (fun i => ?_) i
  · simp [pairPrefix, Fin.snoc]
  · have h₀ : 2 * i.val < 2 * j := by omega
    have h₁ : 2 * i.val + 1 < 2 * j := by omega
    simp [pairPrefix, Fin.snoc, h₀, h₁, show 2 * i.val < 2 * j + 1 by omega,
      show 2 * i.val + 1 < 2 * j + 1 by omega]

/-- A standard measurable policy with one source query at each of `2*T` steps. -/
def toPolicy (alg : PairedPolicy Q R O T Seed) : Policy Q R O (2 * T) Seed where
  query j seed h :=
    let paired := pairPrefix (j / 2) j h (by omega)
    if heven : j % 2 = 0 then alg.first (j / 2) seed paired
    else alg.second (j / 2) seed paired (h ⟨j - 1, by omega⟩)
  output seed h := alg.output seed (pairPrefix T (2 * T) h (by omega))
  query_measurable j := by
    dsimp only
    split_ifs
    · exact (alg.first_measurable (j / 2)).comp
        (measurable_fst.prodMk ((measurable_pairPrefix (j / 2) j (by omega)).comp
          measurable_snd))
    · exact (alg.second_measurable (j / 2)).comp
        (measurable_fst.prodMk
          (((measurable_pairPrefix (j / 2) j (by omega)).comp measurable_snd).prodMk
            ((measurable_pi_apply _).comp measurable_snd)))
  output_measurable := alg.output_measurable.comp
    (measurable_fst.prodMk ((measurable_pairPrefix T (2 * T) (by omega)).comp measurable_snd))

private theorem first_pairPrefix_congr (alg : PairedPolicy Q R O T Seed)
    (k l j : ℕ) (hkl : k = l) (seed : Seed) (h : Fin j → R)
    (hk : 2 * k ≤ j) (hl : 2 * l ≤ j) :
    alg.first k seed (pairPrefix k j h hk) = alg.first l seed (pairPrefix l j h hl) := by
  subst l
  rfl

private theorem second_pairPrefix_congr (alg : PairedPolicy Q R O T Seed)
    (k l j : ℕ) (hkl : k = l) (seed : Seed) (h : Fin j → R) (r : R)
    (hk : 2 * k ≤ j) (hl : 2 * l ≤ j) :
    alg.second k seed (pairPrefix k j h hk) r =
      alg.second l seed (pairPrefix l j h hl) r := by
  subst l
  rfl

theorem toPolicy_query_even (alg : PairedPolicy Q R O T Seed) (j : ℕ)
    (seed : Seed) (h : Fin (2 * j) → R) :
    alg.toPolicy.query (2 * j) seed h =
      alg.first j seed (pairPrefix j (2 * j) h (by omega)) := by
  dsimp only [toPolicy]
  simp only [Nat.mul_mod_right, dite_true]
  exact first_pairPrefix_congr alg _ _ _ (by omega) seed h _ _

theorem toPolicy_query_odd (alg : PairedPolicy Q R O T Seed) (j : ℕ)
    (seed : Seed) (h : Fin (2 * j) → R) (r : R) :
    alg.toPolicy.query (2 * j + 1) seed (Fin.snoc h r) =
      alg.second j seed (pairPrefix j (2 * j) h (by omega)) r := by
  have hdiv : (2 * j + 1) / 2 = j := by omega
  have hmod : (2 * j + 1) % 2 ≠ 0 := by omega
  dsimp only [toPolicy]
  simp only [dif_neg hmod]
  rw [second_pairPrefix_congr alg _ j _ hdiv seed (Fin.snoc h r) _ _ (by omega)]
  rw [pairPrefix_snoc j (2 * j) h r (by omega)]
  congr 1
  simp [Fin.snoc]

theorem toPolicy_transcript (alg : PairedPolicy Q R O T Seed) (oracle : Q → R)
    (seed : Seed) (j : ℕ) :
    pairPrefix j (2 * j) (alg.toPolicy.transcript oracle seed (2 * j)) (by omega) =
      alg.transcript oracle seed j := by
  induction j with
  | zero => exact Subsingleton.elim _ _
  | succ j ih =>
    change pairPrefix (j + 1) (2 * j + 1 + 1)
      (alg.toPolicy.transcript oracle seed (2 * j + 1 + 1)) _ = _
    simp only [Policy.transcript, toPolicy_query_odd, toPolicy_query_even]
    rw [pairPrefix_two_snoc]
    simp only [ih, transcript, step]

theorem toPolicy_run (alg : PairedPolicy Q R O T Seed) (oracle : Q → R) (seed : Seed) :
    alg.toPolicy.run oracle seed = alg.run oracle seed := by
  exact congrArg (alg.output seed) (alg.toPolicy_transcript oracle seed T)

end PairedPolicy

end Matvec.MeasurableSimulation
