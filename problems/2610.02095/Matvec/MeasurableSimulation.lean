import Matvec.ModelMeasurable
import Matvec.OracleSimulation

/-!
# Measurable, seedwise two-call compilation of actual transcript policies

The target policies include every `Model.Algorithm`. The compiled policy
issues two ordinary sequential calls per target round. Its first query,
second query (after the first response), and terminal output are all Borel
functions of the seed and the complete available source transcript.
Simulation maps may depend measurably on the seed, allowing a random testing
basis sampled independently as an extra seed component.
-/

namespace Matvec
namespace MeasurableSimulation

open MeasureTheory

universe u v w s u' v'

structure Policy (Q : Type u) (R : Type v) (O : Type w) (T : ℕ)
    (Seed : Type s) [MeasurableSpace Q] [MeasurableSpace R]
    [MeasurableSpace O] [MeasurableSpace Seed] where
  query : (j : ℕ) → Seed → (Fin j → R) → Q
  query_measurable : ∀ j, Measurable (fun p : Seed × (Fin j → R) => query j p.1 p.2)
  output : Seed → (Fin T → R) → O
  output_measurable : Measurable (fun p : Seed × (Fin T → R) => output p.1 p.2)

namespace Policy

variable {Q : Type u} {R : Type v} {O : Type w} {Seed : Type s}
  [MeasurableSpace Q] [MeasurableSpace R] [MeasurableSpace O] [MeasurableSpace Seed]
  {T : ℕ}

def transcript (alg : Policy Q R O T Seed) (oracle : Q → R) (seed : Seed) :
    (j : ℕ) → (Fin j → R)
  | 0 => Fin.elim0
  | j + 1 => Fin.snoc (alg.transcript oracle seed j)
      (oracle (alg.query j seed (alg.transcript oracle seed j)))

def run (alg : Policy Q R O T Seed) (oracle : Q → R) (seed : Seed) : O :=
  alg.output seed (alg.transcript oracle seed T)

theorem measurable_transcript (alg : Policy Q R O T Seed) (oracle : Q → R)
    (horacle : Measurable oracle) (j : ℕ) :
    Measurable (fun seed => alg.transcript oracle seed j) := by
  induction j with
  | zero => exact measurable_const
  | succ j ih =>
    apply measurable_pi_lambda
    intro i
    refine Fin.lastCases ?_ (fun i => ?_) i
    · simp only [transcript, Fin.snoc_last]
      exact horacle.comp ((alg.query_measurable j).comp (measurable_id.prodMk ih))
    · simpa only [transcript, Fin.snoc_castSucc] using (measurable_pi_apply i).comp ih

theorem measurable_run (alg : Policy Q R O T Seed) (oracle : Q → R)
    (horacle : Measurable oracle) : Measurable (alg.run oracle) :=
  alg.output_measurable.comp (measurable_id.prodMk (alg.measurable_transcript oracle horacle T))

end Policy

/-- Every quantified matrix-game algorithm is already a policy of this type. -/
def ofAlgorithm {m n T : ℕ} {Seed : Type s} [MeasurableSpace Seed]
    (alg : Algorithm m n T Seed) : Policy (Query m n) (Reply m n) (Query m n) T Seed where
  query := alg.query
  query_measurable := alg.query_measurable
  output := alg.output
  output_measurable := alg.output_measurable

theorem ofAlgorithm_transcript {m n T : ℕ} {Seed : Type s} [MeasurableSpace Seed]
    (alg : Algorithm m n T Seed) (A : Payoff m n) (seed : Seed) (j : ℕ) :
    (ofAlgorithm alg).transcript (oracle A) seed j = alg.transcript A seed j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [Policy.transcript, Algorithm.transcript, ih]
    rfl

theorem ofAlgorithm_run {m n T : ℕ} {Seed : Type s} [MeasurableSpace Seed]
    (alg : Algorithm m n T Seed) (A : Payoff m n) (seed : Seed) :
    (ofAlgorithm alg).run (oracle A) seed = alg.run A seed := by
  change alg.output seed ((ofAlgorithm alg).transcript (oracle A) seed T) = _
  rw [ofAlgorithm_transcript]
  rfl

structure TwoCallMap (Q : Type u) (R : Type v) (Q' : Type u') (R' : Type v')
    (Seed : Type s) [MeasurableSpace Q] [MeasurableSpace R]
    [MeasurableSpace Q'] [MeasurableSpace R'] [MeasurableSpace Seed] where
  first : Seed → Q → Q'
  second : Seed → Q → R' → Q'
  combine : Seed → Q → (R' × R') → R
  first_measurable : Measurable (fun p : Seed × Q => first p.1 p.2)
  second_measurable : Measurable (fun p : Seed × (Q × R') => second p.1 p.2.1 p.2.2)
  combine_measurable : Measurable (fun p : Seed × (Q × (R' × R')) => combine p.1 p.2.1 p.2.2)

/-- A genuinely sequential ordinary-oracle policy. Each round has two calls;
the second can depend on the first response. -/
structure PairedPolicy (Q : Type u) (R : Type v) (O : Type w) (T : ℕ)
    (Seed : Type s) [MeasurableSpace Q] [MeasurableSpace R]
    [MeasurableSpace O] [MeasurableSpace Seed] where
  first : (j : ℕ) → Seed → (Fin j → R × R) → Q
  second : (j : ℕ) → Seed → (Fin j → R × R) → R → Q
  output : Seed → (Fin T → R × R) → O
  first_measurable : ∀ j, Measurable (fun p : Seed × (Fin j → R × R) => first j p.1 p.2)
  second_measurable : ∀ j,
    Measurable (fun p : Seed × ((Fin j → R × R) × R) => second j p.1 p.2.1 p.2.2)
  output_measurable : Measurable (fun p : Seed × (Fin T → R × R) => output p.1 p.2)

section Compile

variable {Q : Type u} {R : Type v} {O : Type w} {Seed : Type s}
  {Q' : Type u'} {R' : Type v'} [MeasurableSpace Q] [MeasurableSpace R]
  [MeasurableSpace O] [MeasurableSpace Seed] [MeasurableSpace Q'] [MeasurableSpace R']
  {T : ℕ}

def decode (alg : Policy Q R O T Seed) (sim : TwoCallMap Q R Q' R' Seed) :
    (j : ℕ) → Seed → (Fin j → R' × R') → (Fin j → R)
  | 0, _, _ => Fin.elim0
  | j + 1, seed, h =>
    let past := decode alg sim j seed (Fin.init h)
    Fin.snoc past (sim.combine seed (alg.query j seed past) (h (Fin.last j)))

theorem measurable_decode (alg : Policy Q R O T Seed) (sim : TwoCallMap Q R Q' R' Seed)
    (j : ℕ) : Measurable (fun p : Seed × (Fin j → R' × R') => decode alg sim j p.1 p.2) := by
  induction j with
  | zero => exact measurable_const
  | succ j ih =>
    have hinit : Measurable (fun p : Seed × (Fin (j + 1) → R' × R') =>
        (p.1, Fin.init p.2)) := by
      apply Measurable.prodMk measurable_fst
      apply measurable_pi_lambda
      intro i
      exact (measurable_pi_apply i.castSucc).comp measurable_snd
    have hpast := ih.comp hinit
    have hq := (alg.query_measurable j).comp (measurable_fst.prodMk hpast)
    have hlast : Measurable (fun p : Seed × (Fin (j + 1) → R' × R') => p.2 (Fin.last j)) :=
      (measurable_pi_apply (Fin.last j)).comp measurable_snd
    apply measurable_pi_lambda
    intro i
    refine Fin.lastCases ?_ (fun i => ?_) i
    · simpa only [decode, Fin.snoc_last] using
        sim.combine_measurable.comp (measurable_fst.prodMk (hq.prodMk hlast))
    · simpa only [decode, Fin.snoc_castSucc] using (measurable_pi_apply i).comp hpast

def compile (alg : Policy Q R O T Seed) (sim : TwoCallMap Q R Q' R' Seed) :
    PairedPolicy Q' R' O T Seed where
  first j seed h := sim.first seed (alg.query j seed (decode alg sim j seed h))
  second j seed h r := sim.second seed (alg.query j seed (decode alg sim j seed h)) r
  output seed h := alg.output seed (decode alg sim T seed h)
  first_measurable j := sim.first_measurable.comp
    (measurable_fst.prodMk ((alg.query_measurable j).comp
      (measurable_fst.prodMk (measurable_decode alg sim j))))
  second_measurable j := by
    have hpast : Measurable (fun p : Seed × ((Fin j → R' × R') × R') =>
        decode alg sim j p.1 p.2.1) := (measurable_decode alg sim j).comp
      (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
    have hq := (alg.query_measurable j).comp (measurable_fst.prodMk hpast)
    exact sim.second_measurable.comp
      (measurable_fst.prodMk (hq.prodMk (measurable_snd.comp measurable_snd)))
  output_measurable := alg.output_measurable.comp
    (measurable_fst.prodMk (measurable_decode alg sim T))

end Compile

namespace PairedPolicy

variable {Q : Type u} {R : Type v} {O : Type w} {Seed : Type s}
  [MeasurableSpace Q] [MeasurableSpace R] [MeasurableSpace O] [MeasurableSpace Seed]
  {T : ℕ}

def step (alg : PairedPolicy Q R O T Seed) (oracle : Q → R) (j : ℕ)
    (seed : Seed) (h : Fin j → R × R) : R × R :=
  let r := oracle (alg.first j seed h)
  (r, oracle (alg.second j seed h r))

def transcript (alg : PairedPolicy Q R O T Seed) (oracle : Q → R) (seed : Seed) :
    (j : ℕ) → (Fin j → R × R)
  | 0 => Fin.elim0
  | j + 1 => Fin.snoc (alg.transcript oracle seed j)
      (alg.step oracle j seed (alg.transcript oracle seed j))

def run (alg : PairedPolicy Q R O T Seed) (oracle : Q → R) (seed : Seed) : O :=
  alg.output seed (alg.transcript oracle seed T)

theorem measurable_step (alg : PairedPolicy Q R O T Seed) (oracle : Q → R)
    (horacle : Measurable oracle) (j : ℕ) :
    Measurable (fun p : Seed × (Fin j → R × R) => alg.step oracle j p.1 p.2) := by
  have hr := horacle.comp (alg.first_measurable j)
  exact hr.prodMk (horacle.comp ((alg.second_measurable j).comp
    (measurable_fst.prodMk (measurable_snd.prodMk hr))))

theorem measurable_transcript (alg : PairedPolicy Q R O T Seed) (oracle : Q → R)
    (horacle : Measurable oracle) (j : ℕ) :
    Measurable (fun seed => alg.transcript oracle seed j) := by
  induction j with
  | zero => exact measurable_const
  | succ j ih =>
    apply measurable_pi_lambda
    intro i
    refine Fin.lastCases ?_ (fun i => ?_) i
    · simpa only [transcript, Fin.snoc_last] using
        (alg.measurable_step oracle horacle j).comp (measurable_id.prodMk ih)
    · simpa only [transcript, Fin.snoc_castSucc] using (measurable_pi_apply i).comp ih

theorem measurable_run (alg : PairedPolicy Q R O T Seed) (oracle : Q → R)
    (horacle : Measurable oracle) : Measurable (alg.run oracle) :=
  alg.output_measurable.comp (measurable_id.prodMk (alg.measurable_transcript oracle horacle T))

/-- Flatten paired calls into the existing primitive one-call program syntax. -/
def programFrom (alg : PairedPolicy Q R O T Seed) (seed : Seed) :
    (k j : ℕ) → j + k = T → (Fin j → R × R) → QueryProgram Q R O (2 * k)
  | 0, j, hj, h => .pure (alg.output seed (fun i => h ⟨i.val, by omega⟩))
  | k + 1, j, hj, h => .query (alg.first j seed h) (fun r₁ =>
      .query (alg.second j seed h r₁) (fun r₂ =>
        alg.programFrom seed k (j + 1) (by omega) (Fin.snoc h (r₁, r₂))))

def toProgram (alg : PairedPolicy Q R O T Seed) (seed : Seed) : QueryProgram Q R O (2 * T) :=
  alg.programFrom seed T 0 (by omega) Fin.elim0

theorem programFrom_eval (alg : PairedPolicy Q R O T Seed) (oracle : Q → R) (seed : Seed)
    (k j : ℕ) (hj : j + k = T) :
    (alg.programFrom seed k j hj (alg.transcript oracle seed j)).eval oracle =
      alg.run oracle seed := by
  induction k generalizing j with
  | zero =>
    have heq : j = T := by omega
    subst j
    rfl
  | succ k ih =>
    simp only [programFrom, QueryProgram.eval]
    exact ih (j + 1) (by omega)

theorem toProgram_eval (alg : PairedPolicy Q R O T Seed) (oracle : Q → R) (seed : Seed) :
    (alg.toProgram seed).eval oracle = alg.run oracle seed :=
  alg.programFrom_eval oracle seed T 0 (by omega)

theorem toProgram_all_transcripts (alg : PairedPolicy Q R O T Seed) (seed : Seed)
    (replies : ℕ → Q → R) (round : ℕ) :
    (alg.toProgram seed).transcriptQueryCount replies round ≤ 2 * T :=
  QueryProgram.transcriptQueryCount_le _ _ _

end PairedPolicy

section Correctness

variable {Q : Type u} {R : Type v} {O : Type w} {Seed : Type s}
  {Q' : Type u'} {R' : Type v'} [MeasurableSpace Q] [MeasurableSpace R]
  [MeasurableSpace O] [MeasurableSpace Seed] [MeasurableSpace Q'] [MeasurableSpace R']
  {T : ℕ}

theorem decode_transcript (alg : Policy Q R O T Seed) (sim : TwoCallMap Q R Q' R' Seed)
    (source : Q' → R') (target : Seed → Q → R)
    (hsim : ∀ seed q, sim.combine seed q
      (source (sim.first seed q), source (sim.second seed q (source (sim.first seed q)))) =
        target seed q) (seed : Seed) (j : ℕ) :
    decode alg sim j seed ((compile alg sim).transcript source seed j) =
      alg.transcript (target seed) seed j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [PairedPolicy.transcript, decode, Fin.init_snoc, Fin.snoc_last,
      PairedPolicy.step, compile, hsim, Policy.transcript]
    simpa only [compile] using congrArg
      (fun h : Fin j → R => Fin.snoc (α := fun _ => R) h
        (target seed (alg.query j seed h))) ih

theorem compile_run (alg : Policy Q R O T Seed) (sim : TwoCallMap Q R Q' R' Seed)
    (source : Q' → R') (target : Seed → Q → R)
    (hsim : ∀ seed q, sim.combine seed q
      (source (sim.first seed q), source (sim.second seed q (source (sim.first seed q)))) =
        target seed q) (seed : Seed) :
    (compile alg sim).run source seed = alg.run (target seed) seed := by
  exact congrArg (alg.output seed) (decode_transcript alg sim source target hsim seed T)

theorem compile_program_eval (alg : Policy Q R O T Seed) (sim : TwoCallMap Q R Q' R' Seed)
    (source : Q' → R') (target : Seed → Q → R)
    (hsim : ∀ seed q, sim.combine seed q
      (source (sim.first seed q), source (sim.second seed q (source (sim.first seed q)))) =
        target seed q) (seed : Seed) :
    ((compile alg sim).toProgram seed).eval source = alg.run (target seed) seed := by
  rw [PairedPolicy.toProgram_eval, compile_run alg sim source target hsim]

theorem compile_success_event (alg : Policy Q R O T Seed) (sim : TwoCallMap Q R Q' R' Seed)
    (source : Q' → R') (target : Seed → Q → R)
    (hsim : ∀ seed q, sim.combine seed q
      (source (sim.first seed q), source (sim.second seed q (source (sim.first seed q)))) =
        target seed q) (success : Seed → O → Prop) :
    {seed | success seed ((compile alg sim).run source seed)} =
      {seed | success seed (alg.run (target seed) seed)} := by
  ext seed
  simp only [Set.mem_setOf_eq, compile_run alg sim source target hsim]

end Correctness

noncomputable section
open Matrix
open scoped Matrix

section Concrete

variable {d m n : Type*} [Fintype d] [Fintype m] [Fintype n]
  {Seed : Type s} [MeasurableSpace Seed]

def simplexMap (b : d → ℝ) (R : Matrix d m ℝ) (V : Matrix d n ℝ) (Λ : ℝ) :
    TwoCallMap ((n → ℝ) × (m → ℝ)) ((m → ℝ) × (n → ℝ)) (d → ℝ) (d → ℝ) Seed where
  first _ q := V *ᵥ q.1
  second _ q _ := R *ᵥ q.2
  combine _ q replies := simplexCombine b R V Λ q replies.1 replies.2
  first_measurable := by
    apply measurable_pi_lambda
    intro i
    simp only [Matrix.mulVec, dotProduct]
    fun_prop
  second_measurable := by
    apply measurable_pi_lambda
    intro i
    simp only [Matrix.mulVec, dotProduct]
    fun_prop
  combine_measurable := by
    unfold simplexCombine
    apply Measurable.prodMk
    all_goals
      apply measurable_pi_lambda
      intro i
      simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      fun_prop

theorem simplexMap_correct (H : Matrix d d ℝ) (hH : H.transpose = H)
    (b : d → ℝ) (R : Matrix d m ℝ) (V : Matrix d n ℝ) (Λ : ℝ)
    (seed : Seed) (q : (n → ℝ) × (m → ℝ)) :
    (simplexMap b R V Λ).combine seed q
      (H *ᵥ ((simplexMap b R V Λ).first seed q),
        H *ᵥ ((simplexMap b R V Λ).second seed q
          (H *ᵥ ((simplexMap b R V Λ).first seed q)))) =
      matrixOracle (simplexMatrix H b R V Λ) q :=
  simplexCombine_correct H hH b R V Λ q

def ballMap (b : d → ℝ) (α β : ℝ) :
    TwoCallMap (((d ⊕ Unit) → ℝ) × ((d ⊕ d) → ℝ))
      (((d ⊕ d) → ℝ) × ((d ⊕ Unit) → ℝ)) (d → ℝ) (d → ℝ) Seed where
  first _ q i := q.1 (Sum.inl i)
  second _ q _ i := q.2 (Sum.inl i) - q.2 (Sum.inr i)
  combine _ q replies := ballCombine b α β q replies.1 replies.2
  first_measurable := by fun_prop
  second_measurable := by fun_prop
  combine_measurable := by
    unfold ballCombine
    apply Measurable.prodMk
    · apply measurable_pi_lambda
      intro i
      cases i <;> simp only [Pi.neg_apply, Sum.elim_inl, Sum.elim_inr] <;> fun_prop
    · apply measurable_pi_lambda
      intro i
      cases i <;> simp only [Pi.neg_apply, Sum.elim_inl, Sum.elim_inr,
        Pi.smul_apply, smul_eq_mul, dotProduct, Pi.sub_apply] <;> fun_prop

theorem ballMap_correct (H : Matrix d d ℝ) (hH : H.transpose = H)
    (b : d → ℝ) (α β : ℝ) (seed : Seed)
    (q : ((d ⊕ Unit) → ℝ) × ((d ⊕ d) → ℝ)) :
    (ballMap b α β).combine seed q
      (H *ᵥ ((ballMap b α β).first seed q),
        H *ᵥ ((ballMap b α β).second seed q
          (H *ᵥ ((ballMap b α β).first seed q)))) =
      matrixOracle (-ballMatrix H b α β) q :=
  ballCombine_correct H hH b α β q

end Concrete

theorem compile_simplex_algorithm_run {d m n T : ℕ} {Seed : Type s} [MeasurableSpace Seed]
    (alg : Algorithm m n T Seed) (H : Matrix (Fin d) (Fin d) ℝ) (hH : H.transpose = H)
    (b : Fin d → ℝ) (R : Matrix (Fin d) (Fin m) ℝ) (V : Matrix (Fin d) (Fin n) ℝ)
    (Λ : ℝ) (seed : Seed) :
    (compile (ofAlgorithm alg) (simplexMap b R V Λ)).run H.mulVec seed =
      alg.run (simplexMatrix H b R V Λ) seed := by
  calc
    _ = (ofAlgorithm alg).run (matrixOracle (simplexMatrix H b R V Λ)) seed :=
      compile_run _ _ H.mulVec (fun _ => matrixOracle (simplexMatrix H b R V Λ))
        (simplexMap_correct H hH b R V Λ) seed
    _ = _ := ofAlgorithm_run alg _ seed

theorem compile_simplex_algorithm_all_transcripts {d m n T : ℕ} {Seed : Type s}
    [MeasurableSpace Seed] (alg : Algorithm m n T Seed) (b : Fin d → ℝ)
    (R : Matrix (Fin d) (Fin m) ℝ) (V : Matrix (Fin d) (Fin n) ℝ) (Λ : ℝ)
    (seed : Seed) (replies : ℕ → (Fin d → ℝ) → (Fin d → ℝ)) (round : ℕ) :
    ((compile (ofAlgorithm alg) (simplexMap b R V Λ)).toProgram seed).transcriptQueryCount
      replies round ≤ 2 * T :=
  PairedPolicy.toProgram_all_transcripts _ _ _ _

end
end MeasurableSimulation
end Matvec
