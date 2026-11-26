import Matvec.MeasurableSimulation

/-!
# Measurable sequential composition with additive hard query budgets

Both phases may use arbitrary measurable functions of their complete available
transcript. The second phase additionally receives the first phase's terminal
output. All definitions are total on inconsistent and off-promise transcripts.
-/

namespace Matvec.MeasurableSimulation.Policy
open MeasureTheory

universe u v w w' s s'

variable {Q : Type u} {R : Type v} {O : Type w} {P : Type w'}
  {Seed : Type s} {Seed' : Type s'} [MeasurableSpace Q] [MeasurableSpace R]
  [MeasurableSpace O] [MeasurableSpace P] [MeasurableSpace Seed] [MeasurableSpace Seed']
  {T U : ℕ}

def mapOutput (alg : Policy Q R O T Seed) (f : Seed → O → P)
    (hf : Measurable (fun p : Seed × O => f p.1 p.2)) : Policy Q R P T Seed where
  query := alg.query
  query_measurable := alg.query_measurable
  output seed h := f seed (alg.output seed h)
  output_measurable := hf.comp (measurable_fst.prodMk alg.output_measurable)

theorem mapOutput_transcript (alg : Policy Q R O T Seed) (f : Seed → O → P)
    (hf : Measurable (fun p : Seed × O => f p.1 p.2))
    (oracle : Q → R) (seed : Seed) (j : ℕ) :
    (alg.mapOutput f hf).transcript oracle seed j = alg.transcript oracle seed j := by
  induction j with
  | zero => rfl
  | succ j ih => rw [transcript, transcript, ih]; rfl

theorem mapOutput_run (alg : Policy Q R O T Seed) (f : Seed → O → P)
    (hf : Measurable (fun p : Seed × O => f p.1 p.2))
    (oracle : Q → R) (seed : Seed) :
    (alg.mapOutput f hf).run oracle seed = f seed (alg.run oracle seed) := by
  change f seed (alg.output seed _) = _
  rw [mapOutput_transcript]
  rfl

def seedMap (alg : Policy Q R O T Seed) (f : Seed' → Seed) (hf : Measurable f) :
    Policy Q R O T Seed' where
  query j seed h := alg.query j (f seed) h
  query_measurable j := (alg.query_measurable j).comp
    ((hf.comp measurable_fst).prodMk measurable_snd)
  output seed h := alg.output (f seed) h
  output_measurable := alg.output_measurable.comp
    ((hf.comp measurable_fst).prodMk measurable_snd)

theorem seedMap_transcript (alg : Policy Q R O T Seed) (f : Seed' → Seed) (hf : Measurable f)
    (oracle : Q → R) (seed : Seed') (j : ℕ) :
    (alg.seedMap f hf).transcript oracle seed j = alg.transcript oracle (f seed) j := by
  induction j with
  | zero => rfl
  | succ j ih => rw [transcript, transcript, ih]; rfl

theorem seedMap_run (alg : Policy Q R O T Seed) (f : Seed' → Seed) (hf : Measurable f)
    (oracle : Q → R) (seed : Seed') :
    (alg.seedMap f hf).run oracle seed = alg.run oracle (f seed) := by
  change alg.output (f seed) _ = _
  rw [seedMap_transcript]
  rfl

def historySegment (offset len total : ℕ) (h : Fin total → R)
    (hbound : offset + len ≤ total) : Fin len → R :=
  fun i => h ⟨offset + i.val, by omega⟩

theorem measurable_historySegment (offset len total : ℕ) (hbound : offset + len ≤ total) :
    Measurable (fun h : Fin total → R => historySegment offset len total h hbound) := by
  apply measurable_pi_lambda
  intro i
  exact measurable_pi_apply _

omit [MeasurableSpace R] in
theorem historySegment_snoc (offset len total : ℕ) (h : Fin total → R) (r : R)
    (hbound : offset + len ≤ total) (hbound' : offset + len ≤ total + 1) :
    historySegment offset len (total + 1) (Fin.snoc h r) hbound' =
      historySegment offset len total h hbound := by
  ext i
  have hi : offset + i.val < total := by omega
  simp [historySegment, Fin.snoc, hi]

omit [MeasurableSpace R] in
theorem historySegment_tail_snoc (offset len : ℕ) (h : Fin (offset + len) → R) (r : R) :
    historySegment offset (len + 1) (offset + len + 1) (Fin.snoc h r) (by omega) =
      Fin.snoc (historySegment offset len (offset + len) h (by omega)) r := by
  ext i
  refine Fin.lastCases ?_ (fun i => ?_) i
  · simp [historySegment, Fin.snoc]
  · have hi : offset + i.val < offset + len := by omega
    simp [historySegment, Fin.snoc, hi]

theorem transcript_prefix (alg : Policy Q R O T Seed) (oracle : Q → R) (seed : Seed)
    (j k : ℕ) (hjk : j ≤ k) :
    historySegment 0 j k (alg.transcript oracle seed k) (by omega) =
      alg.transcript oracle seed j := by
  induction k with
  | zero =>
    have : j = 0 := by omega
    subst j
    exact Subsingleton.elim _ _
  | succ k ih =>
    by_cases heq : j = k + 1
    · subst j
      funext i
      exact congrArg (alg.transcript oracle seed (k + 1))
        (show (⟨0 + i.val, by omega⟩ : Fin (k + 1)) = i from Fin.ext (Nat.zero_add i.val))
    · have hjk' : j ≤ k := by omega
      rw [transcript, historySegment_snoc 0 j k _ _ (by omega)]
      exact ih hjk'

/-- Sequential composition: the second seed is the original seed together
with the first phase's output. The hard horizon is exactly `T + U`. -/
def bind (first : Policy Q R O T Seed) (next : Policy Q R P U (Seed × O)) :
    Policy Q R P (T + U) Seed where
  query j seed h :=
    if hj : j < T then first.query j seed h
    else next.query (j - T)
      (seed, first.output seed (historySegment 0 T j h (by omega)))
      (historySegment T (j - T) j h (by omega))
  output seed h := next.output
    (seed, first.output seed (historySegment 0 T (T + U) h (by omega)))
    (historySegment T U (T + U) h (by omega))
  query_measurable j := by
    split_ifs with hj
    · exact first.query_measurable j
    · have hout : Measurable (fun p : Seed × (Fin j → R) =>
          first.output p.1 (historySegment 0 T j p.2 (by omega))) :=
        first.output_measurable.comp (measurable_fst.prodMk
          ((measurable_historySegment 0 T j (by omega)).comp measurable_snd))
      exact (next.query_measurable (j - T)).comp
        ((measurable_fst.prodMk hout).prodMk
          ((measurable_historySegment T (j - T) j (by omega)).comp measurable_snd))
  output_measurable := by
    have hout : Measurable (fun p : Seed × (Fin (T + U) → R) =>
        first.output p.1 (historySegment 0 T (T + U) p.2 (by omega))) :=
      first.output_measurable.comp (measurable_fst.prodMk
        ((measurable_historySegment 0 T (T + U) (by omega)).comp measurable_snd))
    exact next.output_measurable.comp ((measurable_fst.prodMk hout).prodMk
      ((measurable_historySegment T U (T + U) (by omega)).comp measurable_snd))

theorem bind_transcript_first (first : Policy Q R O T Seed)
    (next : Policy Q R P U (Seed × O)) (oracle : Q → R) (seed : Seed)
    (j : ℕ) (hj : j ≤ T) :
    (first.bind next).transcript oracle seed j = first.transcript oracle seed j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [transcript, transcript, ih (by omega)]
    simp only [bind, dif_pos (show j < T by omega)]

private theorem query_historySegment_congr (alg : Policy Q R O T Seed)
    (k l offset j : ℕ) (hkl : k = l) (seed : Seed) (h : Fin j → R)
    (hk : offset + k ≤ j) (hl : offset + l ≤ j) :
    alg.query k seed (historySegment offset k j h hk) =
      alg.query l seed (historySegment offset l j h hl) := by
  subst l
  rfl

theorem bind_query_second (first : Policy Q R O T Seed)
    (next : Policy Q R P U (Seed × O)) (seed : Seed) (j : ℕ) (h : Fin (T + j) → R) :
    (first.bind next).query (T + j) seed h =
      next.query j (seed, first.output seed (historySegment 0 T (T + j) h (by omega)))
        (historySegment T j (T + j) h (by omega)) := by
  dsimp only [bind]
  rw [dif_neg (show ¬T + j < T by omega)]
  exact query_historySegment_congr next _ j T _ (by omega) _ h _ _

theorem bind_transcript_second (first : Policy Q R O T Seed)
    (next : Policy Q R P U (Seed × O)) (oracle : Q → R) (seed : Seed) (j : ℕ) :
    historySegment T j (T + j) ((first.bind next).transcript oracle seed (T + j)) (by omega) =
      next.transcript oracle (seed, first.run oracle seed) j := by
  induction j with
  | zero => exact Subsingleton.elim _ _
  | succ j ih =>
    change historySegment T (j + 1) (T + j + 1)
      ((first.bind next).transcript oracle seed (T + j + 1)) _ = _
    rw [transcript, historySegment_tail_snoc]
    rw [bind_query_second]
    have hp := (first.bind next).transcript_prefix oracle seed T (T + j) (by omega)
    rw [bind_transcript_first first next oracle seed T le_rfl] at hp
    rw [hp]
    change Fin.snoc (α := fun _ => R) _
      (oracle (next.query j (seed, first.run oracle seed) _)) = _
    rw [ih]
    rfl

theorem bind_run (first : Policy Q R O T Seed) (next : Policy Q R P U (Seed × O))
    (oracle : Q → R) (seed : Seed) :
    (first.bind next).run oracle seed = next.run oracle (seed, first.run oracle seed) := by
  have hp := (first.bind next).transcript_prefix oracle seed T (T + U) (by omega)
  rw [bind_transcript_first first next oracle seed T le_rfl] at hp
  change next.output (seed, first.output seed _ ) _ = _
  rw [hp, bind_transcript_second]
  rfl

/-- Arbitrary measurable computation with no oracle calls. -/
def pure (q₀ : Q) (f : Seed → O) (hf : Measurable f) : Policy Q R O 0 Seed where
  query _ _ _ := q₀
  query_measurable _ := measurable_const
  output seed _ := f seed
  output_measurable := hf.comp measurable_fst

theorem pure_run (q₀ : Q) (f : Seed → O) (hf : Measurable f)
    (oracle : Q → R) (seed : Seed) : (pure q₀ f hf).run oracle seed = f seed := rfl

/-- One source query followed by arbitrary measurable postprocessing. -/
def ask (query : Seed → Q) (hq : Measurable query) (output : Seed → R → O)
    (ho : Measurable (fun p : Seed × R => output p.1 p.2)) : Policy Q R O 1 Seed where
  query _ seed _ := query seed
  query_measurable _ := hq.comp measurable_fst
  output seed h := output seed (h 0)
  output_measurable := ho.comp (measurable_fst.prodMk
    ((measurable_pi_apply 0).comp measurable_snd))

theorem ask_run (query : Seed → Q) (hq : Measurable query) (output : Seed → R → O)
    (ho : Measurable (fun p : Seed × R => output p.1 p.2)) (oracle : Q → R) (seed : Seed) :
    (ask query hq output ho).run oracle seed = output seed (oracle (query seed)) := rfl

def castHorizon (alg : Policy Q R O T Seed) (h : T = U) : Policy Q R O U Seed := h ▸ alg

theorem castHorizon_run (alg : Policy Q R O T Seed) (h : T = U)
    (oracle : Q → R) (seed : Seed) :
    (alg.castHorizon h).run oracle seed = alg.run oracle seed := by cases h; rfl

def programFrom (alg : Policy Q R O T Seed) (seed : Seed) :
    (k j : ℕ) → j + k = T → (Fin j → R) → QueryProgram Q R O k
  | 0, j, hj, h => .pure (alg.output seed (fun i => h ⟨i.val, by omega⟩))
  | k + 1, j, hj, h => .query (alg.query j seed h) (fun r =>
      alg.programFrom seed k (j + 1) (by omega) (Fin.snoc h r))

def toProgram (alg : Policy Q R O T Seed) (seed : Seed) : QueryProgram Q R O T :=
  alg.programFrom seed T 0 (by omega) Fin.elim0

theorem programFrom_eval (alg : Policy Q R O T Seed) (oracle : Q → R) (seed : Seed)
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

theorem toProgram_eval (alg : Policy Q R O T Seed) (oracle : Q → R) (seed : Seed) :
    (alg.toProgram seed).eval oracle = alg.run oracle seed :=
  alg.programFrom_eval oracle seed T 0 (by omega)

theorem toProgram_all_transcripts (alg : Policy Q R O T Seed) (seed : Seed)
    (replies : ℕ → Q → R) (round : ℕ) :
    (alg.toProgram seed).transcriptQueryCount replies round ≤ T :=
  QueryProgram.transcriptQueryCount_le _ _ _

end Matvec.MeasurableSimulation.Policy
