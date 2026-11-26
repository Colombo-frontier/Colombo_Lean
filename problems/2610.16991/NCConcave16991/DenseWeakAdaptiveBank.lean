import NCConcave16991.DenseWeakProductBank
import Mathlib.Data.Fin.Tuple.Basic

/-! # Actual adaptive row transcripts preserve column posterior independence

A depth-r experiment is a deterministic row decision tree. Its branches are
indexed by the full response vector of the bank. Thus arbitrary dependence on
all previous rows is represented, with any private seed fixed externally.
-/

noncomputable section

namespace NCConcave16991.DenseWeakHiding

universe u v w

inductive RowExperiment (I : Type u) (D : Type v) (Y : Type w) : ℕ → Type (max u v w)
  | done : RowExperiment I D Y 0
  | query {r : ℕ} (row : I) (next : (D → Y) → RowExperiment I D Y r) :
      RowExperiment I D Y (r + 1)

namespace RowExperiment

variable {I D Y A : Type*} {r : ℕ}

def run (read : A → I → Y) : {r : ℕ} → RowExperiment I D Y r → (D → A) →
    (Fin r → D → Y)
  | 0, .done, _ => Fin.elim0
  | _ + 1, .query i next, bank =>
      let y := fun d ↦ read (bank d) i
      Fin.cons y (run read (next y) bank)

def columnFibre (read : A → I → Y) : {r : ℕ} → RowExperiment I D Y r →
    (Fin r → D → Y) → D → Set A
  | 0, .done, _, _ => Set.univ
  | _ + 1, .query i next, h, d =>
      {a | read a i = h 0 d ∧ a ∈ columnFibre read (next (h 0)) (Fin.tail h) d}

def pathRow : {r : ℕ} → RowExperiment I D Y r → (Fin r → D → Y) → (Fin r → I)
  | 0, .done, _ => Fin.elim0
  | _ + 1, .query i next, h => Fin.cons i (pathRow (next (h 0)) (Fin.tail h))

theorem mem_columnFibre_iff (read : A → I → Y) (E : RowExperiment I D Y r)
    (h : Fin r → D → Y) (d : D) (a : A) :
    a ∈ E.columnFibre read h d ↔ ∀ t, read a (E.pathRow h t) = h t d := by
  induction E with
  | done => simp [columnFibre]
  | @query r i next ih =>
      simp only [columnFibre, Set.mem_setOf_eq, pathRow, Fin.forall_fin_succ,
        Fin.cons_zero, Fin.cons_succ, ih, Fin.tail]

def observedRows [DecidableEq I] (E : RowExperiment I D Y r) (h : Fin r → D → Y) : Finset I :=
  Finset.univ.image (E.pathRow h)

theorem observedRows_card [DecidableEq I] (E : RowExperiment I D Y r)
    (h : Fin r → D → Y) : (E.observedRows h).card ≤ r := by
  exact (Finset.card_image_le).trans (by simp)

/-- An adaptive observation fibre is literally rectangular in the independent
static columns. Adaptivity changes the fixed rectangle associated to a
transcript, and does not introduce posterior column dependence. -/
theorem run_eq_iff (read : A → I → Y) (E : RowExperiment I D Y r)
    (bank : D → A) (h : Fin r → D → Y) :
    E.run read bank = h ↔ ∀ d, bank d ∈ E.columnFibre read h d := by
  induction E with
  | done =>
      constructor
      · intro _ d; trivial
      · intro _; exact funext (fun i ↦ Fin.elim0 i)
  | @query r i next ih =>
      constructor
      · intro heq
        have hhead : (fun d ↦ read (bank d) i) = h 0 := congrFun heq 0
        have htail : (next (h 0)).run read bank = Fin.tail h := by
          simpa only [run, hhead, Fin.tail_cons] using congrArg Fin.tail heq
        have hcols := (ih (h 0) (Fin.tail h)).mp htail
        intro d
        exact ⟨congrFun hhead d, hcols d⟩
      · intro hc
        have hhead : (fun d ↦ read (bank d) i) = h 0 := funext (fun d ↦ (hc d).1)
        have htail := (ih (h 0) (Fin.tail h)).mpr (fun d ↦ (hc d).2)
        simp only [run, hhead, htail, Fin.cons_self_tail]

theorem run_fibre_eq_rectangle (read : A → I → Y) (E : RowExperiment I D Y r)
    (h : Fin r → D → Y) :
    {bank | E.run read bank = h} = FiniteLaw.rectangle (E.columnFibre read h) := by
  ext bank
  exact run_eq_iff read E bank h

variable [Fintype A] [Fintype D] [DecidableEq D]

/-- The probability of an actual adaptive transcript factors into its actual
per-column observation likelihoods. -/
theorem transcript_mass_factor (read : A → I → Y) (P : D → FiniteLaw A)
    (E : RowExperiment I D Y r) (h : Fin r → D → Y) :
    (FiniteLaw.pi P).eventMass {bank | E.run read bank = h} =
      ∏ d, (P d).eventMass (E.columnFibre read h d) := by
  rw [run_fibre_eq_rectangle, FiniteLaw.pi_rectangle_eventMass]

theorem transcript_positive_iff (read : A → I → Y) (P : D → FiniteLaw A)
    (E : RowExperiment I D Y r) (h : Fin r → D → Y) :
    0 < (FiniteLaw.pi P).eventMass {bank | E.run read bank = h} ↔
      ∀ d, 0 < (P d).eventMass (E.columnFibre read h d) := by
  rw [run_fibre_eq_rectangle, FiniteLaw.pi_rectangle_positive_iff]

/-- Exact posterior factorization after an arbitrary positive-mass adaptive
row transcript, derived from the original static product bank. -/
theorem posterior_mass_factor (read : A → I → Y) (P : D → FiniteLaw A)
    (E : RowExperiment I D Y r) (h : Fin r → D → Y)
    (hh : 0 < (FiniteLaw.pi P).eventMass {bank | E.run read bank = h}) (bank : D → A) :
    ((FiniteLaw.pi P).condition {bank | E.run read bank = h} hh).mass bank =
      (FiniteLaw.pi (fun d ↦ (P d).condition (E.columnFibre read h d)
        ((transcript_positive_iff read P E h).mp hh d))).mass bank := by
  have hcols := (transcript_positive_iff read P E h).mp hh
  simpa only [run_fibre_eq_rectangle] using
    FiniteLaw.pi_rectangle_condition_mass P (E.columnFibre read h) hcols bank

end RowExperiment

end NCConcave16991.DenseWeakHiding
