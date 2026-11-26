import MatchingBounds1005.ResponseHistory
import MatchingBounds1005.ShiftedSequential

/-!
# Exact recovery of the original physical-query transcript

Accumulation does not introduce additional policy decisions. At each round
the original row family is evaluated on the decoded history, and the actual
static latent parameter is queried once. The decoded joint law is proved
equal to that physical experiment for every round up to the finite horizon.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory

namespace MatchingBounds1005.PhysicalRowTranscript
open GaussianVector GaussianFitter SequentialPosterior AccumulatedRows ResponseHistory

variable {Ω W : Type*} [MeasurableSpace Ω] [MeasurableSpace W] {d H r : ℕ}

def current (seedView : Ω → W) (rows : (n : ℕ) → History W r n → Fin r → Vec d)
    (n : ℕ) (h : History Ω (H * r) n) : Fin r → Vec d := rows n (decode seedView n h)

theorem current_measurable (seedView : Ω → W) (hv : Measurable seedView)
    (rows : (n : ℕ) → History W r n → Fin r → Vec d)
    (hr : ∀ n i, Measurable (fun h => rows n h i)) (n : ℕ) (i : Fin r) :
    Measurable (fun h => current (H := H) seedView rows n h i) :=
  (hr n i).comp (decode_measurable seedView hv n)

def accumulatedProtocol (seedView : Ω → W) (hv : Measurable seedView)
    (rows : (n : ℕ) → History W r n → Fin r → Vec d)
    (hr : ∀ n i, Measurable (fun h => rows n h i)) : RowProtocol Ω d (H * r) :=
  protocol (current seedView rows) (current_measurable seedView hv rows hr)

def shiftedProtocol (seedView : Ω → W) (hv : Measurable seedView)
    (rows : (n : ℕ) → History W r n → Fin r → Vec d)
    (hr : ∀ n i, Measurable (fun h => rows n h i))
    (S : Ω → Vec d) (hS : Measurable S) : ShiftedSequential.ShiftedProtocol Ω d (H * r) where
  rowProtocol := accumulatedProtocol seedView hv rows hr
  signal := S
  measurable_signal := hS

def decodeJoint (seedView : Ω → W) (n : ℕ) (p : History Ω (H * r) n × Vec d) :
    History W r n × Vec d := (decode seedView n p.1, p.2)

theorem decodeJoint_measurable (seedView : Ω → W) (hv : Measurable seedView) (n : ℕ) :
    Measurable (decodeJoint (d := d) (H := H) (r := r) seedView n) :=
  ((decode_measurable seedView hv n).comp measurable_fst).prodMk measurable_snd

def rawUpdate (rows : (n : ℕ) → History W r n → Fin r → Vec d) (n : ℕ)
    (p : History W r n × Vec d) : History W r (n + 1) × Vec d :=
  ((p.1, rowResponse (rows n p.1) p.2), p.2)

theorem rawUpdate_measurable (rows : (n : ℕ) → History W r n → Fin r → Vec d)
    (hr : ∀ n i, Measurable (fun h => rows n h i)) (n : ℕ) : Measurable (rawUpdate rows n) :=
  (measurable_fst.prodMk (PosteriorGaussian.measurable_rowResponse_family (rows n) (hr n))).prodMk measurable_snd

theorem decode_staticUpdate (seedView : Ω → W) (hv : Measurable seedView)
    (rows : (n : ℕ) → History W r n → Fin r → Vec d)
    (hr : ∀ n i, Measurable (fun h => rows n h i)) (n : ℕ) (hn : n < H)
    (p : History Ω (H * r) n × Vec d) :
    decodeJoint seedView (n + 1) (staticUpdate (accumulatedProtocol seedView hv rows hr) n p) =
      rawUpdate rows n (decodeJoint seedView n p) := by
  change (decode seedView (n + 1) (p.1, rowResponse (accumulated (current seedView rows) n p.1) p.2), p.2) = _
  rw [decode_update (current seedView rows) seedView (⟨n, hn⟩ : Fin H)]
  rfl

def rawStaticJointLaw (seedView : Ω → W)
    (rows : (n : ℕ) → History W r n → Fin r → Vec d)
    (S : Ω → Vec d) (σ : ℝ) (ν₀ : Measure Ω) : (n : ℕ) → Measure (History W r n × Vec d)
  | 0 => (ν₀.prod (standardGaussian d)).map (fun p => (seedView p.1, S p.1 + σ • p.2))
  | n + 1 => (rawStaticJointLaw seedView rows S σ ν₀ n).map (rawUpdate rows n)

/-- Exact finite transcript equivalence. There is one physical query per
round, with all rows of that query fixed before any component is returned. -/
theorem decoded_staticLaw (seedView : Ω → W) (hv : Measurable seedView)
    (rows : (n : ℕ) → History W r n → Fin r → Vec d)
    (hr : ∀ n i, Measurable (fun h => rows n h i))
    (S : Ω → Vec d) (hS : Measurable S) (σ : ℝ) (ν₀ : Measure Ω)
    (n : ℕ) (hn : n ≤ H) :
    (ShiftedSequential.staticJointLaw (shiftedProtocol (H := H) seedView hv rows hr S hS) σ ν₀ n).map
        (decodeJoint seedView n) = rawStaticJointLaw seedView rows S σ ν₀ n := by
  induction n with
  | zero =>
      rw [ShiftedSequential.staticJointLaw, rawStaticJointLaw]
      change ((ν₀.prod (standardGaussian d)).map (fun p => (p.1, S p.1 + σ • p.2))).map
        (decodeJoint seedView 0) = _
      have hi : Measurable (fun p : Ω × Vec d => (p.1, S p.1 + σ • p.2)) :=
        measurable_fst.prodMk ((hS.comp measurable_fst).add (measurable_const.smul measurable_snd))
      rw [Measure.map_map (decodeJoint_measurable seedView hv 0) hi]
      rfl
  | succ n ih =>
      rw [ShiftedSequential.staticJointLaw]
      change ((ShiftedSequential.staticJointLaw (shiftedProtocol (H := H) seedView hv rows hr S hS) σ ν₀ n).map
        (staticUpdate (accumulatedProtocol seedView hv rows hr) n)).map (decodeJoint seedView (n + 1)) = _
      rw [Measure.map_map (decodeJoint_measurable seedView hv (n + 1))
          (measurable_staticUpdate (accumulatedProtocol seedView hv rows hr) n),
        rawStaticJointLaw, ← ih (Nat.le_of_succ_le hn),
        Measure.map_map (rawUpdate_measurable rows hr n) (decodeJoint_measurable seedView hv n)]
      congr 1
      funext p
      exact decode_staticUpdate seedView hv rows hr n (Nat.lt_of_succ_le hn) p

end MatchingBounds1005.PhysicalRowTranscript
