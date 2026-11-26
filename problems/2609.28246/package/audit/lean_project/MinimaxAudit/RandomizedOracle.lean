import MinimaxAudit.JetParameter
import MinimaxAudit.Haar
import MinimaxAudit.MeasurableExecution

/-! Concrete Haar parametrization, exact scalar-jet hiding, and randomized
source-policy execution. The full scalar parameter smoothness is proved in
JetParameter; no operator oracle is substituted for the scalar p-jet. -/
open Set MeasureTheory
open scoped ContDiff RealInnerProductSpace ENNReal
namespace MinimaxAudit.Randomized
set_option maxHeartbeats 1600000
noncomputable section
open Deterministic

section HaarOracle
open VIReference.Pilot
variable {N d : ℕ}

/-- The independent primal and dual Stiefel frames are sampled before the run. -/
def haarParameters (hnd : N + 1 ≤ d) :
    Haar.FrameSample d × Haar.FrameSample d → FrameParameters N d d :=
  fun Q => (haarStiefelFrame hnd Q.1, haarStiefelFrame hnd Q.2)

theorem haarParameters_measurable (hnd : N + 1 ≤ d) : Measurable (haarParameters hnd) :=
  ((measurable_haarStiefelFrame hnd).comp measurable_fst).prodMk
    ((measurable_haarStiefelFrame hnd).comp measurable_snd)

def haarTruncatedOracle (hnd : N + 1 ≤ d)
    (profile : GateProfile) (tau lam c q : ℝ) (p t : ℕ)
    (Q : Haar.FrameSample d × Haar.FrameSample d) (z : SaddleSpace d d) :
    ScalarJet p (SaddleSpace d d) :=
  exactScalarJet p (truncatedPotential profile tau lam c q t
    (haarParameters hnd Q).1 (haarParameters hnd Q).2) z

/-- The concrete Haar-parametrized full scalar oracle is jointly measurable. -/
theorem haarTruncatedOracle_jointlyMeasurable
    (hnd : N + 1 ≤ d) (profile : GateProfile) {tau : ℝ} (htau : tau ≠ 0)
    (lam c q : ℝ) (p t : ℕ) :
    Measurable (fun z : (Haar.FrameSample d × Haar.FrameSample d) × SaddleSpace d d =>
      haarTruncatedOracle hnd profile tau lam c q p t z.1 z.2) := by
  let f : FrameParameters N d d × SaddleSpace d d → ScalarJet p (SaddleSpace d d) :=
    fun z => exactScalarJet p (truncatedPotential profile tau lam c q t z.1.1 z.1.2) z.2
  let g : (Haar.FrameSample d × Haar.FrameSample d) × SaddleSpace d d →
      FrameParameters N d d × SaddleSpace d d :=
    fun z => (haarParameters hnd z.1, z.2)
  have hf : Measurable f := truncatedScalarJet_jointlyMeasurable
    (N := N) (dx := d) (dy := d) profile htau lam c q t p
  have hp : Measurable (fun z : (Haar.FrameSample d × Haar.FrameSample d) × SaddleSpace d d =>
      haarParameters hnd z.1) := (haarParameters_measurable hnd).comp
        (measurable_fst : Measurable (Prod.fst :
          (Haar.FrameSample d × Haar.FrameSample d) × SaddleSpace d d →
            Haar.FrameSample d × Haar.FrameSample d))
  have hg : Measurable g := hp.prodMk
    (measurable_snd : Measurable (Prod.snd :
      (Haar.FrameSample d × Haar.FrameSample d) × SaddleSpace d d → SaddleSpace d d))
  change Measurable (f ∘ g)
  exact hf.comp hg

/-- A round-t truncated full-jet response depends only on the first t+1
primal/dual frame pairs, for every possible query point. -/
theorem haarTruncatedOracle_prefix
    (hnd : N + 1 ≤ d) (profile : GateProfile) (tau lam c q : ℝ)
    (p t : ℕ) (ht : t ≤ N) (z : SaddleSpace d d) :
    Haar.PairPrefixDependent hnd hnd (t + 1)
      (fun Q => haarTruncatedOracle hnd profile tau lam c q p t Q z) := by
  intro Q Q' hU hV
  have hp := truncatedPotential_congr_prefix profile tau lam c q t ht
    (haarStiefelFrame hnd Q.1) (haarStiefelFrame hnd Q'.1)
    (haarStiefelFrame hnd Q.2) (haarStiefelFrame hnd Q'.2)
    (fun i => hU _ i.2) (fun i => hV _ i.2)
  simp only [haarTruncatedOracle, haarParameters]
  rw [hp]

end HaarOracle

theorem paired_scalar_slabs {tau a b : ℝ} (_htau : 0 < tau)
    (ha : |a| ≤ tau / (8 * Real.sqrt 2)) (hb : |b| ≤ tau / (8 * Real.sqrt 2)) :
    |(a + b) / Real.sqrt 2| ≤ tau / 8 ∧ |(a - b) / Real.sqrt 2| ≤ tau / 8 := by
  have hs : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hden : 8 * Real.sqrt 2 * Real.sqrt 2 = (16 : ℝ) := by
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hscale : (tau / (8 * Real.sqrt 2) + tau / (8 * Real.sqrt 2)) / Real.sqrt 2 = tau / 8 := by
    rw [← add_div, div_div, hden]
    ring
  constructor
  · rw [abs_div, abs_of_pos hs]
    calc
      _ ≤ (|a| + |b|) / Real.sqrt 2 := div_le_div_of_nonneg_right (abs_add_le a b) hs.le
      _ ≤ (tau / (8 * Real.sqrt 2) + tau / (8 * Real.sqrt 2)) / Real.sqrt 2 :=
        div_le_div_of_nonneg_right (add_le_add ha hb) hs.le
      _ = _ := hscale
  · rw [abs_div, abs_of_pos hs]
    calc
      _ ≤ (|a| + |b|) / Real.sqrt 2 := div_le_div_of_nonneg_right (by simpa [sub_eq_add_neg] using (abs_add_le a (-b))) hs.le
      _ ≤ (tau / (8 * Real.sqrt 2) + tau / (8 * Real.sqrt 2)) / Real.sqrt 2 :=
        div_le_div_of_nonneg_right (add_le_add ha hb) hs.le
      _ = _ := hscale
section StrictFlatness
variable {N dx dy : ℕ}

/-- Raw primal/dual projection slabs give strict interior bounds on both
actual paired scalar coordinates. -/
theorem paired_forms_slabs {tau : ℝ} (htau : 0 < tau)
    (U : Fin (N + 1) → Primal dx) (V : Fin (N + 1) → Dual dy)
    (i : Fin (N + 1)) (z : SaddleSpace dx dy)
    (hx : |inner ℝ (U i) (primalBlock z)| ≤ tau / (8 * Real.sqrt 2))
    (hy : |inner ℝ (V i) (dualBlock z)| ≤ tau / (8 * Real.sqrt 2)) :
    |plusForm U V i z| ≤ tau / 8 ∧ |minusForm U V i z| ≤ tau / 8 := by
  have hp : plusForm U V i z =
      (inner ℝ (U i) (primalBlock z) + inner ℝ (V i) (dualBlock z)) / Real.sqrt 2 := by
    change inner ℝ (pairedPlus U V i) z = _
    conv_lhs => rw [← join_blocks z, paired_plus_coordinate]
  have hm : minusForm U V i z =
      (inner ℝ (U i) (primalBlock z) - inner ℝ (V i) (dualBlock z)) / Real.sqrt 2 := by
    change inner ℝ (pairedMinus U V i) z = _
    conv_lhs => rw [← join_blocks z, paired_minus_coordinate]
  rw [hp, hm]
  exact paired_scalar_slabs htau hx hy

/-- Exact complete scalar-jet equality from the small raw slabs guaranteed
by Haar concentration. No zero-coordinate or jet-coupling premise is assumed. -/
theorem exactJet_full_eq_stage_of_future_slabs
    (profile : GateProfile) {tau : ℝ} (htau : 0 < tau) (lam c q : ℝ)
    (p t : ℕ) (ht : t ≤ N)
    (U : Fin (N + 1) → Primal dx) (V : Fin (N + 1) → Dual dy)
    (z : SaddleSpace dx dy)
    (hfuture : ∀ i : Fin (N + 1), t ≤ i.1 →
      |inner ℝ (U i) (primalBlock z)| ≤ tau / (8 * Real.sqrt 2) ∧
      |inner ℝ (V i) (dualBlock z)| ≤ tau / (8 * Real.sqrt 2)) :
    exactScalarJet p (hardPotential profile tau lam c q U V) z =
      exactScalarJet p (truncatedPotential profile tau lam c q t U V) z := by
  apply chainPotential_exact_jet_eq_truncated profile htau lam c q publicQuadratic
    (plusForm U V) (minusForm U V) (revealedLinks N t)
  · intro i hi
    have hit : t ≤ i.1 := by simpa [revealedLinks] using hi
    have ha := (paired_forms_slabs htau U V i.castSucc z
      (hfuture i.castSucc hit).1 (hfuture i.castSucc hit).2).1
    have hb := (paired_forms_slabs htau U V i.succ z
      (hfuture i.succ (by simpa only [Fin.val_succ] using Nat.le_succ_of_le hit)).1
      (hfuture i.succ (by simpa only [Fin.val_succ] using Nat.le_succ_of_le hit)).2).2
    linarith
  · have ha := (paired_forms_slabs htau U V (Fin.last N) z
      (hfuture (Fin.last N) ht).1 (hfuture (Fin.last N) ht).2).1
    linarith

/-- The strict slab used in the cubic-log Haar dimension equals tau/(8√2)
for the manuscript's tau=eta*kappa*R/(n√n). -/
theorem strictSlabThreshold_eq_tau_ratio (n eta kappa R : ℝ) :
    Haar.strictSlabThreshold n eta kappa R =
      (eta * kappa * R / (n * Real.sqrt n)) / (8 * Real.sqrt 2) := by
  unfold Haar.strictSlabThreshold
  rw [div_div]
  congr 1
  ring

end StrictFlatness

section StageInterface
open VIReference.Pilot VIReference.Pilot.BorelStoppingPolicy
variable {N d : ℕ}

def joinedHaarFrame (hnd : N + 1 ≤ d) (Q : Haar.FrameSample d × Haar.FrameSample d)
    (i : Fin (N + 1)) : SaddleSpace d d :=
  joinBlocks (haarStiefelFrame hnd Q.1 i) (haarStiefelFrame hnd Q.2 i)

def scalarHaarStage (hnd : N + 1 ≤ d) (profile : GateProfile) (tau lam c q : ℝ) (p : ℕ)
    (Q : Haar.FrameSample d × Haar.FrameSample d) (t : Fin N) (z : SaddleSpace d d) :
    ScalarJet p (SaddleSpace d d) :=
  haarTruncatedOracle hnd profile tau lam c q p t.1 Q z

def scalarHaarActual (hnd : N + 1 ≤ d) (profile : GateProfile) (tau lam c q : ℝ) (p : ℕ)
    (Q : Haar.FrameSample d × Haar.FrameSample d) (z : SaddleSpace d d) :
    ScalarJet p (SaddleSpace d d) :=
  exactScalarJet p (hardPotential profile tau lam c q
    (haarParameters hnd Q).1 (haarParameters hnd Q).2) z

theorem scalarHaarStage_jointlyMeasurable
    (hnd : N + 1 ≤ d) (profile : GateProfile) {tau : ℝ} (htau : tau ≠ 0)
    (lam c q : ℝ) (p : ℕ) (t : Fin N) :
    Measurable (fun z : (Haar.FrameSample d × Haar.FrameSample d) × SaddleSpace d d =>
      scalarHaarStage hnd profile tau lam c q p z.1 t z.2) :=
  haarTruncatedOracle_jointlyMeasurable hnd profile htau lam c q p t.1

theorem scalarHaarStage_prefix
    (hnd : N + 1 ≤ d) (profile : GateProfile) (tau lam c q : ℝ) (p : ℕ) :
    StageOracleDependsOnFramePrefix (joinedHaarFrame hnd)
      (scalarHaarStage hnd profile tau lam c q p) := by
  intro t Q Q' hprefix z
  apply haarTruncatedOracle_prefix hnd profile tau lam c q p t.1 (Nat.le_of_lt t.2) z Q Q'
  · intro i hi
    have hh := congrArg primalBlock (hprefix i hi)
    simpa [joinedHaarFrame] using hh
  · intro i hi
    have hh := congrArg dualBlock (hprefix i hi)
    simpa [joinedHaarFrame] using hh

/-- Exact source-coordinate transcript coupling on raw future-column slabs. -/
theorem scalarHaarStage_eq_actual_of_slabs
    (hnd : N + 1 ≤ d) (profile : GateProfile) {tau : ℝ} (htau : 0 < tau)
    (lam c q : ℝ) (p : ℕ) (t : Fin N)
    (Q : Haar.FrameSample d × Haar.FrameSample d) (z : SaddleSpace d d)
    (hslabs : ∀ i : Fin (N + 1), t.1 ≤ i.1 →
      |inner ℝ (haarStiefelFrame hnd Q.1 i) (primalBlock z)| ≤ tau / (8 * Real.sqrt 2) ∧
      |inner ℝ (haarStiefelFrame hnd Q.2 i) (dualBlock z)| ≤ tau / (8 * Real.sqrt 2)) :
    scalarHaarStage hnd profile tau lam c q p Q t z =
      scalarHaarActual hnd profile tau lam c q p Q z := by
  exact (exactJet_full_eq_stage_of_future_slabs profile htau lam c q p t.1
    (Nat.le_of_lt t.2) _ _ z hslabs).symm

end StageInterface

end
end MinimaxAudit.Randomized
