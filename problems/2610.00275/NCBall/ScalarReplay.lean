import NCBall.MainUpper

/-! # Reconstructing the upper algorithm from scalar replies alone

The replay state has no objective, sample function, sample identity, or
gradient as an input. It uses only internal randomness and previously received
pairs of scalar replies. The equations below identify this computation with
the process in the main upper theorem, including its final output.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators unitInterval
namespace NCBall

abbrev ChordGeometrySeed (n : ℕ) := CoordSpace (n + 1) × Fin (n + 1)

def chordFromValues {n : ℕ} (ρ : ℝ) (z : ChordGeometrySeed n) (v : ℝ × ℝ) : CoordSpace (n + 1) :=
  ((n + 1 : ℝ) / (2 * chordHalfLength ρ (chordSide z.2 z.1)) * (v.1 - v.2)) •
    EuclideanSpace.single z.2 1

def scalarReplayState {n : ℕ} (ρ D : ℝ) (hD : 0 ≤ D) (α : ℝ)
    (x₀ : CoordSpace (n + 1)) (r : ℕ → I) (z : ℕ → ChordGeometrySeed n)
    (v : ℕ → ℝ × ℝ) : ℕ → CoordSpace (n + 1) × CoordSpace (n + 1)
  | 0 => (x₀, 0)
  | t + 1 =>
    let s := scalarReplayState ρ D hD α x₀ r z v t
    (s.1 + s.2, ballProjection D hD (s.2 - α • chordFromValues ρ (z t) (v t)))

def scalarReplayLocation {n : ℕ} (ρ D : ℝ) (hD : 0 ≤ D) (α : ℝ)
    (x₀ : CoordSpace (n + 1)) (r : ℕ → I) (z : ℕ → ChordGeometrySeed n)
    (v : ℕ → ℝ × ℝ) (t : ℕ) : CoordSpace (n + 1) :=
  let s := scalarReplayState ρ D hD α x₀ r z v t
  s.1 + (r t : ℝ) • s.2

def scalarReplayOutput {n : ℕ} (ρ D : ℝ) (hD : 0 ≤ D) (α : ℝ)
    (x₀ : CoordSpace (n + 1)) (r : ℕ → I) (z : ℕ → ChordGeometrySeed n)
    (v : ℕ → ℝ × ℝ) (s m : ℕ) : CoordSpace (n + 1) :=
  (m : ℝ)⁻¹ • ∑ j ∈ Finset.range m, scalarReplayLocation ρ D hD α x₀ r z v (s + j)

theorem chordFromValues_measurable {n : ℕ} (ρ : ℝ) :
    Measurable (fun p : ChordGeometrySeed n × (ℝ × ℝ) => chordFromValues ρ p.1 p.2) := by
  have hm : Measurable (fun p : (CoordSpace (n + 1) × (ℝ × ℝ)) × Fin (n + 1) =>
      chordFromValues ρ (p.1.1, p.2) p.1.2) := by
    apply measurable_from_prod_countable
    intro i
    have hh : Measurable (fun p : CoordSpace (n + 1) × (ℝ × ℝ) =>
        chordHalfLength ρ (chordSide i p.1)) := (chordHalfLength_continuous ρ).measurable.comp
      ((chordSide_measurable i).comp measurable_fst)
    exact ((measurable_const.div (measurable_const.mul hh)).mul
      (measurable_snd.fst.sub measurable_snd.snd)).smul_const (EuclideanSpace.single i (1 : ℝ))
  have ht : Measurable (fun p : ChordGeometrySeed n × (ℝ × ℝ) => ((p.1.1, p.2), p.1.2)) :=
    (measurable_fst.fst.prodMk measurable_snd).prodMk measurable_fst.snd
  have hfinal := hm.comp ht
  simpa only [Function.comp_def, Prod.mk.eta] using hfinal

theorem scalarReplayState_measurable {n : ℕ} (ρ D : ℝ) (hD : 0 ≤ D) (α : ℝ)
    (x₀ : CoordSpace (n + 1)) (t : ℕ) :
    Measurable (fun w : (ℕ → I) × ((ℕ → ChordGeometrySeed n) × (ℕ → ℝ × ℝ)) =>
      scalarReplayState ρ D hD α x₀ w.1 w.2.1 w.2.2 t) := by
  induction t with
  | zero => exact measurable_const
  | succ t ih =>
    have hz : Measurable (fun w : (ℕ → I) × ((ℕ → ChordGeometrySeed n) × (ℕ → ℝ × ℝ)) => w.2.1 t) :=
      (measurable_pi_apply t).comp measurable_snd.fst
    have hv : Measurable (fun w : (ℕ → I) × ((ℕ → ChordGeometrySeed n) × (ℕ → ℝ × ℝ)) => w.2.2 t) :=
      (measurable_pi_apply t).comp measurable_snd.snd
    exact (ih.fst.add ih.snd).prodMk ((ballProjection_measurable D hD).comp
      (ih.snd.sub (((chordFromValues_measurable ρ).comp (hz.prodMk hv)).const_smul α)))

theorem scalarReplayLocation_measurable {n : ℕ} (ρ D : ℝ) (hD : 0 ≤ D) (α : ℝ)
    (x₀ : CoordSpace (n + 1)) (t : ℕ) :
    Measurable (fun w : (ℕ → I) × ((ℕ → ChordGeometrySeed n) × (ℕ → ℝ × ℝ)) =>
      scalarReplayLocation ρ D hD α x₀ w.1 w.2.1 w.2.2 t) := by
  have hs := scalarReplayState_measurable ρ D hD α x₀ t
  exact hs.fst.add ((measurable_subtype_coe.comp ((measurable_pi_apply t).comp measurable_fst)).smul hs.snd)

theorem scalarReplayOutput_measurable {n : ℕ} (ρ D : ℝ) (hD : 0 ≤ D) (α : ℝ)
    (x₀ : CoordSpace (n + 1)) (s m : ℕ) :
    Measurable (fun w : (ℕ → I) × ((ℕ → ChordGeometrySeed n) × (ℕ → ℝ × ℝ)) =>
      scalarReplayOutput ρ D hD α x₀ w.1 w.2.1 w.2.2 s m) := by
  exact (Finset.measurable_sum _ (fun j _ => scalarReplayLocation_measurable ρ D hD α x₀ (s + j))).const_smul (m : ℝ)⁻¹

theorem scalarReplayState_prefix {n : ℕ} (ρ D : ℝ) (hD : 0 ≤ D) (α : ℝ)
    (x₀ : CoordSpace (n + 1)) (r : ℕ → I) (z : ℕ → ChordGeometrySeed n)
    (v v' : ℕ → ℝ × ℝ) (t : ℕ) (hv : ∀ j < t, v j = v' j) :
    scalarReplayState ρ D hD α x₀ r z v t = scalarReplayState ρ D hD α x₀ r z v' t := by
  induction t with
  | zero => rfl
  | succ t ih => simp only [scalarReplayState, ih (fun j hj => hv j (by omega)), hv t (by omega)]

theorem scalarReplayLocation_prefix {n : ℕ} (ρ D : ℝ) (hD : 0 ≤ D) (α : ℝ)
    (x₀ : CoordSpace (n + 1)) (r : ℕ → I) (z : ℕ → ChordGeometrySeed n)
    (v v' : ℕ → ℝ × ℝ) (t : ℕ) (hv : ∀ j < t, v j = v' j) :
    scalarReplayLocation ρ D hD α x₀ r z v t = scalarReplayLocation ρ D hD α x₀ r z v' t := by
  unfold scalarReplayLocation
  rw [scalarReplayState_prefix ρ D hD α x₀ r z v v' t hv]

theorem scalarReplayOutput_prefix {n : ℕ} (ρ D : ℝ) (hD : 0 ≤ D) (α : ℝ)
    (x₀ : CoordSpace (n + 1)) (r : ℕ → I) (z : ℕ → ChordGeometrySeed n)
    (v v' : ℕ → ℝ × ℝ) (s m : ℕ) (hv : ∀ j < s + m, v j = v' j) :
    scalarReplayOutput ρ D hD α x₀ r z v s m = scalarReplayOutput ρ D hD α x₀ r z v' s m := by
  unfold scalarReplayOutput
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  exact scalarReplayLocation_prefix ρ D hD α x₀ r z v v' (s + j)
    (fun k hk => hv k (by have := Finset.mem_range.mp hj; omega))

def actualScalarPairs {n : ℕ} {Ξ : Type*} (ρ D : ℝ) (hD : 0 ≤ D) (α : ℝ)
    (F : Ξ → CoordSpace (n + 1) → ℝ) (x₀ : CoordSpace (n + 1))
    (w : UpperRandomness (StochasticChordSeed n Ξ)) (t : ℕ) : ℝ × ℝ :=
  (F (w.2 t).1 (zerothPlusQuery ρ D hD α F x₀ w t),
    F (w.2 t).1 (zerothMinusQuery ρ D hD α F x₀ w t))

theorem scalarReplayState_eq_upper {n : ℕ} {Ξ : Type*} (ρ D : ℝ) (hD : 0 ≤ D) (α : ℝ)
    (F : Ξ → CoordSpace (n + 1) → ℝ) (x₀ : CoordSpace (n + 1))
    (w : UpperRandomness (StochasticChordSeed n Ξ)) (t : ℕ) :
    scalarReplayState ρ D hD α x₀ w.1 (fun j => (w.2 j).2)
      (actualScalarPairs ρ D hD α F x₀ w) t =
      upperState D hD α (stochasticChord F ρ) x₀ w.1 w.2 t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have he : chordFromValues ρ (w.2 t).2 (actualScalarPairs ρ D hD α F x₀ w t) =
        upperEstimate D hD α (stochasticChord F ρ) x₀ w.1 w.2 t :=
      (upperEstimate_two_scalar_values ρ D hD α F x₀ w t).symm
    simp only [scalarReplayState, ih, he]
    rfl

theorem scalarReplayLocation_eq_upper {n : ℕ} {Ξ : Type*} (ρ D : ℝ) (hD : 0 ≤ D) (α : ℝ)
    (F : Ξ → CoordSpace (n + 1) → ℝ) (x₀ : CoordSpace (n + 1))
    (w : UpperRandomness (StochasticChordSeed n Ξ)) (t : ℕ) :
    scalarReplayLocation ρ D hD α x₀ w.1 (fun j => (w.2 j).2)
      (actualScalarPairs ρ D hD α F x₀ w) t =
      upperLocation D hD α (stochasticChord F ρ) x₀ w.1 w.2 t := by
  simp only [scalarReplayLocation, scalarReplayState_eq_upper, upperLocation]

theorem scalarReplay_queries_eq {n : ℕ} {Ξ : Type*} (ρ D : ℝ) (hD : 0 ≤ D) (α : ℝ)
    (F : Ξ → CoordSpace (n + 1) → ℝ) (x₀ : CoordSpace (n + 1))
    (w : UpperRandomness (StochasticChordSeed n Ξ)) (t : ℕ) :
    let x := scalarReplayLocation ρ D hD α x₀ w.1 (fun j => (w.2 j).2)
      (actualScalarPairs ρ D hD α F x₀ w) t
    chordQueryPlus ρ x (w.2 t).2 = zerothPlusQuery ρ D hD α F x₀ w t ∧
      chordQueryMinus ρ x (w.2 t).2 = zerothMinusQuery ρ D hD α F x₀ w t := by
  simp only [scalarReplayLocation_eq_upper, zerothPlusQuery, zerothMinusQuery, and_self]

theorem scalarReplayOutput_eq_upper {n : ℕ} {Ξ : Type*} (ρ D : ℝ) (hD : 0 ≤ D) (α : ℝ)
    (F : Ξ → CoordSpace (n + 1) → ℝ) (x₀ : CoordSpace (n + 1))
    (w : UpperRandomness (StochasticChordSeed n Ξ)) (s m : ℕ) :
    scalarReplayOutput ρ D hD α x₀ w.1 (fun j => (w.2 j).2)
      (actualScalarPairs ρ D hD α F x₀ w) s m =
      upperOutput D hD α (stochasticChord F ρ) x₀ w.1 w.2 s m := by
  simp only [scalarReplayOutput, scalarReplayLocation_eq_upper, upperOutput]

end NCBall
