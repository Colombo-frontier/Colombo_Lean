import Bilevel.GenieEnergy

/-! Unused query budget does not alter a protocol's actual execution. -/
noncomputable section
namespace Bilevel.GenieProtocol
open EuclideanGaussian ProjectionPosterior

def addQuery {d T m r : ℕ} (P : Protocol d T m r) : Protocol d T (m+1) r := by
  induction P with
  | halt => exact .halt
  | @query m r w next ih => exact .query w (fun y => ih y)
  | @reveal m r i next ih => exact .reveal i (fun y => ih y)

theorem bad_addQuery {d T m r : ℕ} (P : Protocol d T m r) (b : ℝ)
    (U : Frame d T) : bad b (addQuery P) U ↔ bad b P U := by
  induction P with
  | halt => rfl
  | @query m r w next ih => change (_ ∨ _) ↔ (_ ∨ _); exact or_congr Iff.rfl (ih _)
  | @reveal m r i next ih => exact ih (U i)

theorem valid_addQuery {d T m r : ℕ} (P : Protocol d T m r)
    (V : Submodule ℝ (Space d)) : Valid (addQuery P) V ↔ Valid P V := by
  induction P generalizing V with
  | halt => rfl
  | @query m r w next ih =>
    change (_ ∧ _ ∧ ∀ y, Valid (addQuery (next y)) _) ↔ (_ ∧ _ ∧ ∀ y, Valid (next y) _)
    simp only [ih]
  | @reveal m r i next ih => exact forall_congr' (fun y => ih y _)

theorem safe_addQuery {d T m r : ℕ} (P : Protocol d T m r) (cap : ℝ)
    (V : Submodule ℝ (Space d)) (S : Set (Fin T)) (U : Frame d T) :
    Safe cap (addQuery P) V S U ↔ Safe cap P V S U := by
  induction P generalizing V S with
  | halt => rfl
  | @query m r w next ih => exact and_congr Iff.rfl (ih _ _ _)
  | @reveal m r i next ih => exact and_congr Iff.rfl (ih _ _ _)

theorem regular_addQuery {d T m r : ℕ} (P : Protocol d T m r) (b : ℝ) :
    Regular b (addQuery P) ↔ Regular b P := by
  induction P with
  | halt => rfl
  | @query m r w next ih =>
    change (MeasurableSet {p : (Fin T → ℝ) × Frame d T | bad b (addQuery (next p.1)) p.2} ∧ ∀ y, Regular b (addQuery (next y))) ↔ _
    simp only [bad_addQuery,ih]
    rfl
  | @reveal m r i next ih =>
    change (MeasurableSet {p : Space d × Frame d T | bad b (addQuery (next p.1)) p.2} ∧ ∀ y, Regular b (addQuery (next y))) ↔ _
    simp only [bad_addQuery,ih]
    rfl

end Bilevel.GenieProtocol
