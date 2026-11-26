import Bilevel.GenieBudget
import Bilevel.ProjectionNormalization

/-! The source interface: arbitrary vectors, all full projections, and adaptive full-column revelation. -/
noncomputable section
open scoped RealInnerProductSpace
namespace Bilevel.RawGenieProtocol
open EuclideanGaussian ProjectionPosterior ProjectionGeometry ProjectionObservation
open GenieProtocol

inductive Protocol (d T : ℕ) : ℕ → ℕ → Type
  | halt {m r : ℕ} : Protocol d T m r
  | query {m r : ℕ} (q : Space d) (next : Frame d T → Protocol d T m r) : Protocol d T (m+1) r
  | reveal {m r : ℕ} (j : Fin T) (next : Space d × Frame d T → Protocol d T m r) : Protocol d T m (r+1)

def projections (d T : ℕ) (V : Submodule ℝ (Space d)) (U : Frame d T) : Frame d T :=
  fun i => project V (U i)

def normalize {d T : ℕ} : {m r : ℕ} → Protocol d T m r →
    (V : Submodule ℝ (Space d)) → Frame d T → GenieProtocol.Protocol d T m r
  | _, _, .halt, _, _ => .halt
  | _, _, .query q next, V, Z => by
      classical
      exact if hq : ProjectionGeometry.residual V q = 0 then
        addQuery (normalize (next Z) V Z)
      else
        let w := revelationDirection V q
        GenieProtocol.Protocol.query w (fun y =>
          normalize (next (queryUpdate d T Z w y)) (V ⊔ Submodule.span ℝ {w}) (queryUpdate d T Z w y))
  | _, _, .reveal j next, V, Z => .reveal j (fun y =>
      normalize (next (y,revealUpdate d T Z j y)) (V ⊔ Submodule.span ℝ {y}) (revealUpdate d T Z j y))

theorem normalized_valid {d T m r : ℕ} (P : Protocol d T m r)
    (V : Submodule ℝ (Space d)) (Z : Frame d T) : GenieProtocol.Valid (normalize P V Z) V := by
  induction P generalizing V Z with
  | halt => trivial
  | @query m r q next ih =>
    classical
    unfold normalize
    split_ifs with hq
    · exact (valid_addQuery _ _).2 (ih Z V Z)
    · exact ⟨ProjectionNormalization.direction_mem d V q,
        ProjectionNormalization.direction_norm d V q hq, fun y => ih _ _ _⟩
  | @reveal m r j next ih => exact fun y => ih _ _ _

def Safe {d T : ℕ} (cap : ℝ) : {m r : ℕ} → Protocol d T m r →
    Submodule ℝ (Space d) → Set (Fin T) → Frame d T → Prop
  | _, _, .halt, V, S, U => BoundedEnergy V S U cap
  | _, _, .query q next, V, S, U =>
      BoundedEnergy V S U cap ∧ Safe cap (next (projections d T (V ⊔ Submodule.span ℝ {q}) U))
        (V ⊔ Submodule.span ℝ {q}) S U
  | _, _, .reveal j next, V, S, U =>
      BoundedEnergy V S U cap ∧ Safe cap
        (next (U j,projections d T (V ⊔ Submodule.span ℝ {U j}) U))
        (V ⊔ Submodule.span ℝ {U j}) (insert j S) U

theorem safe_current {d T m r : ℕ} (P : Protocol d T m r) (cap : ℝ)
    (V : Submodule ℝ (Space d)) (S : Set (Fin T)) (U : Frame d T)
    (h : Safe cap P V S U) : BoundedEnergy V S U cap := by
  cases P with
  | halt => exact h
  | query _ _ => exact h.1
  | reveal _ _ => exact h.1

theorem safe_normalize_iff {d T m r : ℕ} (P : Protocol d T m r) (cap : ℝ)
    (V : Submodule ℝ (Space d)) (S : Set (Fin T)) (U : Frame d T) (hU : Orthonormal ℝ U) :
    GenieProtocol.Safe cap (normalize P V (projections d T V U)) V S U ↔ Safe cap P V S U := by
  induction P generalizing V S with
  | halt => rfl
  | @query m r q next ih =>
    classical
    unfold normalize
    split_ifs with hq
    · rw [safe_addQuery]
      have hs := ProjectionNormalization.unchanged d V q hq
      change GenieProtocol.Safe cap (normalize (next (projections d T V U)) V (projections d T V U)) V S U ↔ _
      rw [ih]
      change _ ↔ BoundedEnergy V S U cap ∧ _
      rw [hs]
      exact ⟨fun h => ⟨safe_current _ cap V S U h,h⟩, fun h => h.2⟩
    · let w := revelationDirection V q
      have hs := ProjectionNormalization.span_eq d V q hq
      have ho := query_update_correct d T V w (ProjectionNormalization.direction_mem d V q)
        (ProjectionNormalization.direction_norm d V q hq) U
      change BoundedEnergy V S U cap ∧ GenieProtocol.Safe cap
        (normalize (next (queryUpdate d T (projections d T V U) w (queryObservation d T w U)))
          (V ⊔ Submodule.span ℝ {w}) (queryUpdate d T (projections d T V U) w (queryObservation d T w U)))
        (V ⊔ Submodule.span ℝ {w}) S U ↔ _
      change queryUpdate d T (projections d T V U) w (queryObservation d T w U) =
        projections d T (V ⊔ Submodule.span ℝ {w}) U at ho
      rw [ho,ih]
      change _ ↔ BoundedEnergy V S U cap ∧ _
      rw [hs]
  | @reveal m r j next ih =>
    have ho := reveal_update_correct d T V U hU j
    change revealUpdate d T (projections d T V U) j (U j) =
      projections d T (V ⊔ Submodule.span ℝ {U j}) U at ho
    change BoundedEnergy V S U cap ∧ GenieProtocol.Safe cap
      (normalize (next (U j,revealUpdate d T (projections d T V U) j (U j)))
        (V ⊔ Submodule.span ℝ {U j}) (revealUpdate d T (projections d T V U) j (U j)))
      (V ⊔ Submodule.span ℝ {U j}) (insert j S) U ↔ _
    rw [ho,ih]
    rfl

end Bilevel.RawGenieProtocol
