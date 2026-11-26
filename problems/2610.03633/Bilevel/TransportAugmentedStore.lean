import Bilevel.TransportRoundController

/-! A fixed Borel type for the changing finite network generator ledger.
At round t it is the zero-padded image of the actual finite ledger; all
round-dependent reads are explicit restrictions, with an exact inverse. -/
noncomputable section
open MeasureTheory
namespace Bilevel.TransportAugmented
open EuclideanGaussian TransportNetwork TransportRound
set_option autoImplicit false

abbrev FlatGenerators (n D : ℕ) := Vertex n → ℕ → Space D

def flatten {n D m : ℕ} (g : Generators n D m) : FlatGenerators n D :=
  fun v j => if h : j<m then g v ⟨j,h⟩ else 0

def restrict {n D : ℕ} (m : ℕ) (g : FlatGenerators n D) : Generators n D m :=
  fun v j => g v j.val

theorem restrict_flatten {n D m : ℕ} (g : Generators n D m) : restrict m (flatten g)=g := by
  funext v j
  simp only [restrict,flatten,dif_pos j.isLt]

theorem flatten_tail {n D m : ℕ} (g : Generators n D m) (v : Vertex n) (j : ℕ) (hj : m ≤ j) :
    flatten g v j=0 := dif_neg (by omega)

theorem flatten_measurable (n D m : ℕ) : Measurable (flatten (n:=n) (D:=D) (m:=m)) := by
  apply measurable_pi_lambda
  intro v
  apply measurable_pi_lambda
  intro j
  by_cases hj : j<m
  · simpa only [flatten,dif_pos hj] using
      (measurable_pi_apply (⟨j,hj⟩ : Fin m)).comp (measurable_pi_apply v)
  · simpa only [flatten,dif_neg hj] using
      (measurable_const : Measurable (fun _ : Generators n D m => (0 : Space D)))

theorem restrict_measurable (n D m : ℕ) : Measurable (restrict (n:=n) (D:=D) m) := by
  apply measurable_pi_lambda
  intro v
  apply measurable_pi_lambda
  intro j
  exact (measurable_pi_apply j.val).comp (measurable_pi_apply v)

end Bilevel.TransportAugmented
