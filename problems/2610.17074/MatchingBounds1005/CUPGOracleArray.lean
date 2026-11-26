import MatchingBounds1005.Model
import Mathlib.Tactic

/-! Causal finite-oracle replay. This supplies exact response consistency from
the actual closed-loop execution, rather than assuming a correct transcript. -/
noncomputable section
namespace MatchingBounds1005.CUPG

def ArrayCausal {d : ℕ} (Q : ℕ → (ℕ → Model.Response d) → Model.Space d) : Prop :=
  ∀ t a b, (∀ j < t, a j = b j) → Q t a = Q t b

def arrayRun {d : ℕ} (Q : ℕ → (ℕ → Model.Response d) → Model.Space d)
    (f : Model.Space d → ℝ) : ℕ → (ℕ → Model.Response d)
  | 0 => fun _ => 0
  | t + 1 => Function.update (arrayRun Q f t) t (Model.oracle f (Q t (arrayRun Q f t)))

theorem arrayRun_prefix {d : ℕ} (Q : ℕ → (ℕ → Model.Response d) → Model.Space d)
    (f : Model.Space d → ℝ) (s t : ℕ) (hst : s ≤ t) :
    ∀ j < s, arrayRun Q f t j = arrayRun Q f s j := by
  induction t with
  | zero => intro j hj; omega
  | succ t ih =>
    by_cases he : s = t + 1
    · subst s; exact fun _ _ => rfl
    · have hst' : s ≤ t := by omega
      intro j hj
      rw [arrayRun, Function.update_of_ne (by omega : j ≠ t)]
      exact ih hst' j hj

theorem arrayRun_response {d : ℕ} (Q : ℕ → (ℕ → Model.Response d) → Model.Space d)
    (hQ : ArrayCausal Q) (f : Model.Space d → ℝ) (t j : ℕ) (hj : j < t) :
    arrayRun Q f t j = Model.oracle f (Q j (arrayRun Q f t)) := by
  have hp := arrayRun_prefix Q f (j + 1) t (by omega) j (by omega)
  have hq : Q j (arrayRun Q f j) = Q j (arrayRun Q f t) :=
    hQ j _ _ (fun i hi => (arrayRun_prefix Q f j t (by omega) i hi).symm)
  rw [hp, arrayRun, Function.update_self, hq]

theorem arrayRun_prefix_congr {d : ℕ}
    (Q R : ℕ → (ℕ → Model.Response d) → Model.Space d)
    (f : Model.Space d → ℝ) (N : ℕ) (hQR : ∀ t < N, Q t = R t) :
    arrayRun Q f N = arrayRun R f N := by
  induction N with
  | zero => rfl
  | succ N ih =>
    have hp := ih (fun t ht => hQR t (by omega))
    rw [arrayRun, arrayRun, hp, hQR N (by omega)]

end MatchingBounds1005.CUPG
