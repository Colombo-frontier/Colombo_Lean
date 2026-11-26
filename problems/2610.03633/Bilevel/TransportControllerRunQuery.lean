import Bilevel.TransportControllerQueryTheorem
import Bilevel.TransportControllerHistory

/-! The query failure bound now refers to the already-defined executed
round trajectory, rather than to an unrelated abstract protocol. Private
randomness is the initial memory and is independent of the hard instance. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace Bilevel.TransportRound
open EuclideanGaussian TransportNetwork
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000

def familyPolicy {H : Type*} [MeasurableSpace H] {n D p c m T : ℕ}
    (choose : ∀ t, H × Generators n D (size n p c m t) → Queries n D p)
    (hc : ∀ t, Measurable (choose t))
    (respond : ∀ t, StepData H n D (size n p c m t) p T → H)
    (hr : ∀ t, Measurable (respond t))
    (names : ℕ → Vertex n → Fin c → Option (Fin T)) :
    (h t : ℕ) → Policy H n D p c T (size n p c m t) h
  | 0,_ => .halt
  | h+1,t => .step (choose t) (hc t) (respond t) (hr t) (names t)
      (familyPolicy choose hc respond hr names h (t+1))

def runQueryBad {H : Type*} {n D p c m T : ℕ} (hT : T≤D) (a : ℝ)
    (choose : ∀ t, H × Generators n D (size n p c m t) → Queries n D p)
    (respond : ∀ t, StepData H n D (size n p c m t) p T → H)
    (names : ℕ → Vertex n → Fin c → Option (Fin T))
    (s : H × Generators n D m) (z : Latent n D) (h : ℕ) : Prop :=
  ∃ t<h, TransportRoundQuery.queryPhaseBad T hT a
    (requests (choose t (run T hT choose respond names s z t)))
    (known (run T hT choose respond names s z t).2) z

theorem familyPolicy_bad {H : Type*} [MeasurableSpace H] {n D p c m T : ℕ}
    (hT : T≤D) (a : ℝ)
    (choose : ∀ t, H × Generators n D (size n p c m t) → Queries n D p)
    (hc : ∀ t, Measurable (choose t))
    (respond : ∀ t, StepData H n D (size n p c m t) p T → H)
    (hr : ∀ t, Measurable (respond t))
    (names : ℕ → Vertex n → Fin c → Option (Fin T))
    (s : H × Generators n D m) (z : Latent n D) (h t : ℕ) :
    policyBad hT a (familyPolicy choose hc respond hr names h t)
        (run T hT choose respond names s z t) z ↔
      ∃ i, t ≤ i ∧ i < t + h ∧ TransportRoundQuery.queryPhaseBad T hT a
        (requests (choose i (run T hT choose respond names s z i)))
        (known (run T hT choose respond names s z i).2) z := by
  induction h generalizing t with
  | zero =>
    simp only [familyPolicy,policyBad,Nat.add_zero]
    exact ⟨False.elim,fun ⟨_,hi,hlt,_⟩ => (Nat.not_lt_of_ge hi) hlt⟩
  | succ h ih =>
    change (_ ∨ policyBad hT a (familyPolicy choose hc respond hr names h (t+1))
      (run T hT choose respond names s z (t+1)) z) ↔ _
    rw [ih]
    constructor
    · rintro (ht | ⟨i,hi,hih,hbad⟩)
      · exact ⟨t,le_rfl,by omega,ht⟩
      · exact ⟨i,by omega,by omega,hbad⟩
    · rintro ⟨i,hi,hih,hbad⟩
      by_cases he : i=t
      · subst i; exact Or.inl hbad
      · exact Or.inr ⟨i,by omega,by omega,hbad⟩

theorem familyPolicy_bad_zero {H : Type*} [MeasurableSpace H] {n D p c m T : ℕ}
    (hT : T≤D) (a : ℝ)
    (choose : ∀ t, H × Generators n D (size n p c m t) → Queries n D p)
    (hc : ∀ t, Measurable (choose t))
    (respond : ∀ t, StepData H n D (size n p c m t) p T → H)
    (hr : ∀ t, Measurable (respond t))
    (names : ℕ → Vertex n → Fin c → Option (Fin T))
    (s : H × Generators n D m) (z : Latent n D) (h : ℕ) :
    policyBad hT a (familyPolicy choose hc respond hr names h 0) s z ↔
      runQueryBad hT a choose respond names s z h := by
  simpa only [run,runQueryBad,Nat.zero_le,true_and,Nat.zero_add] using
    familyPolicy_bad hT a choose hc respond hr names s z h 0

theorem run_query_failure {H : Type*} [MeasurableSpace H] {n D p c T : ℕ}
    (hT : T≤D) (hpos : 0<T) (a : ℝ) (ha : 0<a) (r : ℕ) (hrank : 0<r)
    (choose : ∀ t, H × Generators n D (size n p c 1 t) → Queries n D p)
    (hc : ∀ t, Measurable (choose t))
    (respond : ∀ t, StepData H n D (size n p c 1 t) p T → H)
    (hr : ∀ t, Measurable (respond t))
    (names : ℕ → Vertex n → Fin c → Option (Fin T))
    (ρ : Measure H) [IsProbabilityMeasure ρ] (h : ℕ) (hD : queryCap n p c 1 h+r≤D) :
    (ρ.prod (TransportNetwork.law n D))
      {z | runQueryBad hT a choose respond names (z.1,seed T hT z.2) z.2 h} ≤
      (h:ℝ≥0∞)*((n+1)*p:ℕ)*ENNReal.ofReal ((T:ℝ)/((r:ℝ)*a)) := by
  have hh := randomized_policy_query_failure hT hpos a ha r hrank
    (familyPolicy choose hc respond hr names h 0) ρ hD
  simpa only [familyPolicy_bad_zero] using hh

theorem queryCap_bound (n p c m h : ℕ) :
    queryCap n p c m h ≤ (m+p+c)*(2*n+2)^h+(n+1)*p := by
  have hbound : ∀ h m, queryCap n p c m h ≤ (m+p+c)*(2*n+2)^h+(n+1)*p := by
    intro h
    induction h with
    | zero => intro m; simp only [queryCap,pow_zero,Nat.mul_one]; omega
    | succ h ih =>
      intro m
      apply max_le
      · have hone : 1≤(2*n+2)^(h+1) := Nat.one_le_pow _ _ (by omega)
        have hm := Nat.mul_le_mul_left (m+p+c) hone
        simp only [Nat.mul_one] at hm
        omega
      · have hh := ih (nextSize n p c m)
        have hn : nextSize n p c m+p+c≤(m+p+c)*(2*n+2) := by
          dsimp [nextSize]; nlinarith
        apply hh.trans
        have hp := Nat.mul_le_mul_right ((2*n+2)^h) hn
        rw [pow_succ]
        nlinarith
  exact hbound h m

end Bilevel.TransportRound
