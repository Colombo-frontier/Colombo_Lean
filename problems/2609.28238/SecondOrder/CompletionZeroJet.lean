import SecondOrder.ScalarJetEquality
import SecondOrder.PeriodicCompletion

namespace SecondOrder
noncomputable section

theorem gate_eq_zero_iff (t : ℝ) : gate t=0 ↔ t≤0 := by
  constructor
  · intro ht
    by_contra hn
    have hp : 0<t := lt_of_not_ge hn
    by_cases h1 : t≤1
    · have hh := gate_strictMonoOn (by constructor <;> norm_num : (0:ℝ) ∈ Set.Icc 0 1)
        ⟨hp.le,h1⟩ hp
      rw [(gate_flat_left (le_refl 0)).1, ht] at hh
      exact (lt_irrefl (0:ℝ)) hh
    · have hh := (gate_flat_right (le_of_not_ge h1)).1
      rw [ht] at hh
      norm_num at hh
  · exact fun ht => (gate_flat_left ht).1

theorem periodicCompletion_eq_zero_iff {m : ℕ} (θ : BalancedVector m) (x : Point (2*m)) :
    periodicCompletion θ x=0 ↔ ‖periodicMean x θ‖≤1/8 := by
  constructor
  · intro hb
    change gate ((64/3)*(periodicEnergy θ x-1/128))=0 at hb
    have hh := (gate_eq_zero_iff _).1 hb
    rw [periodicEnergy_eq] at hh
    nlinarith [norm_nonneg (periodicMean x θ)]
  · exact fun hx => (periodicCompletion_flat θ x hx).1

/-- A zero completion gate has a zero full two-jet, including the Hessian. -/
theorem periodicCompletion_zeroJet {m : ℕ} (θ : BalancedVector m) (x : Point (2*m))
    (hx : periodicCompletion θ x=0) : ScalarJetEq (periodicCompletion θ) (fun _ => 0) x := by
  obtain ⟨hv,hg,hH⟩ := periodicCompletion_flat θ x ((periodicCompletion_eq_zero_iff θ x).1 hx)
  exact scalarJetEq_zero_of_flat
    ((periodicCompletion_contDiff θ).of_le (show (2:WithTop ℕ∞) ≤ 3 by decide)) x hv hg hH

end
end SecondOrder
