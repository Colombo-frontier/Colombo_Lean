import Bilevel.TransportAugmentedAuxiliaryDriver

/-! Literal equality of the network controller and auxiliary observer views
of the common run. The zero padding is only a Borel representation; every
current generator and every query is unchanged. -/
noncomputable section
universe u v
namespace Bilevel.TransportAugmented
open EuclideanGaussian TransportNetwork TransportRound
set_option autoImplicit false
variable {C : Type u} {S : Type v} [MeasurableSpace C] [MeasurableSpace S]
  {n D p Tnet k T B : ℕ}

theorem auxiliary_run_succ_last (P : TransportAuxiliaryFrame.Schedule k T)
    (A : TransportAuxiliaryFrame.Driver C S k T D B) :
    ∀ N t (s : TransportAuxiliaryFrame.State C S k T D) U,
      TransportAuxiliaryFrame.run P A (N+1) t s U =
        TransportAuxiliaryFrame.step P A (t+N) (TransportAuxiliaryFrame.run P A N t s U) U := by
  intro N
  induction N with
  | zero => intros; rfl
  | succ N ih =>
    intro t s U
    rw [TransportAuxiliaryFrame.run,ih,TransportAuxiliaryFrame.run]
    have he : (t+1)+N=t+(N+1) := by omega
    rw [he]

theorem networkRun_columns (P : TransportAuxiliaryFrame.Schedule k T)
    (A : Controller C S n D p Tnet k T B) (hTnet : Tnet ≤ D)
    (names : ℕ → Vertex n → Fin 1 → Option (Fin Tnet))
    (s : NetworkMemory C S k T D × Generators n D 1) (z : Latent n D) (N : ℕ) :
    (networkRun P A hTnet names s z N).1.1=s.1.1 := by
  induction N with
  | zero => rfl
  | succ N ih => exact ih

theorem auxiliary_run_eq_network (P : TransportAuxiliaryFrame.Schedule k T)
    (A : Controller C S n D p Tnet k T B) (hTnet : Tnet ≤ D)
    (names : ℕ → Vertex n → Fin 1 → Option (Fin Tnet))
    (s : NetworkMemory C S k T D × Generators n D 1) (z : Latent n D) (N : ℕ) :
    TransportAuxiliaryFrame.run P (auxiliaryDriver A hTnet names) N 0 (encode z s) s.1.1 =
      encode z (networkRun P A hTnet names s z N) := by
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [auxiliary_run_succ_last,ih,Nat.zero_add]
    rw [←networkRun_columns P A hTnet names s z N]
    exact auxiliary_step_eq_network P A hTnet names N z (networkRun P A hTnet names s z N)

theorem auxiliary_query_eq_network (P : TransportAuxiliaryFrame.Schedule k T)
    (A : Controller C S n D p Tnet k T B) (hTnet : Tnet ≤ D)
    (names : ℕ → Vertex n → Fin 1 → Option (Fin Tnet))
    (s : NetworkMemory C S k T D × Generators n D 1) (z : Latent n D) (N : ℕ) (b : Fin B) :
    (auxiliaryDriver A hTnet names).queries N
      (TransportAuxiliaryFrame.run P (auxiliaryDriver A hTnet names) N 0 (encode z s) s.1.1) b =
      A.auxiliaryQueries N ((networkRun P A hTnet names s z N).1.2,
        (networkRun P A hTnet names s z N).2) b := by
  rw [auxiliary_run_eq_network]
  change A.auxiliaryQueries N (prepare N (encode z _)) b = _
  rw [prepare_encode]

theorem auxiliary_output_eq_network (P : TransportAuxiliaryFrame.Schedule k T)
    (A : Controller C S n D p Tnet k T B) (hTnet : Tnet ≤ D)
    (names : ℕ → Vertex n → Fin 1 → Option (Fin Tnet))
    (s : NetworkMemory C S k T D × Generators n D 1) (z : Latent n D) (N : ℕ) :
    (auxiliaryDriver A hTnet names).output
      (TransportAuxiliaryFrame.run P (auxiliaryDriver A hTnet names) N 0 (encode z s) s.1.1) =
      A.auxiliaryOutput (networkRun P A hTnet names s z N).1.2 := by
  rw [auxiliary_run_eq_network]
  rfl

end Bilevel.TransportAugmented
