import Bilevel.TransportRoundRunProbability

/-! A single conservative public ambient-dimension cap for the actual run.
Its finite generator and reconstruction counts depend on the horizon and
network, never on the ambient dimension or the algorithm's random outcomes. -/
noncomputable section
namespace Bilevel.TransportRound
open TransportControllerMachine

def generatorCap (n p M : ℕ) : ℕ := (p+2)*(2*n+2)^M

theorem frozen_size_le_cap (n p M t : ℕ) (ht : t≤M) : size n p 1 1 t+p≤generatorCap n p M := by
  have hh := size_uniform n p 1 1 M t ht
  simpa only [generatorCap,show 1+p+1=p+2 by omega] using hh

theorem historyProbes_uniform (n p M t : ℕ) (ht : t≤M) :
    historyProbes n p 1 1 t≤2*t*generatorCap n p M := by
  induction t with
  | zero => simp [historyProbes]
  | succ t ih =>
    have hi := ih (by omega)
    have hs := frozen_size_le_cap n p M t (by omega)
    simp only [historyProbes]
    nlinarith

def geometryCap (n p T M : ℕ) : ℕ := max (queryCap n p 1 1 M) (T+1+(2*M+1)*generatorCap n p M)

theorem geometryCap_ge_frame (n p T M : ℕ) : T≤geometryCap n p T M :=
  (by omega : T≤T+1+(2*M+1)*generatorCap n p M).trans (le_max_right _ _)

theorem geometryCap_query {n p T M r D : ℕ} (hD : geometryCap n p T M+r≤D) :
    queryCap n p 1 1 M+r≤D :=
  (Nat.add_le_add_right (le_max_left _ _) r).trans hD

theorem geometryCap_edge {n p T M r D : ℕ} (hD : geometryCap n p T M+r≤D) (t : ℕ) (ht : t<M) :
    T+(1+((size n p 1 1 t+p)+historyProbes n p 1 1 t))+r≤D := by
  have hs := frozen_size_le_cap n p M t (by omega)
  have hh := historyProbes_uniform n p M t (by omega)
  have hm : 2*t*generatorCap n p M≤2*M*generatorCap n p M :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 (by omega))
  have hc := le_max_right (queryCap n p 1 1 M) (T+1+(2*M+1)*generatorCap n p M)
  change T+1+(2*M+1)*generatorCap n p M≤geometryCap n p T M at hc
  have hphase : T+(1+((size n p 1 1 t+p)+historyProbes n p 1 1 t))≤geometryCap n p T M := by
    nlinarith
  exact (Nat.add_le_add_right hphase r).trans hD

end Bilevel.TransportRound
