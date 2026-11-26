import Bilevel.TransportControllerHistory
import Bilevel.TransportControllerPairedStore
import Bilevel.TransportRoundUnprotected

/-! Actual edge-action pairs recorded from each executed frozen round.
The storage order is fixed; the set of constraints is exactly the disclosed
forward and reverse pairs. Their physical domains and ranges lie in the
actual carried generator spaces at every round. -/
noncomputable section
namespace Bilevel.TransportRound
open EuclideanGaussian TransportNetwork TransportEdgePosterior OrthogonalAction
set_option maxHeartbeats 800000

def forwardPairs {n D m : ℕ} (e : Edge n) (g : Generators n D m) (z : Latent n D) : Pairs D :=
  TransportControllerPairedStore.pairs (g (src e),fun i => z.2 e • g (src e) i)

def reversePairs {n D m : ℕ} (e : Edge n) (g : Generators n D m) (z : Latent n D) : Pairs D :=
  TransportControllerPairedStore.pairs ((fun i => (z.2 e)⁻¹ • g (dst e) i),g (dst e))

def recordBatch {n D m : ℕ} (e : Edge n) (g : Generators n D m) (z : Latent n D) (L : Pairs D) : Pairs D :=
  reversePairs e g z++forwardPairs e g z++L

theorem forwardPairs_domain {n D m : ℕ} (e : Edge n) (g : Generators n D m) (z : Latent n D) :
    domain (forwardPairs e g z)=known g (src e) := TransportControllerPairedStore.domain_pairs _

theorem forwardPairs_range {n D m : ℕ} (e : Edge n) (g : Generators n D m) (z : Latent n D) :
    range (forwardPairs e g z)=(known g (src e)).map (isometry D (z.2 e)).toLinearEquiv.toLinearMap := by
  rw [forwardPairs,TransportControllerPairedStore.range_pairs]
  exact TransportGeneratorStore.transported_span _ _

theorem reversePairs_domain {n D m : ℕ} (e : Edge n) (g : Generators n D m) (z : Latent n D) :
    domain (reversePairs e g z)=(known g (dst e)).map (isometry D ((z.2 e)⁻¹)).toLinearEquiv.toLinearMap := by
  rw [reversePairs,TransportControllerPairedStore.domain_pairs]
  exact TransportGeneratorStore.transported_span _ _

theorem reversePairs_range {n D m : ℕ} (e : Edge n) (g : Generators n D m) (z : Latent n D) :
    range (reversePairs e g z)=known g (dst e) := TransportControllerPairedStore.range_pairs _

theorem supports_append {D : ℕ} (L P : Pairs D) (O : OrthogonalHaar.Group D) :
    Supports (L++P) O ↔ Supports L O ∧ Supports P O := by
  induction L with
  | nil => simp [Supports]
  | cons pair L ih => simp only [List.cons_append,Supports,ih,and_assoc]

theorem recordBatch_supported {n D m : ℕ} (e : Edge n) (g : Generators n D m) (z : Latent n D)
    (L : Pairs D) (hL : Supports L (z.2 e)) : Supports (recordBatch e g z L) (z.2 e) := by
  rw [recordBatch,supports_append,supports_append]
  refine ⟨⟨?_,?_⟩,hL⟩
  · apply (TransportControllerPairedStore.pairs_supported _ _).mpr
    intro i
    exact smul_inv_smul (z.2 e) _
  · apply (TransportControllerPairedStore.pairs_supported _ _).mpr
    intro i
    rfl

theorem recordBatch_included {n D m : ℕ} (e : Edge n) (g : Generators n D m) (z : Latent n D)
    (L : Pairs D) (hdom : domain L≤known g (src e)) (hran : range L≤known g (dst e)) :
    domain (recordBatch e g z L)≤known (execute g z) (src e) ∧
      range (recordBatch e g z L)≤known (execute g z) (dst e) := by
  simp only [recordBatch,domain_append,range_append,forwardPairs_domain,forwardPairs_range,
    reversePairs_domain,reversePairs_range]
  constructor
  · exact sup_le (sup_le (reverse_whole_space g z e) (keeps_old g z (src e)))
      (hdom.trans (keeps_old g z (src e)))
  · exact sup_le (sup_le (keeps_old g z (dst e)) (forward_whole_space g z e))
      (hran.trans (keeps_old g z (dst e)))

theorem recordBatch_length {n D m : ℕ} (e : Edge n) (g : Generators n D m) (z : Latent n D) (L : Pairs D) :
    (recordBatch e g z L).length=2*m+L.length := by
  simp only [recordBatch,List.length_append,forwardPairs,reversePairs,TransportControllerPairedStore.pairs,List.length_ofFn]
  omega

def runPairs {H : Type*} {n D p c m T : ℕ} (hT : T≤D)
    (choose : ∀ t, H × Generators n D (size n p c m t) → Queries n D p)
    (respond : ∀ t, StepData H n D (size n p c m t) p T → H)
    (names : ℕ → Vertex n → Fin c → Option (Fin T))
    (s : H × Generators n D m) (z : Latent n D) (e : Edge n) : ℕ → Pairs D
  | 0 => []
  | t+1 =>
    let st := run T hT choose respond names s z t
    recordBatch e (augment st.2 (choose t st)) z (runPairs hT choose respond names s z e t)

theorem runPairs_supported {H : Type*} {n D p c m T : ℕ} (hT : T≤D)
    (choose : ∀ t, H × Generators n D (size n p c m t) → Queries n D p)
    (respond : ∀ t, StepData H n D (size n p c m t) p T → H)
    (names : ℕ → Vertex n → Fin c → Option (Fin T))
    (s : H × Generators n D m) (z : Latent n D) (e : Edge n) (t : ℕ) :
    Supports (runPairs hT choose respond names s z e t) (z.2 e) := by
  induction t with
  | zero => trivial
  | succ t ih => exact recordBatch_supported e _ z _ ih

theorem runPairs_included {H : Type*} {n D p c m T : ℕ} (hT : T≤D)
    (choose : ∀ t, H × Generators n D (size n p c m t) → Queries n D p)
    (respond : ∀ t, StepData H n D (size n p c m t) p T → H)
    (names : ℕ → Vertex n → Fin c → Option (Fin T))
    (s : H × Generators n D m) (z : Latent n D) (e : Edge n) (t : ℕ) :
    domain (runPairs hT choose respond names s z e t)≤known (run T hT choose respond names s z t).2 (src e) ∧
      range (runPairs hT choose respond names s z e t)≤known (run T hT choose respond names s z t).2 (dst e) := by
  induction t with
  | zero => exact ⟨bot_le,bot_le⟩
  | succ t ih =>
    let st := run T hT choose respond names s z t
    have hd : domain (runPairs hT choose respond names s z e t)≤known (augment st.2 (choose t st)) (src e) := by
      rw [augment_span]
      exact ih.1.trans le_sup_left
    have hr : range (runPairs hT choose respond names s z e t)≤known (augment st.2 (choose t st)) (dst e) := by
      rw [augment_span]
      exact ih.2.trans le_sup_left
    have hh := recordBatch_included e (augment st.2 (choose t st)) z _ hd hr
    change domain (recordBatch e (augment st.2 (choose t st)) z _)≤known (augment _ _) (src e) ∧
      range (recordBatch e (augment st.2 (choose t st)) z _)≤known (augment _ _) (dst e)
    rw [augment_span,augment_span]
    exact ⟨hh.1.trans le_sup_left,hh.2.trans le_sup_left⟩

theorem runPairs_length_bound {H : Type*} {n D p c m T : ℕ} (hn : 0<n) (hT : T≤D)
    (choose : ∀ t, H × Generators n D (size n p c m t) → Queries n D p)
    (respond : ∀ t, StepData H n D (size n p c m t) p T → H)
    (names : ℕ → Vertex n → Fin c → Option (Fin T))
    (s : H × Generators n D m) (z : Latent n D) (e : Edge n) (t : ℕ) :
    (runPairs hT choose respond names s z e t).length≤historySize n p c m t := by
  induction t with
  | zero => simp [runPairs,historySize]
  | succ t ih =>
    rw [runPairs,recordBatch_length,historySize]
    nlinarith

end Bilevel.TransportRound
