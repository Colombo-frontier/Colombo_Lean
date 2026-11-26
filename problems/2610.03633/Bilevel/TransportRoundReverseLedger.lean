import Bilevel.TransportRoundForwardLedger
import Bilevel.TransportRoundReverseEnergy

/-! Reverse ledger with the actual forward-updated pairs and frozen inputs.
Its intermediate source-energy preconditions are proved from a finite final
budget, rather than assumed for every intermediate state. -/
noncomputable section
namespace Bilevel.TransportRound
open EuclideanGaussian TransportNetwork TransportEdgePosterior OrthogonalAction ProjectionGeometry TransportObserver
set_option maxHeartbeats 800000

def reverseBlock {n D m : ℕ} (g : Generators n D m) (z : Latent n D) (e : Edge n) : LedgerBlock n D :=
  (src e,(known g (dst e)).map (isometry D ((z.2 e)⁻¹)).toLinearEquiv.toLinearMap)

def reverseAlong {n D m : ℕ} (g : Generators n D m) (z : Latent n D)
    (es : List (Edge n)) (W : Known n D) : Known n D := mergeBlocks (es.map (reverseBlock g z)) W

def reverseMonitor {n D m T : ℕ} (hT : T≤D) (t : ℕ) (g : Generators n D m) (z : Latent n D)
    (P : Edge n → Pairs D) (W : Known n D) (e : Edge n) : Prop :=
  TransportControllerEdge.angleBad (W (src e))
    (residualSpace (domain (reverseHardPairs T hT e z++swapPairs (forwardPairs e g z++P e)))
      (residualSpace (protectedDomain (frame T hT z (dst e)) (swapPairs (forwardPairs e g z++P e))
        (oldProtected T t (src e))) (known g (dst e)))) ((z.2 e)⁻¹)

def reverseFailure {n D m T : ℕ} (hT : T≤D) (t : ℕ) (g : Generators n D m) (z : Latent n D)
    (P : Edge n → Pairs D) : List (Edge n) → Known n D → Prop
  | [],_ => False
  | e::es,W => reverseMonitor hT t g z P W e ∨ reverseFailure hT t g z P es (mergeBlock W (reverseBlock g z e))

theorem reverse_merge_energy {n D m T : ℕ} (hT : T≤D) (hn : 0<n) (t : ℕ)
    (g : Generators n D m) (z : Latent n D) (P : Edge n → Pairs D) (e : Edge n)
    (hP : Supports (P e) (z.2 e)) (hPS : domain (P e)≤known g (src e)) (hPD : range (P e)≤known g (dst e))
    (hprefix : ∀ v i,Protected t v i→frame T hT z v i∈known g v)
    (W : Known n D) (hW : ∀ v,forwardLedger g z (known (postGrant T hT t g z)) v≤W v)
    (hsmall : TransportRoundEnergy.total W (frame T hT z) (postFuture T t)≤(1:ℝ)/4096)
    (hgood : ¬reverseMonitor hT t g z P W e) :
    TransportRoundEnergy.total (mergeBlock W (reverseBlock g z e)) (frame T hT z) (postFuture T t) ≤
      17*TransportRoundEnergy.total W (frame T hT z) (postFuture T t) := by
  have hgrant : ∀ v,known (postGrant T hT t g z) v≤W v := fun v =>
    (le_mergeBlocks (forwardBlocks g z) _ v).trans (hW v)
  have himage : (known g (src e)).map (isometry D (z.2 e)).toLinearEquiv.toLinearMap≤W (dst e) :=
    (forwardImage_le_ledger g z _ e).trans (hW (dst e))
  have hh := reverse_frozen_energy hT hn t g z e (P e) hP hPS hPD hprefix (W (dst e)) (W (src e))
    (sup_le (hgrant (dst e)) himage) (hgrant (src e))
    (TransportRoundEnergy.row_le_total W (frame T hT z) (postFuture T t) (dst e)) hsmall hgood
  have hu := TransportRoundEnergy.total_update W (frame T hT z) (postFuture T t) (src e)
    (W (src e)⊔(known g (dst e)).map (isometry D ((z.2 e)⁻¹)).toLinearEquiv.toLinearMap) (postFuture T t (src e))
  rw [Function.update_eq_self] at hu
  have hrow := TransportRoundEnergy.row_le_total W (frame T hT z) (postFuture T t) (src e)
  change TransportRoundEnergy.total (mergeBlock W (reverseBlock g z e)) (frame T hT z) (postFuture T t)=_ at hu
  linarith

theorem reverseAlong_energy {n D m T : ℕ} (hT : T≤D) (hn : 0<n) (t : ℕ)
    (g : Generators n D m) (z : Latent n D) (P : Edge n → Pairs D)
    (hP : ∀ e,Supports (P e) (z.2 e))
    (hPS : ∀ e,domain (P e)≤known g (src e)) (hPD : ∀ e,range (P e)≤known g (dst e))
    (hprefix : ∀ v i,Protected t v i→frame T hT z v i∈known g v)
    (es : List (Edge n)) (W : Known n D)
    (hW : ∀ v,forwardLedger g z (known (postGrant T hT t g z)) v≤W v)
    (hbudget : 17^es.length*TransportRoundEnergy.total W (frame T hT z) (postFuture T t)≤(1:ℝ)/4096)
    (hgood : ¬reverseFailure hT t g z P es W) :
    TransportRoundEnergy.total (reverseAlong g z es W) (frame T hT z) (postFuture T t) ≤
      17^es.length*TransportRoundEnergy.total W (frame T hT z) (postFuture T t) := by
  induction es generalizing W with
  | nil => simpa only [reverseAlong,List.map_nil,mergeBlocks,List.length_nil,pow_zero,one_mul] using le_rfl
  | cons e es ih =>
    have hg := not_or.mp hgood
    have hp : (1:ℝ)≤17^(e::es).length := one_le_pow₀ (by norm_num)
    have hnon := TransportRoundEnergy.total_nonneg W (frame T hT z) (postFuture T t)
    have hsmall : TransportRoundEnergy.total W (frame T hT z) (postFuture T t)≤(1:ℝ)/4096 := by
      have hm := mul_le_mul_of_nonneg_right hp hnon
      simp only [one_mul] at hm
      exact hm.trans hbudget
    have hs := reverse_merge_energy hT hn t g z P e (hP e) (hPS e) (hPD e) hprefix W hW hsmall hg.1
    have htail : 17^es.length*TransportRoundEnergy.total (mergeBlock W (reverseBlock g z e))
        (frame T hT z) (postFuture T t)≤(1:ℝ)/4096 := by
      have hh := mul_le_mul_of_nonneg_left hs (by positivity : (0:ℝ)≤17^es.length)
      apply hh.trans
      convert hbudget using 1
      rw [List.length_cons,pow_succ]
      ring
    have ht := ih (mergeBlock W (reverseBlock g z e))
      (fun v => (hW v).trans (le_mergeBlock W (reverseBlock g z e) v)) htail hg.2
    apply ht.trans
    have hh := mul_le_mul_of_nonneg_left hs (by positivity : (0:ℝ)≤17^es.length)
    convert hh using 1
    rw [List.length_cons,pow_succ]
    ring

theorem reverseAlong_all {n D m : ℕ} (g : Generators n D m) (z : Latent n D) (W : Known n D) :
    reverseAlong g z (List.ofFn (fun e : Edge n => e)) W=reverseLedger g z W := by
  simp only [reverseAlong,List.map_ofFn,reverseLedger,reverseBlocks,reverseBlock,Function.comp_def]

end Bilevel.TransportRound
