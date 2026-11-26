import Bilevel.TransportRoundLedger
import Bilevel.TransportRoundForwardEnergy

/-! Forward phase of the same-run ledger, including its actual fresh monitor
event. The frozen old energy is retained as a fixed source budget. There is
no assumption of an energy recurrence: the factor nine is derived from each
real protected-block update and the exact sum of ledger row energies. -/
noncomputable section
namespace Bilevel.TransportRound
open EuclideanGaussian TransportNetwork TransportEdgePosterior OrthogonalAction ProjectionGeometry TransportObserver
set_option maxHeartbeats 800000

def forwardBlock {n D m : ℕ} (g : Generators n D m) (z : Latent n D) (e : Edge n) : LedgerBlock n D :=
  (dst e,(known g (src e)).map (isometry D (z.2 e)).toLinearEquiv.toLinearMap)

def forwardAlong {n D m : ℕ} (g : Generators n D m) (z : Latent n D)
    (es : List (Edge n)) (W : Known n D) : Known n D := mergeBlocks (es.map (forwardBlock g z)) W

def forwardMonitor {n D m T : ℕ} (hT : T≤D) (t : ℕ) (g : Generators n D m) (z : Latent n D)
    (P : Edge n → Pairs D) (W : Known n D) (e : Edge n) : Prop :=
  TransportControllerEdge.angleBad (W (dst e))
    (residualSpace (domain (hardPairs T hT e z++P e))
      (residualSpace (protectedDomain (frame T hT z (src e)) (P e) (oldProtected T t (src e)))
        (known g (src e)))) (z.2 e)

def forwardFailure {n D m T : ℕ} (hT : T≤D) (t : ℕ) (g : Generators n D m) (z : Latent n D)
    (P : Edge n → Pairs D) : List (Edge n) → Known n D → Prop
  | [],_ => False
  | e::es,W => forwardMonitor hT t g z P W e ∨ forwardFailure hT t g z P es (mergeBlock W (forwardBlock g z e))

theorem forward_merge_energy {n D m T : ℕ} (hT : T≤D) (hn : 0<n) (t : ℕ)
    (g : Generators n D m) (z : Latent n D) (P : Edge n → Pairs D) (e : Edge n)
    (hP : Supports (P e) (z.2 e)) (hPS : domain (P e)≤known g (src e)) (hPD : range (P e)≤known g (dst e))
    (hprefix : ∀ v i,Protected t v i→frame T hT z v i∈known g v)
    (W : Known n D) (hW : ∀ v,known (postGrant T hT t g z) v≤W v)
    (hsmall : TransportRoundEnergy.total (known g) (frame T hT z) (oldFuture T t)≤(1:ℝ)/4096)
    (hgood : ¬forwardMonitor hT t g z P W e) :
    TransportRoundEnergy.total (mergeBlock W (forwardBlock g z e)) (frame T hT z) (postFuture T t)+
        TransportRoundEnergy.total (known g) (frame T hT z) (oldFuture T t) ≤
      9*(TransportRoundEnergy.total W (frame T hT z) (postFuture T t)+
        TransportRoundEnergy.total (known g) (frame T hT z) (oldFuture T t)) := by
  classical
  let B := TransportRoundEnergy.total (known g) (frame T hT z) (oldFuture T t)
  have hI : postFuture T t (dst e)⊆Finset.univ\oldProtected T t (src e) := by
    rw [postFuture_dst,oldFuture_eq_complement]
  have hKsrc : ∀ i∈oldProtected T t (src e),frame T hT z (src e) i∈known g (src e) := by
    intro i hi
    apply hprefix
    simpa only [oldProtected,Finset.mem_filter,Finset.mem_univ,true_and] using hi
  have hKdst : ∀ i∈oldProtected T t (src e),frame T hT z (dst e) i∈W (dst e) := by
    intro i hi
    apply hW
    apply postGrant_prefix T hT hn t g z hprefix
    apply paired_dst_post t e i
    simpa only [oldProtected,Finset.mem_filter,Finset.mem_univ,true_and] using hi
  have hsource : frameEnergy (known g (src e)) (frame T hT z (src e)) (Finset.univ\oldProtected T t (src e))≤B := by
    rw [← oldFuture_eq_complement]
    exact TransportRoundEnergy.row_le_total _ _ _ (src e)
  have hh := edge_block_energy hT e z (P e) hP (known g (src e)) (known g (src e)) (W (dst e))
    (oldProtected T t (src e)) (postFuture T t (dst e)) hI hPS le_rfl hKsrc
    (hPD.trans ((postGrant_keeps T hT t g z (dst e)).trans (hW (dst e)))) hKdst hsource hsmall hgood
  have hu := TransportRoundEnergy.total_update W (frame T hT z) (postFuture T t) (dst e)
    (W (dst e)⊔(known g (src e)).map (isometry D (z.2 e)).toLinearEquiv.toLinearMap) (postFuture T t (dst e))
  rw [Function.update_eq_self] at hu
  have hrow := TransportRoundEnergy.row_le_total W (frame T hT z) (postFuture T t) (dst e)
  change TransportRoundEnergy.total (mergeBlock W (forwardBlock g z e)) (frame T hT z) (postFuture T t)=_ at hu
  change _+B≤9*(_+B)
  linarith

theorem forwardAlong_energy {n D m T : ℕ} (hT : T≤D) (hn : 0<n) (t : ℕ)
    (g : Generators n D m) (z : Latent n D) (P : Edge n → Pairs D)
    (hP : ∀ e,Supports (P e) (z.2 e))
    (hPS : ∀ e,domain (P e)≤known g (src e)) (hPD : ∀ e,range (P e)≤known g (dst e))
    (hprefix : ∀ v i,Protected t v i→frame T hT z v i∈known g v)
    (es : List (Edge n)) (W : Known n D) (hW : ∀ v,known (postGrant T hT t g z) v≤W v)
    (hsmall : TransportRoundEnergy.total (known g) (frame T hT z) (oldFuture T t)≤(1:ℝ)/4096)
    (hgood : ¬forwardFailure hT t g z P es W) :
    TransportRoundEnergy.total (forwardAlong g z es W) (frame T hT z) (postFuture T t)+
        TransportRoundEnergy.total (known g) (frame T hT z) (oldFuture T t) ≤
      9^es.length*(TransportRoundEnergy.total W (frame T hT z) (postFuture T t)+
        TransportRoundEnergy.total (known g) (frame T hT z) (oldFuture T t)) := by
  induction es generalizing W with
  | nil => simp [forwardAlong,mergeBlocks]
  | cons e es ih =>
    have hg := not_or.mp hgood
    have hstep := forward_merge_energy hT hn t g z P e (hP e) (hPS e) (hPD e) hprefix W hW hsmall hg.1
    have ht := ih (mergeBlock W (forwardBlock g z e))
      (fun v => (hW v).trans (le_mergeBlock W (forwardBlock g z e) v)) hg.2
    apply ht.trans
    calc
      _ ≤ 9^es.length*(9*(TransportRoundEnergy.total W (frame T hT z) (postFuture T t)+
          TransportRoundEnergy.total (known g) (frame T hT z) (oldFuture T t))) :=
        mul_le_mul_of_nonneg_left hstep (by positivity)
      _ = _ := by rw [List.length_cons,pow_succ]; ring

theorem forwardAlong_all {n D m : ℕ} (g : Generators n D m) (z : Latent n D) (W : Known n D) :
    forwardAlong g z (List.ofFn (fun e : Edge n => e)) W=forwardLedger g z W := by
  simp only [forwardAlong,List.map_ofFn,forwardLedger,forwardBlocks,forwardBlock,Function.comp_def]

end Bilevel.TransportRound
