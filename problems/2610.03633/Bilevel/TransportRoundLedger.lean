import Bilevel.TransportRoundGrantFacts

/-! Deterministic sequential analysis ledger for the genuine frozen batch.
Only the target spaces are enlarged while processing blocks. Every source
image is computed from the original frozen generators. After both phases,
the ledger equals the actual simultaneous batch output exactly. -/
noncomputable section
namespace Bilevel.TransportRound
open EuclideanGaussian TransportNetwork OrthogonalAction
set_option maxHeartbeats 800000

abbrev LedgerBlock (n D : ℕ) := Vertex n × Submodule ℝ (Space D)

def mergeBlock {n D : ℕ} (W : Known n D) (b : LedgerBlock n D) : Known n D :=
  Function.update W b.1 (W b.1⊔b.2)

theorem le_mergeBlock {n D : ℕ} (W : Known n D) (b : LedgerBlock n D) (v : Vertex n) : W v≤mergeBlock W b v := by
  by_cases hv : v=b.1
  · subst v; rw [mergeBlock,Function.update_self]; exact le_sup_left
  · rw [mergeBlock,Function.update_of_ne hv]

theorem block_le_mergeBlock {n D : ℕ} (W : Known n D) (b : LedgerBlock n D) : b.2≤mergeBlock W b b.1 := by
  rw [mergeBlock,Function.update_self]
  exact le_sup_right

theorem mergeBlock_le {n D : ℕ} (W V : Known n D) (b : LedgerBlock n D)
    (hW : ∀ v,W v≤V v) (hb : b.2≤V b.1) : ∀ v,mergeBlock W b v≤V v := by
  intro v
  by_cases hv : v=b.1
  · subst v; rw [mergeBlock,Function.update_self]; exact sup_le (hW _) hb
  · rw [mergeBlock,Function.update_of_ne hv]; exact hW v

def mergeBlocks {n D : ℕ} : List (LedgerBlock n D) → Known n D → Known n D
  | [],W => W
  | b::bs,W => mergeBlocks bs (mergeBlock W b)

theorem le_mergeBlocks {n D : ℕ} (bs : List (LedgerBlock n D)) (W : Known n D) (v : Vertex n) :
    W v≤mergeBlocks bs W v := by
  induction bs generalizing W with
  | nil => exact le_rfl
  | cons b bs ih => exact (le_mergeBlock W b v).trans (ih _)

theorem mergeBlocks_le {n D : ℕ} (bs : List (LedgerBlock n D)) (W V : Known n D)
    (hW : ∀ v,W v≤V v) (hbs : ∀ b∈bs,b.2≤V b.1) : ∀ v,mergeBlocks bs W v≤V v := by
  induction bs generalizing W with
  | nil => exact hW
  | cons b bs ih =>
    exact ih _ (mergeBlock_le W V b hW (hbs b List.mem_cons_self))
      (fun b' hb' => hbs b' (List.mem_cons_of_mem b hb'))

theorem block_le_mergeBlocks {n D : ℕ} (bs : List (LedgerBlock n D)) (W : Known n D)
    (b : LedgerBlock n D) (hb : b∈bs) : b.2≤mergeBlocks bs W b.1 := by
  induction bs generalizing W with
  | nil => simp only [List.not_mem_nil] at hb
  | cons b' bs ih =>
    rcases List.mem_cons.mp hb with he | ht
    · subst b'; exact (block_le_mergeBlock W b).trans (le_mergeBlocks bs (mergeBlock W b) b.1)
    · exact ih (mergeBlock W b') ht

def forwardBlocks {n D m : ℕ} (g : Generators n D m) (z : Latent n D) : List (LedgerBlock n D) :=
  List.ofFn (fun e : Edge n => (dst e,(known g (src e)).map (isometry D (z.2 e)).toLinearEquiv.toLinearMap))

def reverseBlocks {n D m : ℕ} (g : Generators n D m) (z : Latent n D) : List (LedgerBlock n D) :=
  List.ofFn (fun e : Edge n => (src e,(known g (dst e)).map (isometry D ((z.2 e)⁻¹)).toLinearEquiv.toLinearMap))

def forwardLedger {n D m : ℕ} (g : Generators n D m) (z : Latent n D) (W : Known n D) : Known n D :=
  mergeBlocks (forwardBlocks g z) W

def reverseLedger {n D m : ℕ} (g : Generators n D m) (z : Latent n D) (W : Known n D) : Known n D :=
  mergeBlocks (reverseBlocks g z) W

theorem forwardImage_le_ledger {n D m : ℕ} (g : Generators n D m) (z : Latent n D) (W : Known n D) (e : Edge n) :
    (known g (src e)).map (isometry D (z.2 e)).toLinearEquiv.toLinearMap≤forwardLedger g z W (dst e) := by
  apply block_le_mergeBlocks (forwardBlocks g z) W
    (dst e,(known g (src e)).map (isometry D (z.2 e)).toLinearEquiv.toLinearMap)
  exact List.mem_ofFn.mpr ⟨e,rfl⟩

theorem reverseImage_le_ledger {n D m : ℕ} (g : Generators n D m) (z : Latent n D) (W : Known n D) (e : Edge n) :
    (known g (dst e)).map (isometry D ((z.2 e)⁻¹)).toLinearEquiv.toLinearMap≤reverseLedger g z W (src e) := by
  apply block_le_mergeBlocks (reverseBlocks g z) W
    (src e,(known g (dst e)).map (isometry D ((z.2 e)⁻¹)).toLinearEquiv.toLinearMap)
  exact List.mem_ofFn.mpr ⟨e,rfl⟩

theorem ledgers_eq_execute {n D m : ℕ} (g : Generators n D m) (z : Latent n D) (W : Known n D)
    (hlow : ∀ v,known g v≤W v) (hup : ∀ v,W v≤known (execute g z) v) :
    reverseLedger g z (forwardLedger g z W)=known (execute g z) := by
  funext v
  apply le_antisymm
  · apply mergeBlocks_le (reverseBlocks g z) _ _
    · apply mergeBlocks_le (forwardBlocks g z) W _ hup
      intro b hb
      obtain ⟨e,rfl⟩ := List.mem_ofFn.mp hb
      exact forward_whole_space g z e
    · intro b hb
      obtain ⟨e,rfl⟩ := List.mem_ofFn.mp hb
      exact reverse_whole_space g z e
  · rw [execute_span]
    apply sup_le
    · exact (hlow v).trans ((le_mergeBlocks (forwardBlocks g z) W v).trans
        (le_mergeBlocks (reverseBlocks g z) (forwardLedger g z W) v))
    · apply Submodule.span_le.mpr
      rintro x ⟨i,rfl⟩
      have hv := i.property
      have hm : batchObservation (probes g) z i.val∈
          reverseLedger g z (forwardLedger g z W) (outputLayer (probes g i.val)) := by
        refine Fin.addCases ?_ ?_ i.val
        · intro j
          let ei : Edge n × Fin m := finProdFinEquiv.symm j
          simp only [probes,Fin.append_left,forwardProbes,batchObservation,probeObservation,
            Bool.false_eq_true,ite_false,outputLayer,forwardObservation]
          apply le_mergeBlocks (reverseBlocks g z) (forwardLedger g z W) (dst ei.1)
          apply forwardImage_le_ledger g z W ei.1
          exact ⟨g (src ei.1) ei.2,TransportGeneratorStore.generator_mem _ _,rfl⟩
        · intro j
          let ei : Edge n × Fin m := finProdFinEquiv.symm j
          simp only [probes,Fin.append_right,reverseProbes,batchObservation,probeObservation,
            ite_true,outputLayer,reverseObservation]
          apply reverseImage_le_ledger g z (forwardLedger g z W) ei.1
          exact ⟨g (dst ei.1) ei.2,TransportGeneratorStore.generator_mem _ _,rfl⟩
      rw [hv] at hm
      exact hm

theorem granted_ledgers_eq_execute {n D m T : ℕ} (hT : T≤D) (t : ℕ)
    (g : Generators n D m) (z : Latent n D)
    (hprefix : ∀ v i,Protected t v i→frame T hT z v i∈known g v) :
    reverseLedger g z (forwardLedger g z (known (postGrant T hT t g z)))=known (execute g z) :=
  ledgers_eq_execute g z _ (postGrant_keeps T hT t g z) (postGrant_le_execute T hT t g z hprefix)

end Bilevel.TransportRound
