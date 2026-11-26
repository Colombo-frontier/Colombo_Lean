import Bilevel.TransportRoundMonitorReduction

/-! On a path, distinct forward edges have distinct target layers, as do
distinct reverse edges. Consequently the real sequential ghost monitor union
can be expressed using the initial target ledger of each phase. No current
edge output is needed to form its own target before its check. -/
noncomputable section
namespace Bilevel.TransportRound
open EuclideanGaussian OrthogonalAction TransportNetwork TransportEdgePosterior
set_option maxHeartbeats 600000

theorem forwardMonitor_merge_ne {n D m T : ℕ} (hT : T≤D) (t : ℕ)
    (g : Generators n D m) (z : Latent n D) (P : Edge n → Pairs D) (W : Known n D)
    (e f : Edge n) (hne : f≠e) :
    forwardMonitor hT t g z P (mergeBlock W (forwardBlock g z e)) f ↔ forwardMonitor hT t g z P W f := by
  have hd : dst f≠dst e := fun h => hne (Fin.succ_injective n h)
  unfold forwardMonitor mergeBlock forwardBlock
  rw [Function.update_of_ne hd]

theorem reverseMonitor_merge_ne {n D m T : ℕ} (hT : T≤D) (t : ℕ)
    (g : Generators n D m) (z : Latent n D) (P : Edge n → Pairs D) (W : Known n D)
    (e f : Edge n) (hne : f≠e) :
    reverseMonitor hT t g z P (mergeBlock W (reverseBlock g z e)) f ↔ reverseMonitor hT t g z P W f := by
  have hd : src f≠src e := fun h => hne (Fin.castSucc_injective n h)
  unfold reverseMonitor mergeBlock reverseBlock
  rw [Function.update_of_ne hd]

theorem forwardFailure_distinct {n D m T : ℕ} (hT : T≤D) (t : ℕ)
    (g : Generators n D m) (z : Latent n D) (P : Edge n → Pairs D)
    (es : List (Edge n)) (hn : es.Nodup) (W : Known n D) :
    forwardFailure hT t g z P es W ↔ ∃ e∈es,forwardMonitor hT t g z P W e := by
  induction es generalizing W with
  | nil => simp only [forwardFailure,List.not_mem_nil,false_and,exists_false]
  | cons e es ih =>
    have hne := (List.nodup_cons.mp hn).1
    have ht := (List.nodup_cons.mp hn).2
    rw [forwardFailure,ih ht]
    constructor
    · rintro (hb|⟨f,hf,hb⟩)
      · exact ⟨e,List.mem_cons_self,hb⟩
      · exact ⟨f,List.mem_cons_of_mem e hf,
          (forwardMonitor_merge_ne hT t g z P W e f (by intro he; subst f; exact hne hf)).mp hb⟩
    · rintro ⟨f,hf,hb⟩
      rcases List.mem_cons.mp hf with he|hf
      · subst f; exact Or.inl hb
      · exact Or.inr ⟨f,hf,(forwardMonitor_merge_ne hT t g z P W e f
          (by intro he; subst f; exact hne hf)).mpr hb⟩

theorem reverseFailure_distinct {n D m T : ℕ} (hT : T≤D) (t : ℕ)
    (g : Generators n D m) (z : Latent n D) (P : Edge n → Pairs D)
    (es : List (Edge n)) (hn : es.Nodup) (W : Known n D) :
    reverseFailure hT t g z P es W ↔ ∃ e∈es,reverseMonitor hT t g z P W e := by
  induction es generalizing W with
  | nil => simp only [reverseFailure,List.not_mem_nil,false_and,exists_false]
  | cons e es ih =>
    have hne := (List.nodup_cons.mp hn).1
    have ht := (List.nodup_cons.mp hn).2
    rw [reverseFailure,ih ht]
    constructor
    · rintro (hb|⟨f,hf,hb⟩)
      · exact ⟨e,List.mem_cons_self,hb⟩
      · exact ⟨f,List.mem_cons_of_mem e hf,
          (reverseMonitor_merge_ne hT t g z P W e f (by intro he; subst f; exact hne hf)).mp hb⟩
    · rintro ⟨f,hf,hb⟩
      rcases List.mem_cons.mp hf with he|hf
      · subst f; exact Or.inl hb
      · exact Or.inr ⟨f,hf,(reverseMonitor_merge_ne hT t g z P W e f
          (by intro he; subst f; exact hne hf)).mpr hb⟩

theorem batchFailure_distinct {n D m T : ℕ} (hT : T≤D) (t : ℕ)
    (g : Generators n D m) (z : Latent n D) (P : Edge n → Pairs D) :
    batchFailure hT t g z P ↔
      (∃ e,forwardMonitor hT t g z P (known (postGrant T hT t g z)) e) ∨
      (∃ e,reverseMonitor hT t g z P (forwardLedger g z (known (postGrant T hT t g z))) e) := by
  have hn : (List.ofFn (fun e : Edge n => e)).Nodup := List.nodup_ofFn.mpr Function.injective_id
  rw [batchFailure,forwardFailure_distinct hT t g z P _ hn,reverseFailure_distinct hT t g z P _ hn]
  simp only [List.mem_ofFn,exists_eq,true_and]

end Bilevel.TransportRound
