import NCConcave16991.MixedHaarProgramMeasurable
import Mathlib.MeasureTheory.MeasurableSpace.Constructions

/-! # Actual reply recording and consistency with a fixed latent oracle -/

namespace NCConcave16991.OracleProgram

open MeasureTheory Set

variable {Q R X Ω Θ : Type*} [MeasurableSpace Q] [MeasurableSpace R]
  [MeasurableSpace X] [MeasurableSpace Ω] [MeasurableSpace Θ] {T : ℕ}

def recordReplies (P : Fixed Q R X Ω T) : Fixed Q R (X × (Fin T → R)) Ω T where
  ask := P.ask
  finish seed replies := (P.finish seed replies,replies)
  ask_measurable := P.ask_measurable
  finish_measurable := P.finish_measurable.prodMk measurable_snd

def cachePrefix (replies : Fin T → R) (t : Fin T) : Fin t.val → R :=
  fun i ↦ replies ⟨i.val,lt_trans i.isLt t.isLt⟩

def CacheConsistent (P : Fixed Q R X Ω T) (A : Q → R) (seed : Ω) (replies : Fin T → R) : Prop :=
  ∀ t : Fin T, A (P.ask t seed (cachePrefix replies t)) = replies t

def PrefixConsistent (P : Fixed Q R X Ω T) (A : Q → R) (seed : Ω)
    (t : ℕ) (replies : Fin t → R) : Prop :=
  ∀ i : Fin t, ∀ hi : i.val < T,
    A (P.ask ⟨i.val,hi⟩ seed (fun j : Fin i.val ↦ replies ⟨j.val,lt_trans j.isLt i.isLt⟩)) = replies i

private theorem snoc_restricted (replies : Fin t → R) (r : R) (s : ℕ) (hs : s ≤ t) :
    (fun j : Fin s ↦ Fin.snoc (α := fun _ : Fin (t + 1) ↦ R) replies r ⟨j.val,by have := j.isLt; omega⟩) =
      (fun j : Fin s ↦ replies ⟨j.val,by have := j.isLt; omega⟩) := by
  funext j
  let i : Fin t := ⟨j.val,lt_of_lt_of_le j.isLt hs⟩
  change Fin.snoc (α := fun _ : Fin (t + 1) ↦ R) replies r i.castSucc = replies i
  exact Fin.snoc_castSucc (α := fun _ : Fin (t + 1) ↦ R) r replies i

theorem PrefixConsistent.snoc (P : Fixed Q R X Ω T) (A : Q → R) (seed : Ω)
    (t : ℕ) (ht : t < T) (replies : Fin t → R) (hprev : PrefixConsistent P A seed t replies) :
    PrefixConsistent P A seed (t + 1) (Fin.snoc replies (A (P.ask ⟨t,ht⟩ seed replies))) := by
  intro i
  refine Fin.lastCases ?_ (fun j ↦ ?_) i
  · intro hi
    simp only [Fin.val_last,Fin.snoc_last]
    rw [snoc_restricted replies _ t le_rfl]
  · intro hi
    simp only [Fin.val_castSucc,Fin.snoc_castSucc]
    rw [snoc_restricted replies _ j.val j.isLt.le]
    exact hprev j hi

theorem evalFrom_recordReplies_consistent (P : Fixed Q R X Ω T) (A : Q → R) (seed : Ω)
    (k t : ℕ) (ht : t + k = T) (replies : Fin t → R) (hprev : PrefixConsistent P A seed t replies) :
    CacheConsistent P A seed (evalFrom (recordReplies P) A seed k t ht replies).2 := by
  induction k generalizing t with
  | zero =>
      have he : t = T := by omega
      subst t
      intro i
      exact hprev i i.isLt
  | succ k ih =>
      exact ih (t + 1) (by omega) _ (PrefixConsistent.snoc P A seed t (by omega) replies hprev)

theorem eval_recordReplies_consistent (P : Fixed Q R X Ω T) (A : Q → R) (seed : Ω) :
    CacheConsistent P A seed (eval (recordReplies P) A seed).2 :=
  evalFrom_recordReplies_consistent P A seed T 0 (by omega) Fin.elim0 (fun i ↦ Fin.elim0 i)

theorem evalFrom_recordReplies_fst (P : Fixed Q R X Ω T) (A : Q → R) (seed : Ω)
    (k t : ℕ) (ht : t + k = T) (replies : Fin t → R) :
    (evalFrom (recordReplies P) A seed k t ht replies).1 = evalFrom P A seed k t ht replies := by
  induction k generalizing t with
  | zero => rfl
  | succ k ih => exact ih (t + 1) _ _

theorem eval_recordReplies_fst (P : Fixed Q R X Ω T) (A : Q → R) (seed : Ω) :
    (eval (recordReplies P) A seed).1 = eval P A seed :=
  evalFrom_recordReplies_fst P A seed T 0 (by omega) Fin.elim0

theorem evalFrom_recordReplies_finish (P : Fixed Q R X Ω T) (A : Q → R) (seed : Ω)
    (k t : ℕ) (ht : t + k = T) (replies : Fin t → R) :
    (evalFrom (recordReplies P) A seed k t ht replies).1 =
      P.finish seed (evalFrom (recordReplies P) A seed k t ht replies).2 := by
  induction k generalizing t with
  | zero => rfl
  | succ k ih => exact ih (t + 1) _ _

theorem eval_recordReplies_finish (P : Fixed Q R X Ω T) (A : Q → R) (seed : Ω) :
    (eval (recordReplies P) A seed).1 = P.finish seed (eval (recordReplies P) A seed).2 :=
  evalFrom_recordReplies_finish P A seed T 0 (by omega) Fin.elim0

theorem evalFrom_eq_finish_of_cacheConsistent (P : Fixed Q R X Ω T) (A : Q → R) (seed : Ω)
    (cache : Fin T → R) (hc : CacheConsistent P A seed cache)
    (k t : ℕ) (ht : t + k = T) (replies : Fin t → R)
    (hprefix : ∀ i : Fin t, replies i = cache ⟨i.val,by have := i.isLt; omega⟩) :
    evalFrom P A seed k t ht replies = P.finish seed cache := by
  induction k generalizing t with
  | zero =>
      have he : t = T := by omega
      subst t
      change P.finish seed (fun i ↦ replies (Fin.cast ht.symm i)) = _
      congr 1
      funext i
      simpa only [Fin.cast_refl,Function.id_def] using hprefix i
  | succ k ih =>
      have hlt : t < T := by omega
      have hp : replies = cachePrefix cache ⟨t,hlt⟩ := funext hprefix
      have hcur : A (P.ask ⟨t,hlt⟩ seed replies) = cache ⟨t,hlt⟩ := by
        rw [hp]
        exact hc ⟨t,hlt⟩
      apply ih (t + 1) (by omega)
      intro i
      refine Fin.lastCases ?_ (fun j ↦ ?_) i
      · simpa only [Fin.snoc_last,Fin.val_last] using hcur
      · simpa only [Fin.snoc_castSucc,Fin.val_castSucc] using hprefix j

theorem CacheConsistent.finish_eq_eval (P : Fixed Q R X Ω T) (A : Q → R) (seed : Ω)
    (cache : Fin T → R) (hc : CacheConsistent P A seed cache) : P.finish seed cache = eval P A seed :=
  (evalFrom_eq_finish_of_cacheConsistent P A seed cache hc T 0 (by omega) Fin.elim0 (fun i ↦ Fin.elim0 i)).symm

theorem cacheConsistent_measurableSet [MeasurableEq R] (P : Fixed Q R X Ω T) (A : Θ → Q → R)
    (hA : Measurable (Function.uncurry A)) :
    MeasurableSet {a : Θ × (Ω × (Fin T → R)) | CacheConsistent P (A a.1) a.2.1 a.2.2} := by
  simp only [CacheConsistent,setOf_forall]
  apply MeasurableSet.iInter
  intro t
  have hq : Measurable (fun a : Θ × (Ω × (Fin T → R)) ↦ P.ask t a.2.1 (cachePrefix a.2.2 t)) := by
    have hp : Measurable (fun a : Θ × (Ω × (Fin T → R)) ↦ (a.2.1,cachePrefix a.2.2 t)) :=
      (measurable_fst.comp measurable_snd).prodMk (measurable_pi_iff.mpr (fun j ↦
        (measurable_pi_apply (⟨j.val,lt_trans j.isLt t.isLt⟩ : Fin T)).comp (measurable_snd.comp measurable_snd)))
    convert (P.ask_measurable t).comp hp using 1
    all_goals rfl
  exact measurableSet_eq_fun (hA.comp (measurable_fst.prodMk hq))
    ((measurable_pi_apply t).comp (measurable_snd.comp measurable_snd))

end NCConcave16991.OracleProgram
