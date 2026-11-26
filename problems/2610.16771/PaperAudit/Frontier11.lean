import Mathlib
import PaperAudit.Frontier10

open scoped Topology NNReal ENNReal BigOperators
set_option maxHeartbeats 10000000


section
-- Source component: BorelWarmDataSpaces.lean

open MeasureTheory
namespace FangqingBorelWarmData
noncomputable section

abbrev BAnswer (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  OriginalBorelWarmReplay.OriginalBetaATSTrial.Answer E
abbrev BTrial (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  OriginalBorelWarmReplay.OriginalBetaATSTrial.TrialResult E
abbrev BResult (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  OriginalBorelWarmReplay.OriginalCoupledBetaSearch.Result E

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [MeasurableSpace (E →L[ℝ] E)]

def answerCode (a : BAnswer E) : E × (E →L[ℝ] E) := (a.grad,a.hess)
instance answerMeasurableSpace : MeasurableSpace (BAnswer E) := MeasurableSpace.comap answerCode inferInstance

def answerEquiv : BAnswer E ≃ᵐ E × (E →L[ℝ] E) where
  toFun := answerCode
  invFun := fun p => ⟨p.1,p.2⟩
  left_inv := by intro a; cases a; rfl
  right_inv := by intro p; cases p; rfl
  measurable_toFun := comap_measurable answerCode
  measurable_invFun := measurable_comap_iff.mpr measurable_id

theorem answer_grad_measurable : Measurable (fun a : BAnswer E => a.grad) :=
  measurable_fst.comp answerEquiv.measurable

theorem answer_hess_measurable : Measurable (fun a : BAnswer E => a.hess) :=
  measurable_snd.comp answerEquiv.measurable

def trialCode : BTrial E → E ⊕ (E × BAnswer E)
  | .stop w => .inl w
  | .step d a => .inr (d,a)
instance trialMeasurableSpace : MeasurableSpace (BTrial E) := MeasurableSpace.comap trialCode inferInstance

def trialEquiv : BTrial E ≃ᵐ E ⊕ (E × BAnswer E) where
  toFun := trialCode
  invFun := fun q => match q with | .inl w => .stop w | .inr (d,a) => .step d a
  left_inv := by intro q; cases q <;> rfl
  right_inv := by intro q; cases q with | inl w => rfl | inr q => cases q; rfl
  measurable_toFun := comap_measurable trialCode
  measurable_invFun := by
    apply measurable_comap_iff.mpr
    convert measurable_id using 1
    funext q
    cases q with | inl w => rfl | inr q => cases q; rfl

def resultCode : BResult E → E ⊕ (ℝ × (E × BAnswer E))
  | .stop w => .inl w
  | .window b d a => .inr (b,d,a)
instance resultMeasurableSpace : MeasurableSpace (BResult E) := MeasurableSpace.comap resultCode inferInstance

def resultEquiv : BResult E ≃ᵐ E ⊕ (ℝ × (E × BAnswer E)) where
  toFun := resultCode
  invFun := fun q => match q with | .inl w => .stop w | .inr (b,d,a) => .window b d a
  left_inv := by intro q; cases q <;> rfl
  right_inv := by intro q; cases q with | inl w => rfl | inr q => rcases q with ⟨b,d,a⟩; rfl
  measurable_toFun := comap_measurable resultCode
  measurable_invFun := by
    apply measurable_comap_iff.mpr
    convert measurable_id using 1
    funext q
    cases q with | inl w => rfl | inr q => rcases q with ⟨b,d,a⟩; rfl

section Hysteresis
variable {R : Type*} [MeasurableSpace R]

abbrev BDecision (R : Type*) := OriginalBorelWarmReplay.FangqingHysteresis.Decision R
abbrev BSearchOutcome (R : Type*) := OriginalBorelWarmReplay.FangqingHysteresis.Outcome R

def decisionCode : BDecision R → R ⊕ Bool
  | .accept r => .inl r
  | .low => .inr false
  | .high => .inr true
instance decisionMeasurableSpace : MeasurableSpace (BDecision R) := MeasurableSpace.comap decisionCode inferInstance

def decisionEquiv : BDecision R ≃ᵐ R ⊕ Bool where
  toFun := decisionCode
  invFun := fun q => match q with | .inl r => .accept r | .inr false => .low | .inr true => .high
  left_inv := by intro q; cases q <;> rfl
  right_inv := by intro q; cases q with | inl r => rfl | inr b => cases b <;> rfl
  measurable_toFun := comap_measurable decisionCode
  measurable_invFun := by
    apply measurable_comap_iff.mpr
    convert measurable_id using 1
    funext q
    cases q with | inl r => rfl | inr b => cases b <;> rfl

def searchOutcomeCode : BSearchOutcome R → R ⊕ (ℝ × ℝ)
  | .found r => .inl r
  | .bracket l u => .inr (l,u)
instance searchOutcomeMeasurableSpace : MeasurableSpace (BSearchOutcome R) := MeasurableSpace.comap searchOutcomeCode inferInstance

def searchOutcomeEquiv : BSearchOutcome R ≃ᵐ R ⊕ (ℝ × ℝ) where
  toFun := searchOutcomeCode
  invFun := fun q => match q with | .inl r => .found r | .inr (l,u) => .bracket l u
  left_inv := by intro q; cases q <;> rfl
  right_inv := by intro q; cases q with | inl r => rfl | inr q => cases q; rfl
  measurable_toFun := comap_measurable searchOutcomeCode
  measurable_invFun := by
    apply measurable_comap_iff.mpr
    convert measurable_id using 1
    funext q
    cases q with | inl r => rfl | inr q => cases q; rfl

end Hysteresis

abbrev BState (E : Type*) := OriginalBorelWarmReplay.OriginalRobustTrajectory.State E
abbrev BOutcome (E : Type*) := OriginalBorelWarmReplay.OriginalRobustTrajectory.Outcome E

def stateCode (s : BState E) : ℝ × (E × E) := (s.weight,s.x,s.y)
instance stateMeasurableSpace : MeasurableSpace (BState E) := MeasurableSpace.comap stateCode inferInstance

def stateEquiv : BState E ≃ᵐ ℝ × (E × E) where
  toFun := stateCode
  invFun := fun q => ⟨q.1,q.2.1,q.2.2⟩
  left_inv := by intro q; cases q; rfl
  right_inv := by intro q; rcases q with ⟨a,x,y⟩; rfl
  measurable_toFun := comap_measurable stateCode
  measurable_invFun := measurable_comap_iff.mpr measurable_id

def outcomeCode : BOutcome E → E ⊕ (BState E ⊕ Unit)
  | .stop w => .inl w
  | .finished s => .inr (.inl s)
  | .failure => .inr (.inr ())
instance outcomeMeasurableSpace : MeasurableSpace (BOutcome E) := MeasurableSpace.comap outcomeCode inferInstance

def outcomeEquiv : BOutcome E ≃ᵐ E ⊕ (BState E ⊕ Unit) where
  toFun := outcomeCode
  invFun := fun q => match q with | .inl w => .stop w | .inr (.inl s) => .finished s | .inr (.inr _) => .failure
  left_inv := by intro q; cases q <;> rfl
  right_inv := by
    intro q
    cases q with
    | inl w => rfl
    | inr q => cases q with | inl s => rfl | inr u => cases u; rfl
  measurable_toFun := comap_measurable outcomeCode
  measurable_invFun := by
    apply measurable_comap_iff.mpr
    convert measurable_id using 1
    funext q
    cases q with
    | inl w => rfl
    | inr q => cases q with | inl s => rfl | inr u => cases u; rfl

end
end FangqingBorelWarmData
end

section
-- Source component: BorelGetterProgramFamily.lean

open MeasureTheory Function

namespace FangqingBorelGetterProgramFamily
open OriginalBetaATSTrial FangqingGetterComposition
noncomputable section
set_option maxHeartbeats 4500000

variable {X Y Q A R S : Type*}

def streamDrop (n : ℕ) (a : ℕ → A) : ℕ → A := fun j => a (n+j)

def streamRun : GetterProgram Q A R → (ℕ → A) → R × List Q
  | .pure r, _ => (r,[])
  | .ask q k, a => let r := streamRun (k (a 0)) (streamDrop 1 a); (r.1,q::r.2)

theorem streamDrop_add (n m : ℕ) (a : ℕ → A) :
    streamDrop n (streamDrop m a) = streamDrop (m+n) a := by
  funext j
  simp only [streamDrop,Nat.add_assoc]

theorem stream_run_bind (p : GetterProgram Q A R) (k : R → GetterProgram Q A S) (a : ℕ → A) :
    streamRun (FangqingGetterComposition.bind p k) a =
      let r := streamRun p a
      let s := streamRun (k r.1) (streamDrop r.2.length a)
      (s.1,r.2++s.2) := by
  induction p generalizing a with
  | pure r =>
      have hd : streamDrop 0 a = a := by funext j; simp only [streamDrop,Nat.zero_add]
      simp only [FangqingGetterComposition.bind,streamRun,List.length_nil,List.nil_append,hd]
  | ask q cont ih =>
      simp only [FangqingGetterComposition.bind,streamRun,ih,List.length_cons,List.cons_append,streamDrop_add,Nat.add_comm]

theorem measurable_nat_select [MeasurableSpace X] [MeasurableSpace R]
    (f : ℕ → X → R) (hf : ∀ n, Measurable (f n))
    (n : X → ℕ) (hn : Measurable n) : Measurable (fun x => f (n x) x) := by
  have h : Measurable (fun x : X × ℕ => f x.2 x.1) :=
    measurable_from_prod_countable_left (fun j => hf j)
  simpa only [Function.comp_def,id_eq] using h.comp (measurable_id.prodMk hn)

theorem stream_drop_measurable [MeasurableSpace A] :
    Measurable (fun x : ℕ × (ℕ → A) => streamDrop x.1 x.2) := by
  apply measurable_pi_lambda
  intro j
  exact measurable_nat_select (fun n (x : ℕ × (ℕ → A)) => x.2 (n+j))
    (fun n => (measurable_pi_apply (n+j)).comp measurable_snd) Prod.fst measurable_fst

/-- Natural finite-transcript sigma structure: result, charged count and every
actual request coordinate are measurable on the whole answer-stream space.
No measurability is presumed of an arbitrary continuation or choice function. -/
structure BorelFamily [MeasurableSpace X] [MeasurableSpace Q] [MeasurableSpace A]
    [MeasurableSpace R] (p : X → GetterProgram Q A R) : Prop where
  result : Measurable (fun x : X × (ℕ → A) => (streamRun (p x.1) x.2).1)
  count : Measurable (fun x : X × (ℕ → A) => (streamRun (p x.1) x.2).2.length)
  request : ∀ (q0 : Q) (n : ℕ), Measurable (fun x : X × (ℕ → A) => (streamRun (p x.1) x.2).2.getD n q0)

section Closures
variable [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Q]
  [MeasurableSpace A] [MeasurableSpace R] [MeasurableSpace S]

theorem pure_family (r : X → R) (hr : Measurable r) :
    BorelFamily (Q := Q) (A := A) (fun x => .pure (r x)) := by
  refine ⟨hr.comp measurable_fst,measurable_const,?_⟩
  intro q0 n
  exact measurable_const

theorem precomp_family (p : X → GetterProgram Q A R) (hp : BorelFamily p)
    (f : Y → X) (hf : Measurable f) : BorelFamily (fun y => p (f y)) := by
  have hi : Measurable (fun x : Y × (ℕ → A) => (f x.1,x.2)) :=
    (hf.comp measurable_fst).prodMk measurable_snd
  exact ⟨hp.result.comp hi,hp.count.comp hi,fun q0 n => (hp.request q0 n).comp hi⟩

theorem ask_family (q : X → Q) (hq : Measurable q)
    (k : X × A → GetterProgram Q A R) (hk : BorelFamily k) :
    BorelFamily (fun x => .ask (q x) (fun a => k (x,a))) := by
  have hi : Measurable (fun x : X × (ℕ → A) => ((x.1,x.2 0),streamDrop 1 x.2)) :=
    (measurable_fst.prodMk ((measurable_pi_apply 0).comp measurable_snd)).prodMk
      (stream_drop_measurable.comp (measurable_const.prodMk measurable_snd))
  refine ⟨hk.result.comp hi,?_,?_⟩
  · convert! (hk.count.comp hi).add (measurable_const (a := (1:ℕ))) using 1
  · intro q0 n
    cases n with
    | zero => exact hq.comp measurable_fst
    | succ n => simpa only [streamRun,List.getD_cons_succ,Function.comp_def] using (hk.request q0 n).comp hi

theorem ite_family (test : X → Prop) [DecidablePred test]
    (ht : MeasurableSet {x | test x}) (p q : X → GetterProgram Q A R)
    (hp : BorelFamily p) (hq : BorelFamily q) :
    BorelFamily (fun x => if test x then p x else q x) := by
  classical
  have ht' : MeasurableSet {x : X × (ℕ → A) | test x.1} := ht.preimage measurable_fst
  refine ⟨?_,?_,?_⟩
  · convert! hp.result.ite ht' hq.result using 1
    funext x
    split_ifs <;> rfl
    exact fun x => Classical.propDecidable (test x.1)
  · convert! hp.count.ite ht' hq.count using 1
    funext x
    split_ifs <;> rfl
    exact fun x => Classical.propDecidable (test x.1)
  · intro q0 n
    convert! (hp.request q0 n).ite ht' (hq.request q0 n) using 1
    funext x
    split_ifs <;> rfl
    exact fun x => Classical.propDecidable (test x.1)

theorem nat_select_family (p : ℕ → X → GetterProgram Q A R) (hp : ∀ n, BorelFamily (p n))
    (n : X → ℕ) (hn : Measurable n) : BorelFamily (fun x => p (n x) x) := by
  exact ⟨measurable_nat_select _ (fun j => (hp j).result) (fun x : X × (ℕ → A) => n x.1) (hn.comp measurable_fst),
    measurable_nat_select _ (fun j => (hp j).count) (fun x : X × (ℕ → A) => n x.1) (hn.comp measurable_fst),
    fun q0 i => measurable_nat_select _ (fun j => (hp j).request q0 i) (fun x : X × (ℕ → A) => n x.1) (hn.comp measurable_fst)⟩

theorem bind_family (p : X → GetterProgram Q A R) (hp : BorelFamily p)
    (k : X × R → GetterProgram Q A S) (hk : BorelFamily k) :
    BorelFamily (fun x => FangqingGetterComposition.bind (p x) (fun r => k (x,r))) := by
  have hd : Measurable (fun x : X × (ℕ → A) => streamDrop (streamRun (p x.1) x.2).2.length x.2) :=
    stream_drop_measurable.comp (hp.count.prodMk measurable_snd)
  have hi : Measurable (fun x : X × (ℕ → A) =>
      ((x.1,(streamRun (p x.1) x.2).1),streamDrop (streamRun (p x.1) x.2).2.length x.2)) :=
    (measurable_fst.prodMk hp.result).prodMk hd
  refine ⟨?_,?_,?_⟩
  · simpa only [stream_run_bind,Function.comp_def] using hk.result.comp hi
  · convert! hp.count.add (hk.count.comp hi) using 1
    funext x
    simp only [stream_run_bind,List.length_append,Pi.add_apply,Function.comp_def]
  · intro q0 n
    have hleft := hp.request q0 n
    have hright : Measurable (fun x : X × (ℕ → A) =>
        (streamRun (k (x.1,(streamRun (p x.1) x.2).1))
          (streamDrop (streamRun (p x.1) x.2).2.length x.2)).2.getD (n-(streamRun (p x.1) x.2).2.length) q0) :=
      measurable_nat_select _ (fun j => (hk.request q0 j).comp hi) _ (measurable_const.sub hp.count)
    have htest : MeasurableSet {x : X × (ℕ → A) | n < (streamRun (p x.1) x.2).2.length} :=
      measurableSet_lt measurable_const hp.count
    convert! hleft.ite htest hright using 1
    · funext x
      rw [stream_run_bind]
      simp only [List.getD,List.getElem?_append]
      split_ifs <;> rfl
    · exact fun x => inferInstance

theorem map_family (p : X → GetterProgram Q A R) (hp : BorelFamily p)
    (f : X × R → S) (hf : Measurable f) :
    BorelFamily (fun x => FangqingGetterComposition.map (fun r => f (x,r)) (p x)) :=
  bind_family p hp (fun xr => .pure (f xr)) (pure_family f hf)

end Closures
end
end FangqingBorelGetterProgramFamily

namespace FangqingBorelGetterProgramFamily
open OriginalBetaATSTrial
noncomputable section
set_option maxHeartbeats 4500000
variable {X Q A R : Type*}

/-- A request at index n and stopping through n are determined by the first n
answers. If stopped, the entire finite result/transcript is already determined. -/
theorem prefix_causality (p : GetterProgram Q A R) (a b : ℕ → A) (n : ℕ)
    (hab : ∀ j < n, a j = b j) :
    (streamRun p a).2.take (n+1) = (streamRun p b).2.take (n+1) ∧
      ((streamRun p a).2.length ≤ n ↔ (streamRun p b).2.length ≤ n) ∧
      ((streamRun p a).2.length ≤ n → streamRun p a = streamRun p b) := by
  induction p generalizing a b n with
  | pure r => exact ⟨rfl,Iff.rfl,fun _ => rfl⟩
  | ask q cont ih =>
      cases n with
      | zero =>
          refine ⟨?_,?_,?_⟩
          · simp only [streamRun,List.take_succ_cons,List.take_zero]
          · constructor <;> intro h <;> simp only [streamRun,List.length_cons] at h <;> omega
          · intro h
            simp only [streamRun,List.length_cons] at h
            omega
      | succ n =>
          have h0 : a 0 = b 0 := hab 0 (by omega)
          have hi := ih (a 0) (streamDrop 1 a) (streamDrop 1 b) n (by
            intro j hj
            exact hab (1+j) (by omega))
          refine ⟨?_,?_,?_⟩
          · simpa only [streamRun,← h0,List.take_succ_cons] using congrArg (List.cons q) hi.1
          · simpa only [streamRun,← h0,List.length_cons,Nat.add_le_add_iff_right] using hi.2.1
          · intro hh
            have hc : (streamRun (cont (a 0)) (streamDrop 1 a)).2.length ≤ n := by
              simpa only [streamRun,List.length_cons,Nat.add_le_add_iff_right] using hh
            simp only [streamRun,← h0,hi.2.2 hc]

def streamPad (n : ℕ) (a0 : A) (a : ℕ → A) : ℕ → A := fun j => if j<n then a j else a0

theorem padding_preserves_actual_request_and_stop
    (p : GetterProgram Q A R) (a : ℕ → A) (a0 : A) (q0 : Q) (n : ℕ) :
    (streamRun p a).2.getD n q0 = (streamRun p (streamPad n a0 a)).2.getD n q0 ∧
    ((streamRun p a).2.length ≤ n ↔ (streamRun p (streamPad n a0 a)).2.length ≤ n) ∧
    ((streamRun p a).2.length ≤ n → streamRun p a = streamRun p (streamPad n a0 a)) := by
  have h := prefix_causality p a (streamPad n a0 a) n (by
    intro j hj
    simp only [streamPad,if_pos hj])
  refine ⟨?_,h.2⟩
  have he := congrArg (fun l : List Q => l[n]?) h.1
  have he' : (streamRun p a).2[n]? = (streamRun p (streamPad n a0 a)).2[n]? := by
    simpa only [List.getElem?_take,Nat.lt_succ_self,if_true] using he
  simpa only [List.getD_eq_getElem?_getD] using congrArg (fun o : Option Q => o.getD q0) he'

section Measurable
variable [MeasurableSpace X] [MeasurableSpace Q] [MeasurableSpace A] [MeasurableSpace R]

theorem stream_pad_measurable (n : ℕ) (a0 : A) : Measurable (streamPad n a0) := by
  apply measurable_pi_lambda
  intro j
  by_cases hj : j<n
  · simpa only [streamPad,if_pos hj] using measurable_pi_apply j
  · simpa only [streamPad,if_neg hj] using (measurable_const (a := a0) : Measurable (fun _ : ℕ → A => a0))

theorem actual_next_query_measurable (p : X → GetterProgram Q A R) (hp : BorelFamily p)
    (n : ℕ) (a0 : A) (q0 : Q) :
    Measurable (fun x : X × (ℕ → A) => (streamRun (p x.1) (streamPad n a0 x.2)).2.getD n q0) :=
  (hp.request q0 n).comp (measurable_fst.prodMk ((stream_pad_measurable n a0).comp measurable_snd))

theorem actual_stop_measurable (p : X → GetterProgram Q A R) (hp : BorelFamily p)
    (n : ℕ) (a0 : A) :
    MeasurableSet {x : X × (ℕ → A) | (streamRun (p x.1) (streamPad n a0 x.2)).2.length ≤ n} :=
  measurableSet_le (hp.count.comp (measurable_fst.prodMk ((stream_pad_measurable n a0).comp measurable_snd))) measurable_const

theorem actual_stopped_output_measurable (p : X → GetterProgram Q A R) (hp : BorelFamily p)
    (n : ℕ) (a0 : A) :
    Measurable (fun x : X × (ℕ → A) => (streamRun (p x.1) (streamPad n a0 x.2)).1) :=
  hp.result.comp (measurable_fst.prodMk ((stream_pad_measurable n a0).comp measurable_snd))

end Measurable
end
end FangqingBorelGetterProgramFamily
end

section
-- Source component: BorelWarmProgramBridges.lean

namespace FangqingBorelWarmProgramBridges
open OriginalBetaATSTrial
noncomputable section

variable {Q A R S BQ BA : Type*}

theorem bind_eq_original (p : GetterProgram Q A R) (k : R → GetterProgram Q A S) :
    OriginalBorelWarmReplay.FangqingGetterComposition.bind p k = FangqingGetterComposition.bind p k := by
  induction p with
  | pure r => rfl
  | ask q cont ih =>
    simp only [OriginalBorelWarmReplay.FangqingGetterComposition.bind,FangqingGetterComposition.bind]
    congr 1
    funext a
    exact ih a

theorem map_eq_original (f : R → S) (p : GetterProgram Q A R) :
    OriginalBorelWarmReplay.FangqingGetterComposition.map f p = FangqingGetterComposition.map f p := by
  simp only [OriginalBorelWarmReplay.FangqingGetterComposition.map,FangqingGetterComposition.map,bind_eq_original]

theorem trace_eq_original (getter : Q → A) (p : GetterProgram Q A R) :
    OriginalBorelWarmReplay.FangqingGetterComposition.trace getter p = FangqingGetterComposition.trace getter p := by
  induction p with
  | pure r => rfl
  | ask q cont ih =>
    simp only [OriginalBorelWarmReplay.FangqingGetterComposition.trace,FangqingGetterComposition.trace,ih]

theorem primitive_lower_eq_original (oracle : Q → GetterProgram BQ BA A) (p : GetterProgram Q A R) :
    OriginalBorelWarmReplay.FangqingGetterComposition.primitiveLower oracle p =
      FangqingGetterComposition.primitiveLower oracle p := by
  induction p with
  | pure r => rfl
  | ask q cont ih =>
    simp only [OriginalBorelWarmReplay.FangqingGetterComposition.primitiveLower,
      FangqingGetterComposition.primitiveLower,bind_eq_original]
    congr 1
    funext a
    exact ih a

/-- Every actual base query is exactly the concatenation of the actual inner
oracle-program traces, in the order of the actual outer requests. No query
bound or Borel conclusion is assumed by this execution identity. -/
theorem actual_primitive_trace_flatten (base : BQ → BA)
    (oracle : Q → GetterProgram BQ BA A) (p : GetterProgram Q A R) :
    OriginalBorelWarmReplay.FangqingGetterComposition.trace base
      (OriginalBorelWarmReplay.FangqingGetterComposition.primitiveLower oracle p) =
      (OriginalBorelWarmReplay.FangqingGetterComposition.trace
        (OriginalBorelWarmReplay.FangqingGetterComposition.implementedGetter base oracle) p).flatMap
          (fun q => OriginalBorelWarmReplay.FangqingGetterComposition.trace base (oracle q)) := by
  induction p with
  | pure r => rfl
  | ask q cont ih =>
    simp only [OriginalBorelWarmReplay.FangqingGetterComposition.primitiveLower,
      OriginalBorelWarmReplay.OriginalCoupledQueryGeometry.trace_bind_actual,
      OriginalBorelWarmReplay.FangqingGetterComposition.trace,List.flatMap_cons]
    exact congrArg (fun l => OriginalBorelWarmReplay.FangqingGetterComposition.trace base (oracle q) ++ l)
      (ih (OriginalBorelWarmReplay.FangqingGetterComposition.implementedGetter base oracle q))

end
end FangqingBorelWarmProgramBridges
end

section
-- Source component: BorelWarmATSFamily.lean

open MeasureTheory
namespace FangqingBorelWarmATS
open OriginalBetaATSTrial FangqingBorelGetterProgramFamily FangqingBorelWarmData
noncomputable section
set_option maxHeartbeats 4000000

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]
local instance : MeasurableSpace E := borel E
local instance : BorelSpace E := ⟨rfl⟩
local instance : MeasurableSpace (E →L[ℝ] E) := borel (E →L[ℝ] E)
local instance : BorelSpace (E →L[ℝ] E) := ⟨rfl⟩

theorem trial_stop_measurable : Measurable (fun w : E => (.stop w : BTrial E)) :=
  trialEquiv.symm.measurable.comp measurable_inl

theorem trial_step_measurable : Measurable (fun p : E × BAnswer E => (.step p.1 p.2 : BTrial E)) :=
  trialEquiv.symm.measurable.comp measurable_inr

abbrev TrialInput (E : Type*) := E × (ℝ × (ℝ × (ℝ × ℝ)))

/-- Every query, branch and output of the executed Taylor trial is Borel on
ALL answers, including inaccurate/noncoercive Hessians and nonpositive lambda.
The total selector is used in this new executed program. -/
theorem actual_trial_program_family (M : ℝ) :
    BorelFamily (fun p : TrialInput E =>
      OriginalBorelWarmReplay.OriginalBetaATSTrial.trialProgram M p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2 p.1) := by
  classical
  let U := TrialInput E × BAnswer E
  let V := U × BAnswer E
  let d : U → E := fun u => OriginalBorelTaylorProx.totalStep u.2.grad u.2.hess M u.1.2.1
  have hz : Measurable (fun p : TrialInput E => p.1) := measurable_fst
  have hl : Measurable (fun p : TrialInput E => p.2.1) := measurable_snd.fst
  have hdelta : Measurable (fun p : TrialInput E => p.2.2.1) := measurable_snd.snd.fst
  have hrho : Measurable (fun p : TrialInput E => p.2.2.2.1) := measurable_snd.snd.snd.fst
  have hdeltaY : Measurable (fun p : TrialInput E => p.2.2.2.2) := measurable_snd.snd.snd.snd
  have hga : Measurable (fun u : U => u.2.grad) := answer_grad_measurable.comp measurable_snd
  have hHa : Measurable (fun u : U => u.2.hess) := answer_hess_measurable.comp measurable_snd
  have hd : Measurable d := (OriginalBorelTaylorProx.total_step_measurable M).comp
    ((hga.prodMk hHa).prodMk (hl.comp measurable_fst))
  have hnew : Measurable (fun u : U => u.1.1+d u) := (hz.comp measurable_fst).add hd
  have htest : MeasurableSet {u : U | ‖u.2.grad‖+u.1.2.2.1 ≤ u.1.2.2.2.1} :=
    measurableSet_le (hga.norm.add (hdelta.comp measurable_fst)) (hrho.comp measurable_fst)
  have htestY : MeasurableSet {v : V | ‖v.2.grad‖+v.1.1.2.2.2.2 ≤ v.1.1.2.2.2.1} :=
    measurableSet_le ((answer_grad_measurable.comp measurable_snd).norm.add
      (hdeltaY.comp measurable_fst.fst)) (hrho.comp measurable_fst.fst)
  have hstop : BorelFamily (fun u : U => (.pure (.stop u.1.1) : GetterProgram (E×ℝ) (BAnswer E) (BTrial E))) :=
    pure_family _ (trial_stop_measurable.comp (hz.comp measurable_fst))
  have hstopY : BorelFamily (fun v : V => (.pure (.stop (v.1.1.1+d v.1)) :
      GetterProgram (E×ℝ) (BAnswer E) (BTrial E))) :=
    pure_family _ (trial_stop_measurable.comp (hnew.comp measurable_fst))
  have hstepY : BorelFamily (fun v : V => (.pure (.step (d v.1) v.2) :
      GetterProgram (E×ℝ) (BAnswer E) (BTrial E))) :=
    pure_family _ (trial_step_measurable.comp ((hd.comp measurable_fst).prodMk measurable_snd))
  have hfinish : BorelFamily (fun v : V =>
      if ‖v.2.grad‖+v.1.1.2.2.2.2 ≤ v.1.1.2.2.2.1 then
        (.pure (.stop (v.1.1.1+d v.1)) : GetterProgram (E×ℝ) (BAnswer E) (BTrial E))
      else .pure (.step (d v.1) v.2)) :=
    ite_family _ htestY _ _ hstopY hstepY
  have hsecond : BorelFamily (fun u : U =>
      .ask (u.1.1+d u,u.1.2.2.2.2) (fun aY : BAnswer E =>
        if ‖aY.grad‖+u.1.2.2.2.2 ≤ u.1.2.2.2.1 then
          (.pure (.stop (u.1.1+d u)) : GetterProgram (E×ℝ) (BAnswer E) (BTrial E))
        else .pure (.step (d u) aY))) :=
    ask_family _ (hnew.prodMk (hdeltaY.comp measurable_fst)) _ hfinish
  have hcont : BorelFamily (fun u : U =>
      if ‖u.2.grad‖+u.1.2.2.1 ≤ u.1.2.2.2.1 then
        (.pure (.stop u.1.1) : GetterProgram (E×ℝ) (BAnswer E) (BTrial E))
      else .ask (u.1.1+d u,u.1.2.2.2.2) (fun aY : BAnswer E =>
        if ‖aY.grad‖+u.1.2.2.2.2 ≤ u.1.2.2.2.1 then
          .pure (.stop (u.1.1+d u)) else .pure (.step (d u) aY))) :=
    ite_family _ htest _ _ hstop hsecond
  have hall := ask_family (fun p : TrialInput E => (p.1,p.2.2.1)) (hz.prodMk hdelta) _ hcont
  simpa only [OriginalBorelWarmReplay.OriginalBetaATSTrial.trialProgram,
    OriginalBorelWarmReplay.OriginalTaylorProxStability.exactStep,d] using hall

end
end FangqingBorelWarmATS
end

section
-- Source component: BorelWarmCases.lean

open MeasureTheory
namespace FangqingBorelWarmCases
open OriginalBetaATSTrial FangqingBorelGetterProgramFamily FangqingBorelWarmData
noncomputable section

variable {X Y Q A R S T : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [MeasurableSpace Q] [MeasurableSpace A] [MeasurableSpace R]
  [MeasurableSpace S] [MeasurableSpace T]

theorem measurable_sum_stream (f : X × S → T) (g : Y × S → T)
    (hf : Measurable f) (hg : Measurable g) :
    Measurable (fun z : (X ⊕ Y) × S => match z.1 with | .inl x => f (x,z.2) | .inr y => g (y,z.2)) := by
  have hsum : Measurable (Sum.elim f g) := measurable_fun_sum (f := Sum.elim f g) hf hg
  convert hsum.comp (MeasurableEquiv.sumProdDistrib X Y S).measurable using 1
  funext z
  rcases z with ⟨x|y,s⟩ <;> rfl

theorem sum_family (p : X → GetterProgram Q A R) (q : Y → GetterProgram Q A R)
    (hp : BorelFamily p) (hq : BorelFamily q) :
    BorelFamily (Sum.elim p q) := by
  refine ⟨?_,?_,?_⟩
  · convert measurable_sum_stream _ _ hp.result hq.result using 1
    funext z
    cases z.1 <;> rfl
  · convert measurable_sum_stream _ _ hp.count hq.count using 1
    funext z
    cases z.1 <;> rfl
  · intro q0 n
    convert measurable_sum_stream _ _ (hp.request q0 n) (hq.request q0 n) using 1
    funext z
    cases z.1 <;> rfl

/-- Borel branching on the actual accept/low/high search response, with its
natural payload-plus-Bool encoding. -/
theorem decision_case_family
    (accepted : X × S → GetterProgram Q A R)
    (low high : X → GetterProgram Q A R)
    (ha : BorelFamily accepted) (hl : BorelFamily low) (hh : BorelFamily high) :
    BorelFamily (fun z : X × BDecision S => match z.2 with
      | .accept value => accepted (z.1,value)
      | .low => low z.1
      | .high => high z.1) := by
  classical
  have hb : BorelFamily (fun z : X × Bool =>
      if z.2 = true then high z.1 else low z.1) :=
    ite_family _ (measurableSet_eq_fun measurable_snd measurable_const) _ _
      (precomp_family _ hh Prod.fst measurable_fst) (precomp_family _ hl Prod.fst measurable_fst)
  have hs := sum_family accepted
    (fun z : X × Bool => if z.2 = true then high z.1 else low z.1) ha hb
  have hcode : Measurable (fun z : X × BDecision S =>
      (MeasurableEquiv.prodSumDistrib X S Bool) (z.1,decisionEquiv z.2)) :=
    (MeasurableEquiv.prodSumDistrib X S Bool).measurable.comp
      (measurable_fst.prodMk (decisionEquiv.measurable.comp measurable_snd))
  have hp := precomp_family _ hs _ hcode
  convert hp using 1
  funext z
  rcases z with ⟨x,ans⟩
  cases ans with
  | accept value => rfl
  | low =>
    change low x = (if (false:Bool)=true then high x else low x)
    simp
  | high =>
    change high x = (if (true:Bool)=true then high x else low x)
    simp

end
end FangqingBorelWarmCases
end

section
-- Source component: BorelWarmEncodedCases.lean

open MeasureTheory
namespace FangqingBorelWarmEncodedCases
open OriginalBetaATSTrial FangqingBorelGetterProgramFamily FangqingBorelWarmCases
noncomputable section

variable {X D B C Q A R : Type*} [MeasurableSpace X] [MeasurableSpace D]
  [MeasurableSpace B] [MeasurableSpace C] [MeasurableSpace Q] [MeasurableSpace A] [MeasurableSpace R]

theorem encoded_case_family (e : D ≃ᵐ B ⊕ C)
    (p : X × B → GetterProgram Q A R) (q : X × C → GetterProgram Q A R)
    (hp : BorelFamily p) (hq : BorelFamily q) :
    BorelFamily (fun z : X × D => Sum.elim p q
      ((MeasurableEquiv.prodSumDistrib X B C) (z.1,e z.2))) :=
  precomp_family _ (sum_family p q hp hq) _
    ((MeasurableEquiv.prodSumDistrib X B C).measurable.comp
      (measurable_fst.prodMk (e.measurable.comp measurable_snd)))

end
end FangqingBorelWarmEncodedCases
end

section
-- Source component: BorelWarmScalarMaps.lean

open MeasureTheory
namespace FangqingBorelWarmScalars
open OriginalBorelWarmReplay.OriginalCoupledBetaSearch
noncomputable section
set_option maxHeartbeats 4000000

def withWeight (c : Settings) (a : ℝ) : Settings := {c with A:=a}

theorem lower_measurable (c : Settings) :
    Measurable (fun p : ℝ×ℝ => lower (withWeight c p.1) p.2) := by
  unfold lower OriginalBorelWarmReplay.OriginalBetaSearchEndpoints.betaLow
    OriginalBorelWarmReplay.OriginalBetaSearchEndpoints.lambdaLow withWeight
  fun_prop

theorem upper_measurable (c : Settings) :
    Measurable (fun a : ℝ => upper (withWeight c a)) := by
  unfold upper margin OriginalBorelWarmReplay.OriginalBetaSearchEndpoints.highMargin
    OriginalBorelWarmReplay.OriginalBetaSearchEndpoints.lambdaHigh withWeight
  fun_prop

theorem tolerance_measurable (c : Settings) :
    Measurable (fun p : ℝ×ℝ => tolerance (withWeight c p.1) p.2) := by
  unfold tolerance lambdaMin lambdaMax lower margin
    OriginalBorelWarmReplay.OriginalBetaSearchEndpoints.betaLow
    OriginalBorelWarmReplay.OriginalBetaSearchEndpoints.highMargin
    OriginalBorelWarmReplay.OriginalBetaSearchEndpoints.lambdaLow
    OriginalBorelWarmReplay.OriginalBetaSearchEndpoints.lambdaHigh
    OriginalBorelWarmReplay.OriginalBetaATSUniform.uniformTolerance
    OriginalBorelWarmReplay.OriginalBetaATSUniform.uniformStepFloor CertifiedATS.stepFloor withWeight
  fun_prop

theorem lambda_max_measurable (c : Settings) :
    Measurable (fun a : ℝ => lambdaMax (withWeight c a)) := by
  unfold lambdaMax margin OriginalBorelWarmReplay.OriginalBetaSearchEndpoints.highMargin
    OriginalBorelWarmReplay.OriginalBetaSearchEndpoints.lambdaHigh withWeight
  fun_prop

theorem output_precision_measurable (c : Settings) (sigma0 : ℝ) :
    Measurable (fun a : ℝ => OriginalBorelWarmReplay.OriginalCertifiedCoupledAHPE.outputQueryPrecision
      (withWeight c a) sigma0) := by
  unfold OriginalBorelWarmReplay.OriginalCertifiedCoupledAHPE.outputQueryPrecision
    OriginalBorelWarmReplay.OriginalCertifiedCoupledAHPE.outputTolerance
    OriginalBorelWarmReplay.RobustAHPE.uniformOutputGradientTolerance
    OriginalBorelWarmReplay.RobustAHPE.chosenSlack lambdaMax margin
    OriginalBorelWarmReplay.OriginalBetaSearchEndpoints.highMargin
    OriginalBorelWarmReplay.OriginalBetaSearchEndpoints.lambdaHigh withWeight
  fun_prop

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]
local instance : MeasurableSpace E := borel E
local instance : BorelSpace E := ⟨rfl⟩

abbrev NumericInput (E : Type*) := (ℝ×ℝ) × (E×E)

theorem modulus_measurable (c : Settings) :
    Measurable (fun p : NumericInput E => modulus (withWeight c p.1.1) p.1.2 p.2.1 p.2.2) := by
  unfold modulus OriginalBorelWarmReplay.OriginalBetaCurveBounds.sizeModulus
    OriginalBorelWarmReplay.OriginalBetaCurveBounds.stepModulus
    OriginalBorelWarmReplay.OriginalBetaCurveBounds.inverseLambdaModulus
    lower margin OriginalBorelWarmReplay.OriginalBetaSearchEndpoints.betaLow
    OriginalBorelWarmReplay.OriginalBetaSearchEndpoints.highMargin
    OriginalBorelWarmReplay.OriginalBetaSearchEndpoints.lambdaLow
    OriginalBorelWarmReplay.OriginalBetaSearchEndpoints.lambdaHigh withWeight
  fun_prop

theorem fuel_measurable (c : Settings) :
    Measurable (fun p : NumericInput E => fuel (withWeight c p.1.1) p.1.2 p.2.1 p.2.2) := by
  unfold fuel OriginalBorelWarmReplay.FangqingHysteresis.searchFuel
    OriginalBorelWarmReplay.FangqingHysteresis.halvingCount Real.logb
  apply Nat.measurable_ceil.comp
  apply Measurable.div _ measurable_const
  apply Real.measurable_log.comp
  apply Measurable.max measurable_const
  have hm := modulus_measurable (E:=E) c
  have hu := (upper_measurable c).comp (measurable_fst.fst :
    Measurable (fun p : NumericInput E => p.1.1))
  have hl := (lower_measurable c).comp (measurable_fst :
    Measurable (fun p : NumericInput E => p.1))
  have hgap : Measurable (fun p : NumericInput E =>
      (thresholdHigh (withWeight c p.1.1)-thresholdLow (withWeight c p.1.1))/2) := by
    unfold thresholdHigh thresholdLow withWeight
    fun_prop
  exact (hm.mul (hu.sub hl)).div hgap

end
end FangqingBorelWarmScalars
end

section
-- Source component: BorelWarmTrialClassification.lean

open MeasureTheory
namespace FangqingBorelWarmClassification
open OriginalBetaATSTrial FangqingBorelGetterProgramFamily FangqingBorelWarmData
  FangqingBorelWarmScalars FangqingBorelWarmProgramBridges
open OriginalBorelWarmReplay.OriginalCoupledBetaSearch
noncomputable section
set_option maxHeartbeats 5000000

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]
local instance : MeasurableSpace E := borel E
local instance : BorelSpace E := ⟨rfl⟩
local instance : MeasurableSpace (E →L[ℝ] E) := borel (E →L[ℝ] E)
local instance : BorelSpace (E →L[ℝ] E) := ⟨rfl⟩

theorem classify_measurable (c : Settings) :
    Measurable (fun z : (ℝ×ℝ) × BTrial E => classifyResult (withWeight c z.1.1) z.1.2 z.2) := by
  classical
  let f : (ℝ×ℝ) × E → BDecision (BResult E) := fun z => .accept (.stop z.2)
  let g : (ℝ×ℝ) × (E × BAnswer E) → BDecision (BResult E) := fun z =>
    let t := OriginalCoupledBetaAlgebra.lambda z.1.1 z.1.2 * ‖z.2.1‖
    if c.sigmaLow/c.M ≤ t ∧ t ≤ c.sigmaUp/c.M then .accept (.window z.1.2 z.2.1 z.2.2)
    else if t < c.sigmaLow/c.M then .low else .high
  have hf : Measurable f :=
    decisionEquiv.symm.measurable.comp (measurable_inl.comp
      (resultEquiv.symm.measurable.comp (measurable_inl.comp measurable_snd)))
  have ht : Measurable (fun z : (ℝ×ℝ) × (E × BAnswer E) =>
      OriginalCoupledBetaAlgebra.lambda z.1.1 z.1.2 * ‖z.2.1‖) := by
    unfold OriginalCoupledBetaAlgebra.lambda
    fun_prop
  have hwin : MeasurableSet {z : (ℝ×ℝ) × (E × BAnswer E) |
      c.sigmaLow/c.M ≤ OriginalCoupledBetaAlgebra.lambda z.1.1 z.1.2 * ‖z.2.1‖ ∧
      OriginalCoupledBetaAlgebra.lambda z.1.1 z.1.2 * ‖z.2.1‖ ≤ c.sigmaUp/c.M} :=
    (measurableSet_le measurable_const ht).inter (measurableSet_le ht measurable_const)
  have hlo : MeasurableSet {z : (ℝ×ℝ) × (E × BAnswer E) |
      OriginalCoupledBetaAlgebra.lambda z.1.1 z.1.2 * ‖z.2.1‖ < c.sigmaLow/c.M} :=
    measurableSet_lt ht measurable_const
  have hwindow : Measurable (fun z : (ℝ×ℝ) × (E × BAnswer E) =>
      (.accept (.window z.1.2 z.2.1 z.2.2) : BDecision (BResult E))) :=
    decisionEquiv.symm.measurable.comp (measurable_inl.comp (resultEquiv.symm.measurable.comp
      (measurable_inr.comp (measurable_fst.snd.prodMk measurable_snd))))
  have hg : Measurable g := Measurable.ite hwin hwindow
    (Measurable.ite hlo measurable_const measurable_const)
  have hsum : Measurable (Sum.elim f g) := measurable_fun_sum (f:=Sum.elim f g) hf hg
  have hcode : Measurable (fun z : (ℝ×ℝ) × BTrial E =>
      (MeasurableEquiv.prodSumDistrib (ℝ×ℝ) E (E × BAnswer E)) (z.1,trialEquiv z.2)) :=
    (MeasurableEquiv.prodSumDistrib (ℝ×ℝ) E (E × BAnswer E)).measurable.comp
      (measurable_fst.prodMk (trialEquiv.measurable.comp measurable_snd))
  convert hsum.comp hcode using 1
  funext z
  rcases z with ⟨⟨a,b⟩,raw⟩
  cases raw <;> rfl

abbrev TrialContext (E : Type*) := NumericInput E × ℝ

theorem actual_trials_family (c : Settings) :
    BorelFamily (fun z : TrialContext E × ℝ =>
      OriginalBorelWarmReplay.OriginalCoupledGetterProgram.trials
        (withWeight c z.1.1.1.1) z.1.1.1.2 z.1.2 z.1.1.2.1 z.1.1.2.2 z.2) := by
  have hc : Measurable (fun z : TrialContext E × ℝ =>
      OriginalCoupledBetaAlgebra.center z.1.1.2.1 z.1.1.2.2 z.2) := by
    unfold OriginalCoupledBetaAlgebra.center
    fun_prop
  have hl : Measurable (fun z : TrialContext E × ℝ =>
      OriginalCoupledBetaAlgebra.lambda z.1.1.1.1 z.2) := by
    unfold OriginalCoupledBetaAlgebra.lambda
    fun_prop
  have ht := (tolerance_measurable c).comp
    (measurable_fst.fst.fst : Measurable (fun z : TrialContext E × ℝ => z.1.1.1))
  have hparam : Measurable (fun z : TrialContext E × ℝ =>
      (OriginalCoupledBetaAlgebra.center z.1.1.2.1 z.1.1.2.2 z.2,
       (OriginalCoupledBetaAlgebra.lambda z.1.1.1.1 z.2,
        (tolerance (withWeight c z.1.1.1.1) z.1.1.1.2,(c.rho,z.1.2))))) :=
    hc.prodMk (hl.prodMk (ht.prodMk (measurable_const.prodMk measurable_fst.snd)))
  have htrial := precomp_family _ (FangqingBorelWarmATS.actual_trial_program_family (E:=E) c.M) _ hparam
  have hcl : Measurable (fun z : (TrialContext E × ℝ) × BTrial E =>
      classifyResult (withWeight c z.1.1.1.1.1) z.1.2 z.2) :=
    (classify_measurable (E:=E) c).comp
      ((measurable_fst.fst.fst.fst.fst.prodMk measurable_fst.snd).prodMk measurable_snd)
  have hm := map_family _ htrial
    (fun z : (TrialContext E × ℝ) × BTrial E =>
      classifyResult (withWeight c z.1.1.1.1.1) z.1.2 z.2) hcl
  simpa only [OriginalBorelWarmReplay.OriginalCoupledGetterProgram.trials,
    OriginalBorelWarmReplay.FangqingGetterComposition.mappedTaylorTrial,map_eq_original,withWeight] using hm

end
end FangqingBorelWarmClassification
end

section
-- Source component: BorelWarmBisectionFamily.lean

open MeasureTheory
namespace FangqingBorelWarmBisection
open OriginalBetaATSTrial FangqingBorelGetterProgramFamily FangqingBorelWarmData
  FangqingBorelWarmCases FangqingBorelWarmProgramBridges
noncomputable section
set_option maxHeartbeats 4000000

variable {X Q A R : Type*} [MeasurableSpace X] [MeasurableSpace Q]
  [MeasurableSpace A] [MeasurableSpace R]

theorem found_measurable : Measurable (fun r : R => (.found r : BSearchOutcome R)) :=
  searchOutcomeEquiv.symm.measurable.comp measurable_inl

theorem bracket_measurable : Measurable (fun p : ℝ×ℝ => (.bracket p.1 p.2 : BSearchOutcome R)) :=
  searchOutcomeEquiv.symm.measurable.comp measurable_inr

/-- Real finite midpoint bisection after lowering every actual trial to its
primitive query program. The proof follows the actual recursion and all three
response branches, rather than presuming admissibility of arbitrary syntax. -/
theorem lowered_bisect_family
    (trials : X × ℝ → GetterProgram Q A (BDecision R)) (ht : BorelFamily trials) (n : ℕ) :
    BorelFamily (fun z : X × (ℝ×ℝ) =>
      OriginalBorelWarmReplay.FangqingGetterComposition.lower (fun b => trials (z.1,b))
        (OriginalBorelWarmReplay.FangqingHysteresis.bisect n z.2.1 z.2.2)) := by
  induction n with
  | zero =>
    simpa only [OriginalBorelWarmReplay.FangqingHysteresis.bisect,
      OriginalBorelWarmReplay.FangqingGetterComposition.lower] using
      pure_family (fun z : X × (ℝ×ℝ) => (.bracket z.2.1 z.2.2 : BSearchOutcome R))
        (bracket_measurable.comp measurable_snd)
  | succ n ih =>
    let Z := X × (ℝ×ℝ)
    have hm : Measurable (fun z : Z => (z.1,(z.2.1+z.2.2)/2)) := by fun_prop
    have hmid := precomp_family trials ht (fun z : Z => (z.1,(z.2.1+z.2.2)/2)) hm
    have hlo := precomp_family _ ih
      (fun z : Z => (z.1,((z.2.1+z.2.2)/2,z.2.2))) (by fun_prop)
    have hhi := precomp_family _ ih
      (fun z : Z => (z.1,(z.2.1,(z.2.1+z.2.2)/2))) (by fun_prop)
    have haccept : BorelFamily (fun z : Z × R =>
        (.pure (.found z.2) : GetterProgram Q A (BSearchOutcome R))) :=
      pure_family _ (found_measurable.comp measurable_snd)
    have hcase := decision_case_family
      (fun z : Z × R => (.pure (.found z.2) : GetterProgram Q A (BSearchOutcome R)))
      (fun z : Z => OriginalBorelWarmReplay.FangqingGetterComposition.lower (fun b => trials (z.1,b))
        (OriginalBorelWarmReplay.FangqingHysteresis.bisect n ((z.2.1+z.2.2)/2) z.2.2))
      (fun z : Z => OriginalBorelWarmReplay.FangqingGetterComposition.lower (fun b => trials (z.1,b))
        (OriginalBorelWarmReplay.FangqingHysteresis.bisect n z.2.1 ((z.2.1+z.2.2)/2)))
      haccept hlo hhi
    have hbind := bind_family _ hmid _ hcase
    convert hbind using 1
    funext z
    simp only [OriginalBorelWarmReplay.FangqingHysteresis.bisect,
      OriginalBorelWarmReplay.FangqingGetterComposition.lower,bind_eq_original]
    congr 1
    funext answer
    cases answer <;> rfl

/-- Actual two endpoint trials followed by the actual midpoint recursion, with
its observed-data-dependent measurable integer fuel. -/
theorem lowered_endpoints_family
    (trials : X × ℝ → GetterProgram Q A (BDecision R)) (ht : BorelFamily trials)
    (fuel : X → ℕ) (hfuel : Measurable fuel) (lo up : X → ℝ)
    (hlo : Measurable lo) (hup : Measurable up) :
    BorelFamily (fun x : X => OriginalBorelWarmReplay.FangqingGetterComposition.lower
      (fun b => trials (x,b))
      (OriginalBorelWarmReplay.FangqingHysteresis.Program.ask (lo x) (fun left => match left with
        | .accept value => .pure (.found value)
        | _ => .ask (up x) (fun right => match right with
          | .accept value => .pure (.found value)
          | _ => OriginalBorelWarmReplay.FangqingHysteresis.bisect (fuel x) (lo x) (up x))))) := by
  have hb : BorelFamily (fun x : X => OriginalBorelWarmReplay.FangqingGetterComposition.lower
      (fun b => trials (x,b))
      (OriginalBorelWarmReplay.FangqingHysteresis.bisect (fuel x) (lo x) (up x))) :=
    nat_select_family _ (fun n => precomp_family _ (lowered_bisect_family trials ht n)
      (fun x => (x,(lo x,up x))) (measurable_id.prodMk (hlo.prodMk hup))) fuel hfuel
  have ha : BorelFamily (fun z : X × R => (.pure (.found z.2) : GetterProgram Q A (BSearchOutcome R))) :=
    pure_family _ (found_measurable.comp measurable_snd)
  have hright := decision_case_family _ _ _ ha hb hb
  have hupper := precomp_family trials ht (fun x => (x,up x)) (measurable_id.prodMk hup)
  have hbind2 := bind_family _ hupper _ hright
  have hsecond : BorelFamily (fun x : X => OriginalBorelWarmReplay.FangqingGetterComposition.lower
      (fun b => trials (x,b))
      (OriginalBorelWarmReplay.FangqingHysteresis.Program.ask (up x) (fun right => match right with
        | .accept value => .pure (.found value)
        | _ => OriginalBorelWarmReplay.FangqingHysteresis.bisect (fuel x) (lo x) (up x)))) := by
    convert hbind2 using 1
    funext x
    simp only [OriginalBorelWarmReplay.FangqingGetterComposition.lower,bind_eq_original]
    congr 1
    funext ans
    cases ans <;> simp only [OriginalBorelWarmReplay.FangqingGetterComposition.lower,bind_eq_original]
  have hleft := decision_case_family _ _ _ ha hsecond hsecond
  have hlower := precomp_family trials ht (fun x => (x,lo x)) (measurable_id.prodMk hlo)
  have hbind1 := bind_family _ hlower _ hleft
  convert hbind1 using 1
  funext x
  simp only [OriginalBorelWarmReplay.FangqingGetterComposition.lower,bind_eq_original]
  congr 1
  funext ans
  cases ans <;> simp only [OriginalBorelWarmReplay.FangqingGetterComposition.lower,bind_eq_original]

end
end FangqingBorelWarmBisection
end

section
-- Source component: BorelWarmPositiveSearchFamily.lean

open MeasureTheory
namespace FangqingBorelWarmPositiveSearch
open OriginalBetaATSTrial FangqingBorelGetterProgramFamily FangqingBorelWarmData
  FangqingBorelWarmScalars FangqingBorelWarmClassification FangqingBorelWarmBisection
open OriginalBorelWarmReplay.OriginalCoupledBetaSearch
noncomputable section
set_option maxHeartbeats 4500000

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]
local instance : MeasurableSpace E := borel E
local instance : BorelSpace E := ⟨rfl⟩
local instance : MeasurableSpace (E →L[ℝ] E) := borel (E →L[ℝ] E)
local instance : BorelSpace (E →L[ℝ] E) := ⟨rfl⟩

theorem actual_lowered_search_family (c : Settings) :
    BorelFamily (fun z : TrialContext E =>
      OriginalBorelWarmReplay.FangqingGetterComposition.lower
        (OriginalBorelWarmReplay.OriginalCoupledGetterProgram.trials
          (withWeight c z.1.1.1) z.1.1.2 z.2 z.1.2.1 z.1.2.2)
        (searchProgram (withWeight c z.1.1.1) z.1.1.2 z.1.2.1 z.1.2.2)) := by
  have h := lowered_endpoints_family _ (actual_trials_family (E:=E) c)
    (fun z : TrialContext E => fuel (withWeight c z.1.1.1) z.1.1.2 z.1.2.1 z.1.2.2)
    ((fuel_measurable (E:=E) c).comp measurable_fst)
    (fun z : TrialContext E => lower (withWeight c z.1.1.1) z.1.1.2)
    (fun z : TrialContext E => upper (withWeight c z.1.1.1))
    ((lower_measurable c).comp measurable_fst.fst)
    ((upper_measurable c).comp measurable_fst.fst.fst)
  convert h using 1
  funext z
  unfold searchProgram
  congr 1
  congr 1
  funext left
  cases left with
  | accept value => rfl
  | low | high =>
    dsimp only
    congr 1
    funext right
    cases right <;> rfl

abbrev PositiveInput (E : Type*) := (ℝ×ℝ) × (E×E)

/-- The actual initial observed-gradient query, measured refinement/fuel, two
endpoint trials and every midpoint trial are one certified Borel program. -/
theorem actual_positive_program_family (c : Settings) :
    BorelFamily (fun z : PositiveInput E =>
      OriginalBorelWarmReplay.OriginalCoupledGetterProgram.positiveProgram
        (withWeight c z.1.1) z.1.2 z.2.1 z.2.2) := by
  have hG : Measurable (fun z : PositiveInput E × BAnswer E =>
      ‖z.2.grad‖+1+c.Lg*‖z.1.2.1-z.1.2.2‖) :=
    ((answer_grad_measurable.comp measurable_snd).norm.add measurable_const).add
      (measurable_const.mul ((measurable_fst.snd.fst.sub measurable_fst.snd.snd).norm))
  have hctx : Measurable (fun z : PositiveInput E × BAnswer E =>
      (((z.1.1.1,‖z.2.grad‖+1+c.Lg*‖z.1.2.1-z.1.2.2‖),z.1.2),z.1.1.2)) :=
    ((measurable_fst.fst.fst.prodMk hG).prodMk measurable_fst.snd).prodMk measurable_fst.fst.snd
  have hcont := precomp_family _ (actual_lowered_search_family (E:=E) c) _ hctx
  have hq : Measurable (fun z : PositiveInput E => (z.2.2,(1:ℝ))) :=
    measurable_snd.snd.prodMk measurable_const
  have h := ask_family (fun z : PositiveInput E => (z.2.2,(1:ℝ))) hq _ hcont
  simpa only [OriginalBorelWarmReplay.OriginalCoupledGetterProgram.positiveProgram,
    OriginalBorelWarmReplay.FangqingGetterComposition.withInitial,
    OriginalBorelWarmReplay.OriginalCoupledGetterProgram.initialBound,withWeight] using h

end
end FangqingBorelWarmPositiveSearch
end

section
-- Source component: BorelWarmAHPEFamily.lean

open MeasureTheory
namespace FangqingBorelWarmAHPE
open OriginalBetaATSTrial FangqingBorelGetterProgramFamily FangqingBorelWarmData
  FangqingBorelWarmScalars FangqingBorelWarmPositiveSearch FangqingBorelWarmProgramBridges
open OriginalBorelWarmReplay.OriginalCoupledBetaSearch
noncomputable section
set_option maxHeartbeats 5000000

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]
local instance : MeasurableSpace E := borel E
local instance : BorelSpace E := ⟨rfl⟩
local instance : MeasurableSpace (E →L[ℝ] E) := borel (E →L[ℝ] E)
local instance : BorelSpace (E →L[ℝ] E) := ⟨rfl⟩

theorem state_weight_measurable : Measurable (fun s : BState E => s.weight) :=
  measurable_fst.comp stateEquiv.measurable

theorem state_x_measurable : Measurable (fun s : BState E => s.x) :=
  measurable_snd.fst.comp stateEquiv.measurable

theorem state_y_measurable : Measurable (fun s : BState E => s.y) :=
  measurable_snd.snd.comp stateEquiv.measurable

def effectiveWeight (a : ℝ) : ℝ := if a=0 then 1 else a

theorem effective_weight_measurable : Measurable effectiveWeight := by
  classical
  exact Measurable.ite (measurableSet_eq_fun measurable_id measurable_const) measurable_const measurable_id

theorem actual_ahpe_step_program_family (c : Settings) (sigma0 : ℝ) :
    BorelFamily (fun s : BState E =>
      OriginalBorelWarmReplay.OriginalRobustTrajectory.stepProgram c sigma0 s) := by
  classical
  have hw := state_weight_measurable (E:=E)
  have hx := state_x_measurable (E:=E)
  have hy := state_y_measurable (E:=E)
  have ha := effective_weight_measurable.comp hw
  have hdy := (output_precision_measurable c sigma0).comp ha
  have heffY : Measurable (fun s : BState E => if s.weight=0 then s.x else s.y) :=
    Measurable.ite (measurableSet_eq_fun hw measurable_const) hx hy
  have hp := precomp_family _ (actual_positive_program_family (E:=E) c)
    (fun s : BState E => ((effectiveWeight s.weight,
      OriginalBorelWarmReplay.OriginalCertifiedCoupledAHPE.outputQueryPrecision
        (withWeight c (effectiveWeight s.weight)) sigma0),(s.x,if s.weight=0 then s.x else s.y)))
    ((ha.prodMk hdy).prodMk (hx.prodMk heffY))
  convert hp using 1
  funext s
  by_cases hs : s.weight=0 <;>
    simp [OriginalBorelWarmReplay.OriginalRobustTrajectory.stepProgram,
      OriginalBorelWarmReplay.OriginalRobustTrajectory.settingsAt,
      OriginalBorelWarmReplay.OriginalCertifiedCoupledAHPE.program,
      OriginalBorelWarmReplay.OriginalCertifiedCoupledAHPE.effective,
      OriginalBorelWarmReplay.OriginalFirstCoupledStep.proxySettings,
      OriginalBorelWarmReplay.OriginalCertifiedCoupledAHPE.effectiveY,withWeight,effectiveWeight,hs]

abbrev WindowInput (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  BState E × (ℝ × (E × BAnswer E))

theorem next_window_measurable (c : Settings) :
    Measurable (fun z : WindowInput E =>
      OriginalBorelWarmReplay.OriginalRobustTrajectory.nextWindow c z.1 z.2.1 z.2.2.1 z.2.2.2) := by
  classical
  have hw := (state_weight_measurable (E:=E)).comp (measurable_fst :
    Measurable (fun z : WindowInput E => z.1))
  have hx := (state_x_measurable (E:=E)).comp (measurable_fst :
    Measurable (fun z : WindowInput E => z.1))
  have hy := (state_y_measurable (E:=E)).comp (measurable_fst :
    Measurable (fun z : WindowInput E => z.1))
  have hb : Measurable (fun z : WindowInput E => z.2.1) := measurable_snd.fst
  have hd : Measurable (fun z : WindowInput E => z.2.2.1) := measurable_snd.snd.fst
  have hg : Measurable (fun z : WindowInput E => z.2.2.2.grad) :=
    answer_grad_measurable.comp measurable_snd.snd.snd
  have heffA := effective_weight_measurable.comp hw
  have hlam : Measurable (fun z : WindowInput E =>
      OriginalCoupledBetaAlgebra.lambda (effectiveWeight z.1.weight) z.2.1) := by
    unfold OriginalCoupledBetaAlgebra.lambda
    exact (heffA.mul (hb.pow_const 2)).div (measurable_const.sub hb)
  have hwgt : Measurable (fun z : WindowInput E =>
      (OriginalCoupledBetaAlgebra.lambda (effectiveWeight z.1.weight) z.2.1 +
        Real.sqrt ((OriginalCoupledBetaAlgebra.lambda (effectiveWeight z.1.weight) z.2.1)^2+
          4*OriginalCoupledBetaAlgebra.lambda (effectiveWeight z.1.weight) z.2.1*z.1.weight))/2) :=
    (hlam.add (Real.continuous_sqrt.measurable.comp ((hlam.pow_const 2).add
      ((measurable_const.mul hlam).mul hw)))).div measurable_const
  have heffY : Measurable (fun z : WindowInput E => if z.1.weight=0 then z.1.x else z.1.y) :=
    Measurable.ite (measurableSet_eq_fun hw measurable_const) hx hy
  have hnewY : Measurable (fun z : WindowInput E =>
      (1-z.2.1) • (if z.1.weight=0 then z.1.x else z.1.y) + z.2.1 • z.1.x) :=
    ((measurable_const.sub hb).smul heffY).add (hb.smul hx)
  apply measurable_comap_iff.mpr
  change Measurable (fun z : WindowInput E => stateCode
    (OriginalBorelWarmReplay.OriginalRobustTrajectory.nextWindow c z.1 z.2.1 z.2.2.1 z.2.2.2))
  convert (hw.add hwgt).prodMk ((hx.sub (hwgt.smul hg)).prodMk (hnewY.add hd)) using 1
  funext z
  by_cases hs : z.1.weight=0 <;>
    simp [stateCode,OriginalBorelWarmReplay.OriginalRobustTrajectory.nextWindow,
      OriginalBorelWarmReplay.OriginalRobustTrajectory.settingsAt,
      OriginalBorelWarmReplay.OriginalCertifiedCoupledAHPE.actualWeight,
      OriginalBorelWarmReplay.OriginalCertifiedCoupledAHPE.actualLambda,
      OriginalBorelWarmReplay.OriginalCertifiedCoupledAHPE.actualCenter,
      OriginalBorelWarmReplay.OriginalCertifiedCoupledAHPE.effective,
      OriginalBorelWarmReplay.OriginalCertifiedCoupledAHPE.effectiveY,
      OriginalBorelWarmReplay.OriginalFirstCoupledStep.proxySettings,
      OriginalCoupledBetaAlgebra.center,effectiveWeight,hs]

end
end FangqingBorelWarmAHPE
end

section
-- Source component: BorelWarmAHPETrajectoryFamily.lean

open MeasureTheory
namespace FangqingBorelWarmTrajectory
open OriginalBetaATSTrial FangqingBorelGetterProgramFamily FangqingBorelWarmData
  FangqingBorelWarmAHPE FangqingBorelWarmEncodedCases FangqingBorelWarmProgramBridges
open OriginalBorelWarmReplay.OriginalCoupledBetaSearch
noncomputable section
set_option maxHeartbeats 5000000

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]
local instance : MeasurableSpace E := borel E
local instance : BorelSpace E := ⟨rfl⟩
local instance : MeasurableSpace (E →L[ℝ] E) := borel (E →L[ℝ] E)
local instance : BorelSpace (E →L[ℝ] E) := ⟨rfl⟩

theorem outcome_stop_measurable : Measurable (fun w : E => (.stop w : BOutcome E)) :=
  outcomeEquiv.symm.measurable.comp measurable_inl

theorem outcome_finished_measurable : Measurable (fun s : BState E => (.finished s : BOutcome E)) :=
  outcomeEquiv.symm.measurable.comp (measurable_inr.comp measurable_inl)

theorem actual_ahpe_loop_family (c : Settings) (sigma0 : ℝ) (n : ℕ) :
    BorelFamily (fun s : BState E =>
      OriginalBorelWarmReplay.OriginalRobustTrajectory.loopProgram c sigma0 n s) := by
  induction n with
  | zero =>
    simpa only [OriginalBorelWarmReplay.OriginalRobustTrajectory.loopProgram] using
      pure_family (Q:=E×ℝ) (A:=BAnswer E) (fun s : BState E => (.finished s : BOutcome E))
        outcome_finished_measurable
  | succ n ih =>
    have hs : BorelFamily (fun z : BState E × E =>
        (.pure (.stop z.2) : GetterProgram (E×ℝ) (BAnswer E) (BOutcome E))) :=
      pure_family _ (outcome_stop_measurable.comp measurable_snd)
    have hw := precomp_family _ ih _ (next_window_measurable (E:=E) c)
    have hr0 := encoded_case_family (resultEquiv (E:=E))
      (fun z : BState E × E => (.pure (.stop z.2) : GetterProgram (E×ℝ) (BAnswer E) (BOutcome E)))
      (fun z : WindowInput E => OriginalBorelWarmReplay.OriginalRobustTrajectory.loopProgram c sigma0 n
        (OriginalBorelWarmReplay.OriginalRobustTrajectory.nextWindow c z.1 z.2.1 z.2.2.1 z.2.2.2)) hs hw
    have hr : BorelFamily (fun z : BState E × BResult E => match z.2 with
        | .stop w => (.pure (.stop w) : GetterProgram (E×ℝ) (BAnswer E) (BOutcome E))
        | .window b d aY => OriginalBorelWarmReplay.OriginalRobustTrajectory.loopProgram c sigma0 n
          (OriginalBorelWarmReplay.OriginalRobustTrajectory.nextWindow c z.1 b d aY)) := by
      convert hr0 using 1
      funext z
      rcases z with ⟨s,r⟩
      cases r <;> rfl
    have hf : BorelFamily (fun _ : BState E × (ℝ×ℝ) =>
        (.pure .failure : GetterProgram (E×ℝ) (BAnswer E) (BOutcome E))) :=
      pure_family _ measurable_const
    have hk0 := encoded_case_family (searchOutcomeEquiv (R:=BResult E)) _ _ hr hf
    have hk : BorelFamily (fun z : BState E × BSearchOutcome (BResult E) => match z.2 with
        | .found (.stop w) => (.pure (.stop w) : GetterProgram (E×ℝ) (BAnswer E) (BOutcome E))
        | .found (.window b d aY) => OriginalBorelWarmReplay.OriginalRobustTrajectory.loopProgram c sigma0 n
          (OriginalBorelWarmReplay.OriginalRobustTrajectory.nextWindow c z.1 b d aY)
        | .bracket _ _ => .pure .failure) := by
      convert hk0 using 1
      funext z
      rcases z with ⟨s,r⟩
      cases r with
      | found r => cases r <;> rfl
      | bracket l u => rfl
    have hb := bind_family _ (actual_ahpe_step_program_family (E:=E) c sigma0) _ hk
    convert hb using 1
    funext s
    simp only [OriginalBorelWarmReplay.OriginalRobustTrajectory.loopProgram,bind_eq_original]
    congr 1

theorem result_point_measurable :
    Measurable (OriginalBorelWarmReplay.OriginalRobustTrajectory.resultPoint : BOutcome E → E) := by
  have hright : Measurable (Sum.elim (fun s : BState E => s.y) (fun _ : Unit => (0:E))) :=
    measurable_fun_sum (f:=Sum.elim (fun s : BState E => s.y) (fun _ : Unit => (0:E)))
      state_y_measurable measurable_const
  have hall : Measurable (Sum.elim (fun w : E => w)
      (Sum.elim (fun s : BState E => s.y) (fun _ : Unit => (0:E)))) :=
    measurable_fun_sum (f:=Sum.elim (fun w : E => w)
      (Sum.elim (fun s : BState E => s.y) (fun _ : Unit => (0:E)))) measurable_id hright
  convert hall.comp outcomeEquiv.measurable using 1
  funext r
  cases r <;> rfl

theorem actual_contraction_program_family (c : Settings) (sigma0 D : ℝ) :
    BorelFamily (fun start : E =>
      OriginalBorelWarmReplay.OriginalRobustTrajectory.contractionProgram c sigma0 D start) := by
  have hi : Measurable (fun start : E => (⟨0,start,start⟩ : BState E)) :=
    stateEquiv.symm.measurable.comp (measurable_const.prodMk (measurable_id.prodMk measurable_id))
  have hp := precomp_family _ (actual_ahpe_loop_family (E:=E) c sigma0
    (OriginalBorelWarmReplay.OriginalRobustTrajectory.contractionIterations c sigma0 D)) _ hi
  have hm := map_family _ hp (fun z : E × BOutcome E =>
    OriginalBorelWarmReplay.OriginalRobustTrajectory.resultPoint z.2)
    (result_point_measurable.comp measurable_snd)
  simpa only [OriginalBorelWarmReplay.OriginalRobustTrajectory.contractionProgram,map_eq_original] using hm

theorem actual_one_radius_program_family (c : Settings) (sigma0 R : ℝ) :
    BorelFamily (fun start : E =>
      OriginalBorelWarmReplay.OriginalRobustTrajectory.oneRadiusProgram c sigma0 R start) :=
  actual_contraction_program_family (OriginalBorelWarmReplay.OriginalRobustTrajectory.atRadius c R) sigma0 R

/-- Full actual finite restart program, including all nested adaptive beta
trials. No aggregate per-step measurability or admissibility premise is added. -/
theorem actual_positive_restarts_family (c : Settings) (sigma0 : ℝ) (r : ℕ) (R : ℝ) :
    BorelFamily (fun start : E =>
      OriginalBorelWarmReplay.OriginalRobustTrajectory.restartProgram c sigma0 r R start) := by
  induction r generalizing R with
  | zero =>
    simpa only [OriginalBorelWarmReplay.OriginalRobustTrajectory.restartProgram] using
      pure_family (Q:=E×ℝ) (A:=BAnswer E) (fun start : E => start) measurable_id
  | succ r ih =>
    have hc := precomp_family _ (ih (R/2)) (fun z : E×E => z.2) measurable_snd
    have hb := bind_family _ (actual_one_radius_program_family (E:=E) c sigma0 R) _ hc
    simpa only [OriginalBorelWarmReplay.OriginalRobustTrajectory.restartProgram,bind_eq_original] using hb

end
end FangqingBorelWarmTrajectory
end

section
-- Source component: BorelOperatorInverse.lean

open MeasureTheory
namespace OriginalBorelOperatorInverse
noncomputable section
local instance (p : Prop) : Decidable p := Classical.propDecidable p

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace (E →L[ℝ] E)] [BorelSpace (E →L[ℝ] E)]

theorem ring_inverse_measurable : Measurable (Ring.inverse : (E →L[ℝ] E) → (E →L[ℝ] E)) := by
  have hcont : ContinuousOn (Ring.inverse : (E →L[ℝ] E) → (E →L[ℝ] E)) {T | IsUnit T} := by
    intro T hT
    obtain ⟨u,rfl⟩ := hT
    exact (NormedRing.inverse_continuousAt u).continuousWithinAt
  have hp := hcont.measurable_piecewise (continuous_const.continuousOn :
    ContinuousOn (fun _ : E →L[ℝ] E => (0:E →L[ℝ] E)) {T | IsUnit T}ᶜ)
      (Units.isOpen.measurableSet : MeasurableSet {T : E →L[ℝ] E | IsUnit T})
  convert hp using 1
  funext T
  by_cases hT : IsUnit T
  · simp [Set.piecewise,hT]
  · simp [Set.piecewise,hT,Ring.inverse_non_unit]

theorem continuous_linear_map_inverse_measurable :
    Measurable (ContinuousLinearMap.inverse : (E →L[ℝ] E) → (E →L[ℝ] E)) := by
  rw [← ContinuousLinearMap.ringInverse_eq_inverse]
  exact ring_inverse_measurable

end
end OriginalBorelOperatorInverse
end

section
-- Source component: BorelDualOracleProgram.lean

open MeasureTheory Function
namespace FangqingBorelDualOracleProgram
open OriginalSaddleImplicit OriginalDualOracleProgram OriginalDualGetterImplementation OriginalBetaATSTrial
  FangqingBorelGetterProgramFamily
noncomputable section
set_option maxHeartbeats 4500000

variable {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [MeasurableSpace Z] [MeasurableSpace (Z →L[ℝ] Z)]

def answerEncode (a : OracleAnswer Z) : ℝ × (Z × (Z →L[ℝ] Z)) := (a.value,(a.grad,a.hess))

instance oracleAnswerMeasurableSpace : MeasurableSpace (OracleAnswer Z) :=
  MeasurableSpace.comap answerEncode inferInstance

theorem answer_encode_measurable : Measurable (answerEncode (Z := Z)) :=
  Measurable.of_comap_le le_rfl

theorem answer_value_measurable : Measurable (OracleAnswer.value (Z := Z)) :=
  measurable_fst.comp answer_encode_measurable

theorem answer_gradient_measurable : Measurable (OracleAnswer.grad (Z := Z)) :=
  measurable_fst.comp (measurable_snd.comp answer_encode_measurable)

theorem answer_hessian_measurable : Measurable (OracleAnswer.hess (Z := Z)) :=
  measurable_snd.comp (measurable_snd.comp answer_encode_measurable)

theorem answer_mk_measurable {X : Type*} [MeasurableSpace X]
    (v : X → ℝ) (g : X → Z) (H : X → Z →L[ℝ] Z)
    (hv : Measurable v) (hg : Measurable g) (hH : Measurable H) :
    Measurable (fun x => (⟨v x,g x,H x⟩ : OracleAnswer Z)) := by
  apply measurable_comap_iff.mpr
  exact hv.prodMk (hg.prodMk hH)

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F] [FiniteDimensional ℝ F]
  [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]
  [MeasurableSpace (Joint E F)] [BorelSpace (Joint E F)]
  [MeasurableSpace (Joint E F →L[ℝ] Joint E F)] [BorelSpace (Joint E F →L[ℝ] Joint E F)]

def stateEncode (s : QueryState E F) : E × OracleAnswer (Joint E F) := (s.u,s.answer)

instance queryStateMeasurableSpace : MeasurableSpace (QueryState E F) :=
  MeasurableSpace.comap stateEncode inferInstance

theorem state_encode_measurable : Measurable (stateEncode (E := E) (F := F)) :=
  Measurable.of_comap_le le_rfl

theorem state_u_measurable : Measurable (QueryState.u (E := E) (F := F)) :=
  measurable_fst.comp state_encode_measurable

theorem state_answer_measurable : Measurable (QueryState.answer (E := E) (F := F)) :=
  measurable_snd.comp state_encode_measurable

theorem state_mk_measurable {X : Type*} [MeasurableSpace X]
    (u : X → E) (a : X → OracleAnswer (Joint E F)) (hu : Measurable u) (ha : Measurable a) :
    Measurable (fun x => (⟨u x,a x⟩ : QueryState E F)) := by
  apply measurable_comap_iff.mpr
  exact hu.prodMk ha

theorem residual_measurable (L : ℝ) :
    Measurable (fun z : E × QueryState E F => answerResidual L z.1 z.2) := by
  have hg : Measurable (fun z : E × QueryState E F => z.2.answer.grad) :=
    answer_gradient_measurable.comp ((state_answer_measurable (E := E) (F := F)).comp measurable_snd)
  have hgx := (WithLp.fstL 2 ℝ E F).continuous.measurable.comp hg
  have hu := state_u_measurable.comp (measurable_snd : Measurable (Prod.snd : E × QueryState E F → QueryState E F))
  exact hgx.add (measurable_const.smul (hu.sub measurable_fst))

theorem next_point_measurable (L : ℝ) :
    Measurable (fun z : E × QueryState E F => nextPoint L z.1 z.2) :=
  (state_u_measurable.comp measurable_snd).sub (measurable_const.smul (residual_measurable L))

theorem loop_family (L : ℝ) (n : ℕ) :
    BorelFamily (fun z : (E × F) × QueryState E F => liftQuery (loop L z.1.1 z.1.2 n z.2)) := by
  induction n with
  | zero => exact pure_family Prod.snd measurable_snd
  | succ n ih =>
      have hp : Measurable (fun z : (E × F) × QueryState E F => nextPoint L z.1.1 z.2) :=
        (next_point_measurable L).comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
      have hq : Measurable (fun z : (E × F) × QueryState E F =>
          JointSliceRegularity.point (nextPoint L z.1.1 z.2) z.1.2) := by
        unfold JointSliceRegularity.point
        fun_prop
      have hnew : Measurable (fun z : ((E × F) × QueryState E F) × OracleAnswer (Joint E F) =>
          (z.1.1,(⟨nextPoint L z.1.1.1 z.1.2,z.2⟩ : QueryState E F))) :=
        (measurable_fst.comp measurable_fst).prodMk
          (state_mk_measurable _ _ (hp.comp measurable_fst) measurable_snd)
      exact ask_family _ hq _ (precomp_family _ ih _ hnew)

end
end FangqingBorelDualOracleProgram
end

section
-- Source component: BorelDualOracleSimulator.lean

open MeasureTheory Function
namespace FangqingBorelDualOracleSimulator
open OriginalSaddleImplicit OriginalDualOracleProgram OriginalDualGetterImplementation
  FangqingBorelDualOracleProgram FangqingBorelGetterProgramFamily
noncomputable section
set_option maxHeartbeats 4500000
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F] [FiniteDimensional ℝ F]
  [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]
  [MeasurableSpace (Joint E F)] [BorelSpace (Joint E F)]
  [MeasurableSpace (Joint E F →L[ℝ] Joint E F)] [BorelSpace (Joint E F →L[ℝ] Joint E F)]

abbrev SimulatorInput (E F : Type*) := E × (F × (E × ℝ))

theorem simulator_family (L : ℝ) :
    BorelFamily (fun z : SimulatorInput E F =>
      liftQuery (simulator L z.1 z.2.1 z.2.2.1 z.2.2.2)) := by
  have hq : Measurable (fun z : SimulatorInput E F => JointSliceRegularity.point z.2.2.1 z.2.1) := by
    unfold JointSliceRegularity.point
    fun_prop
  let state : SimulatorInput E F × OracleAnswer (Joint E F) → QueryState E F :=
    fun z => ⟨z.1.2.2.1,z.2⟩
  have hstate : Measurable state := state_mk_measurable _ _ (by fun_prop) measurable_snd
  have hx : Measurable (fun z : SimulatorInput E F × OracleAnswer (Joint E F) => z.1.1) := by fun_prop
  have he : Measurable (fun z : SimulatorInput E F × OracleAnswer (Joint E F) => z.1.2.2.2) := by fun_prop
  have hmap : Measurable (fun z : SimulatorInput E F × OracleAnswer (Joint E F) => ((z.1.1,z.1.2.1),state z)) :=
    (hx.prodMk (by fun_prop)).prodMk hstate
  have hres := (residual_measurable L).comp (hx.prodMk hstate)
  have hbudget : Measurable (fun z : SimulatorInput E F × OracleAnswer (Joint E F) =>
      OriginalDualOracleGD.logBudget (‖answerResidual L z.1.1 (state z)‖/L) z.1.2.2.2) := by
    unfold OriginalDualOracleGD.logBudget
    exact Nat.measurable_ceil.comp (measurable_const.mul (Real.measurable_log.comp
      (measurable_const.add ((measurable_const.mul (hres.norm.div measurable_const)).div he))))
  have hcont := nat_select_family
    (fun n (z : SimulatorInput E F × OracleAnswer (Joint E F)) =>
      liftQuery (loop L z.1.1 z.1.2.1 n (state z)))
    (fun n => precomp_family _ (loop_family L n) _ hmap) _ hbudget
  exact ask_family _ hq _ hcont

variable
  [MeasurableSpace (E →L[ℝ] E)] [BorelSpace (E →L[ℝ] E)]
  [MeasurableSpace (E →L[ℝ] F)] [BorelSpace (E →L[ℝ] F)]
  [MeasurableSpace (F →L[ℝ] E)] [BorelSpace (F →L[ℝ] E)]
  [MeasurableSpace (F →L[ℝ] F)] [BorelSpace (F →L[ℝ] F)]

theorem gradient_output_measurable : Measurable (gradientOutput (E := E) (F := F)) := by
  have hg := answer_gradient_measurable.comp (state_answer_measurable (E := E) (F := F))
  exact ((WithLp.sndL 2 ℝ E F).continuous.measurable.comp hg).neg

theorem hessian_output_measurable (L : ℝ) : Measurable (hessianOutput (E := E) (F := F) L) := by
  let X := (JointSliceRegularity.axisX (E := E) (F := F)).toContinuousLinearMap
  let Y := (JointSliceRegularity.axisY (E := E) (F := F)).toContinuousLinearMap
  let AA := fun H : Joint E F →L[ℝ] Joint E F => (WithLp.fstL 2 ℝ E F).comp (H.comp X) +
    (2*L) • ContinuousLinearMap.id ℝ E
  let UU := fun H : Joint E F →L[ℝ] Joint E F => (WithLp.fstL 2 ℝ E F).comp (H.comp Y)
  let VV := fun H : Joint E F →L[ℝ] Joint E F => (WithLp.sndL 2 ℝ E F).comp (H.comp X)
  let WW := fun H : Joint E F →L[ℝ] Joint E F => (WithLp.sndL 2 ℝ E F).comp (H.comp Y)
  have hAA : Continuous AA := by unfold AA; fun_prop
  have hUU : Continuous UU := by unfold UU; fun_prop
  have hVV : Continuous VV := by unfold VV; fun_prop
  have hWW : Continuous WW := by unfold WW; fun_prop
  have hH := answer_hessian_measurable.comp (state_answer_measurable (E := E) (F := F))
  have hi := OriginalBorelOperatorInverse.continuous_linear_map_inverse_measurable.comp (hAA.measurable.comp hH)
  have hcomp : Continuous (fun z : (E →L[ℝ] F) × ((E →L[ℝ] E) × (F →L[ℝ] E)) => z.1.comp (z.2.1.comp z.2.2)) := by fun_prop
  exact (hWW.measurable.comp hH).neg.add
    (hcomp.measurable.comp ((hVV.measurable.comp hH).prodMk (hi.prodMk (hUU.measurable.comp hH))))

end
end FangqingBorelDualOracleSimulator
end

section
-- Source component: BorelWarmDualGetterFamily.lean

open MeasureTheory
namespace FangqingBorelWarmDualGetterFamily
open OriginalSaddleImplicit FangqingBorelGetterProgramFamily FangqingBorelWarmData
  FangqingBorelDualOracleSimulator
noncomputable section
set_option maxHeartbeats 4500000

variable {Q A R : Type*}

theorem lift_query_eq_original (p : OriginalDualOracleProgram.QueryProgram Q A R) :
    OriginalBorelWarmReplay.OriginalDualGetterImplementation.liftQuery p = OriginalDualGetterImplementation.liftQuery p := by
  induction p with
  | pure r => rfl
  | ask q k ih =>
      simp only [OriginalBorelWarmReplay.OriginalDualGetterImplementation.liftQuery,
        OriginalDualGetterImplementation.liftQuery]
      congr 1
      funext a
      exact ih a

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F] [FiniteDimensional ℝ F]
local instance : MeasurableSpace E := borel E
local instance : BorelSpace E := ⟨rfl⟩
local instance : MeasurableSpace F := borel F
local instance : BorelSpace F := ⟨rfl⟩
local instance : MeasurableSpace (Joint E F) := borel (Joint E F)
local instance : BorelSpace (Joint E F) := ⟨rfl⟩
local instance : MeasurableSpace (Joint E F →L[ℝ] Joint E F) := borel (Joint E F →L[ℝ] Joint E F)
local instance : BorelSpace (Joint E F →L[ℝ] Joint E F) := ⟨rfl⟩
local instance : MeasurableSpace (E →L[ℝ] E) := borel (E →L[ℝ] E)
local instance : BorelSpace (E →L[ℝ] E) := ⟨rfl⟩
local instance : MeasurableSpace (E →L[ℝ] F) := borel (E →L[ℝ] F)
local instance : BorelSpace (E →L[ℝ] F) := ⟨rfl⟩
local instance : MeasurableSpace (F →L[ℝ] E) := borel (F →L[ℝ] E)
local instance : BorelSpace (F →L[ℝ] E) := ⟨rfl⟩
local instance : MeasurableSpace (F →L[ℝ] F) := borel (F →L[ℝ] F)
local instance : BorelSpace (F →L[ℝ] F) := ⟨rfl⟩

abbrev Input (E F : Type*) := E × (E × (F × ℝ))

theorem actual_dual_getter_program_family (L rho : ℝ) :
    BorelFamily (fun z : Input E F =>
      OriginalBorelWarmReplay.OriginalDualGetterImplementation.oracleProgram L rho z.1 z.2.1 z.2.2) := by
  have hargs : Measurable (fun z : Input E F =>
      (z.1,(z.2.2.1,(z.2.1,OriginalBorelWarmReplay.OriginalDualGetterImplementation.accuracyRadius L rho z.2.2.2)))) := by
    unfold OriginalBorelWarmReplay.OriginalDualGetterImplementation.accuracyRadius
    fun_prop
  have hs := precomp_family _ (simulator_family (E := E) (F := F) L) _ hargs
  have hout : Measurable (fun s : OriginalDualOracleProgram.QueryState E F =>
      (⟨OriginalDualOracleProgram.gradientOutput s,OriginalDualOracleProgram.hessianOutput L s⟩ : BAnswer F)) :=
    answerEquiv.symm.measurable.comp (gradient_output_measurable.prodMk (hessian_output_measurable L))
  have hm := map_family _ hs (fun z : Input E F × OriginalDualOracleProgram.QueryState E F =>
      (⟨OriginalDualOracleProgram.gradientOutput z.2,OriginalDualOracleProgram.hessianOutput L z.2⟩ : BAnswer F))
      (hout.comp measurable_snd)
  simpa only [OriginalBorelWarmReplay.OriginalDualGetterImplementation.oracleProgram,
    FangqingBorelWarmProgramBridges.map_eq_original,lift_query_eq_original] using hm

end
end FangqingBorelWarmDualGetterFamily
end

section
-- Source component: BorelBoundedPrimitiveLower.lean

open MeasureTheory Function
namespace FangqingBorelBoundedPrimitiveLower
open OriginalBetaATSTrial FangqingGetterComposition FangqingBorelGetterProgramFamily
noncomputable section
set_option maxHeartbeats 6000000
universe u
variable {X Q A R BQ BA : Type u}

def afterOne : GetterProgram Q A R → A → GetterProgram Q A R
  | .pure r, _ => .pure r
  | .ask _ k, a => k a

def streamCons (a : A) (t : ℕ → A) : ℕ → A
  | 0 => a
  | n+1 => t n

theorem streamDrop_streamCons (a : A) (t : ℕ → A) : streamDrop 1 (streamCons a t) = t := by
  funext n
  simp only [streamDrop,Nat.add_comm 1 n,streamCons]

theorem stream_run_after_one (p : GetterProgram Q A R) (a : A) (t : ℕ → A) :
    streamRun (afterOne p a) t = ((streamRun p (streamCons a t)).1,(streamRun p (streamCons a t)).2.drop 1) := by
  cases p with
  | pure r => rfl
  | ask q k => simp only [afterOne,streamRun,streamCons,streamDrop_streamCons,List.drop_succ_cons,List.drop_zero]

def boundedLower (oracle : Q → GetterProgram BQ BA A) : ℕ → GetterProgram Q A R → GetterProgram BQ BA (Unit ⊕ R)
  | _, .pure r => .pure (.inr r)
  | 0, .ask _ _ => .pure (.inl ())
  | n+1, .ask q k => FangqingGetterComposition.bind (oracle q) (fun a => boundedLower oracle n (k a))

section Borel
variable [MeasurableSpace Q] [MeasurableSpace A] [MeasurableSpace R]
  [MeasurableSpace BQ] [MeasurableSpace BA]

theorem stream_cons_measurable : Measurable (fun z : A × (ℕ → A) => streamCons z.1 z.2) := by
  apply measurable_pi_lambda
  intro n
  cases n with
  | zero => exact measurable_fst
  | succ n => exact (measurable_pi_apply n).comp measurable_snd

theorem after_one_family [MeasurableSpace X] (p : X → GetterProgram Q A R) (hp : BorelFamily p) :
    BorelFamily (fun z : X × A => afterOne (p z.1) z.2) := by
  have hi : Measurable (fun z : (X × A) × (ℕ → A) => (z.1.1,streamCons z.1.2 z.2)) :=
    measurable_fst.fst.prodMk (stream_cons_measurable.comp (measurable_fst.snd.prodMk measurable_snd))
  refine ⟨?_,?_,?_⟩
  · simpa only [stream_run_after_one,Function.comp_def] using hp.result.comp hi
  · convert! (hp.count.comp hi).sub (measurable_const (a := (1:ℕ))) using 1
    funext z
    simp only [stream_run_after_one,List.length_drop,Pi.sub_apply,Function.comp_def]
  · intro q0 n
    simpa only [stream_run_after_one,List.getD_eq_getElem?_getD,List.getElem?_drop,Function.comp_def] using
      (hp.request q0 (1+n)).comp hi

/-- The bounded composition is a Borel program on all answer streams. The fuel
bounds OUTER requests only; every inner actual query is retained and charged. -/
theorem bounded_lower_family (a0 : A) (q0 : Q) (fuel : ℕ) :
    ∀ {X : Type u} [MeasurableSpace X] (p : X → GetterProgram Q A R) (hp : BorelFamily p)
      (oracle : X × Q → GetterProgram BQ BA A) (ho : BorelFamily oracle),
      BorelFamily (fun x => boundedLower (fun q => oracle (x,q)) fuel (p x)) := by
  induction fuel with
  | zero =>
      intro X mX p hp oracle ho
      have hi : Measurable (fun x : X => (x,fun _ : ℕ => a0)) := measurable_id.prodMk measurable_const
      have hc := hp.count.comp hi
      have hr := hp.result.comp hi
      have ht : MeasurableSet {x : X | (streamRun (p x) (fun _ => a0)).2.length = 0} := measurableSet_eq_fun hc measurable_const
      have hyes := pure_family (Q := BQ) (A := BA) (fun x : X => (Sum.inr (streamRun (p x) (fun _ => a0)).1 : Unit ⊕ R))
        (measurable_inr.comp hr)
      have hno := pure_family (Q := BQ) (A := BA) (fun _ : X => (Sum.inl () : Unit ⊕ R)) measurable_const
      classical
      convert! ite_family _ ht _ _ hyes hno using 1
      funext x
      cases he : p x with
      | pure r => simp only [he,boundedLower,streamRun,List.length_nil,ite_true]
      | ask q k => simp only [he,boundedLower,streamRun,List.length_cons,Nat.add_eq_zero,one_ne_zero,and_false,if_false]
  | succ fuel ih =>
      intro X mX p hp oracle ho
      have hi : Measurable (fun x : X => (x,fun _ : ℕ => a0)) := measurable_id.prodMk measurable_const
      have hc := hp.count.comp hi
      have hr := hp.result.comp hi
      have hq := (hp.request q0 0).comp hi
      have ht : MeasurableSet {x : X | (streamRun (p x) (fun _ => a0)).2.length = 0} := measurableSet_eq_fun hc measurable_const
      let request : X → Q := fun x => (streamRun (p x) (fun _ => a0)).2.getD 0 q0
      have hinner := precomp_family oracle ho (fun x => (x,request x)) (measurable_id.prodMk hq)
      have ho' : BorelFamily (fun z : (X × A) × Q => oracle (z.1.1,z.2)) :=
        precomp_family oracle ho _ (measurable_fst.fst.prodMk measurable_snd)
      have htail := ih (fun z : X × A => afterOne (p z.1) z.2) (after_one_family p hp)
        (fun z : (X × A) × Q => oracle (z.1.1,z.2)) ho'
      have hno := bind_family _ hinner _ htail
      have hyes := pure_family (Q := BQ) (A := BA) (fun x : X => (Sum.inr (streamRun (p x) (fun _ => a0)).1 : Unit ⊕ R))
        (measurable_inr.comp hr)
      classical
      convert! ite_family _ ht _ _ hyes hno using 1
      funext x
      cases he : p x with
      | pure r => simp only [he,boundedLower,streamRun,List.length_nil,ite_true]
      | ask q k =>
          simp only [he,boundedLower,streamRun,List.length_cons,Nat.add_eq_zero,one_ne_zero,and_false,if_false,
            request,List.getD_cons_zero,afterOne]

end Borel

theorem trace_bind_actual (base : BQ → BA) (p : GetterProgram BQ BA A) (k : A → GetterProgram BQ BA R) :
    trace base (FangqingGetterComposition.bind p k) = trace base p ++ trace base (k (execute base p).1) := by
  induction p with
  | pure r => rfl
  | ask q cont ih => simp only [FangqingGetterComposition.bind,trace,execute,ih,List.cons_append]

/-- Under the independently proved outer-query budget, bounded composition
has exactly the original lowered result, complete actual trace and charged cost. -/
theorem bounded_lower_actual_execution (base : BQ → BA) (oracle : Q → GetterProgram BQ BA A)
    (p : GetterProgram Q A R) (fuel : ℕ)
    (hbudget : (execute (implementedGetter base oracle) p).2 ≤ fuel) :
    execute base (boundedLower oracle fuel p) =
      (.inr (execute base (primitiveLower oracle p)).1,(execute base (primitiveLower oracle p)).2) ∧
    trace base (boundedLower oracle fuel p) = trace base (primitiveLower oracle p) := by
  induction p generalizing fuel with
  | pure r => cases fuel <;> exact ⟨rfl,rfl⟩
  | ask q cont ih =>
      cases fuel with
      | zero => simp only [execute] at hbudget; omega
      | succ fuel =>
          have ht : (execute (implementedGetter base oracle) (cont (implementedGetter base oracle q))).2 ≤ fuel := by
            simpa only [execute,Nat.add_le_add_iff_right] using hbudget
          have hh := ih (implementedGetter base oracle q) fuel ht
          constructor
          · simp only [boundedLower,primitiveLower,execute_bind]
            have hh' := hh.1
            change execute base (boundedLower oracle fuel (cont (execute base (oracle q)).1)) = _ at hh'
            rw [hh']
            rfl
          · simp only [boundedLower,primitiveLower,trace_bind_actual,implementedGetter]
            exact congrArg (fun l => trace base (oracle q) ++ l) hh.2

end
end FangqingBorelBoundedPrimitiveLower

namespace FangqingBorelBoundedPrimitiveLower
open OriginalBetaATSTrial FangqingBorelGetterProgramFamily
noncomputable section
universe u
variable {X Q A R BQ BA : Type u}
  [MeasurableSpace X] [MeasurableSpace Q] [MeasurableSpace A] [MeasurableSpace R]
  [MeasurableSpace BQ] [MeasurableSpace BA]

theorem bounded_lower_variable_fuel_family (a0 : A) (q0 : Q)
    (p : X → GetterProgram Q A R) (hp : BorelFamily p)
    (oracle : X × Q → GetterProgram BQ BA A) (ho : BorelFamily oracle)
    (fuel : X → ℕ) (hfuel : Measurable fuel) :
    BorelFamily (fun x => boundedLower (fun q => oracle (x,q)) (fuel x) (p x)) :=
  nat_select_family _ (fun n => bounded_lower_family a0 q0 n p hp oracle ho) fuel hfuel

end
end FangqingBorelBoundedPrimitiveLower
end

section
-- Source component: BorelWarmZeroFamily.lean

open MeasureTheory
namespace FangqingBorelWarmZero
open FangqingBorelGetterProgramFamily FangqingBorelWarmData FangqingBorelWarmATS
noncomputable section
set_option maxHeartbeats 4500000
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]
local instance : MeasurableSpace E := borel E
local instance : BorelSpace E := ⟨rfl⟩
local instance : MeasurableSpace (E →L[ℝ] E) := borel (E →L[ℝ] E)
local instance : BorelSpace (E →L[ℝ] E) := ⟨rfl⟩

/-- Six real inputs are (mu,Lg,A,sigma,rho,deltaY); no legality restriction is
used in the Borel extension. The two points x,y and every answer are arbitrary. -/
abbrev Input (E : Type*) := (Fin 6 → ℝ) × (E × E)

theorem actual_zero_program_family :
    BorelFamily (fun z : Input E =>
      OriginalBorelWarmReplay.OriginalZeroCurvatureSearch.zeroProgram
        (z.1 0) (z.1 1) (z.1 2) (z.1 3) (z.1 4) (z.1 5) z.2.1 z.2.2) := by
  let U := Input E × BAnswer E
  have hgrad : Measurable (fun u : U => u.2.grad) := answer_grad_measurable.comp measurable_snd
  have hLambda : Measurable (fun u : U =>
      OriginalBorelWarmReplay.OriginalZeroCurvatureSearch.initialLambda
        (u.1.1 0) (u.1.1 1) (u.1.1 2) (u.1.1 3) (u.1.1 4) u.1.2.1 u.1.2.2 u.2) := by
    unfold OriginalBorelWarmReplay.OriginalZeroCurvatureSearch.initialLambda
      OriginalBorelWarmReplay.OriginalZeroCurvatureSearch.initialBeta
      OriginalBorelWarmReplay.OriginalZeroCurvatureSearch.largeLambda
      OriginalBorelWarmReplay.OriginalBetaSearchEndpoints.betaHigh
      OriginalBorelWarmReplay.OriginalBetaSearchEndpoints.highMargin
      OriginalCoupledBetaAlgebra.lambda
    fun_prop
  have hCenter : Measurable (fun u : U =>
      OriginalBorelWarmReplay.OriginalZeroCurvatureSearch.initialCenter
        (u.1.1 0) (u.1.1 1) (u.1.1 2) (u.1.1 3) (u.1.1 4) u.1.2.1 u.1.2.2 u.2) := by
    unfold OriginalBorelWarmReplay.OriginalZeroCurvatureSearch.initialCenter
      OriginalBorelWarmReplay.OriginalZeroCurvatureSearch.initialBeta
      OriginalBorelWarmReplay.OriginalZeroCurvatureSearch.largeLambda
      OriginalBorelWarmReplay.OriginalBetaSearchEndpoints.betaHigh
      OriginalBorelWarmReplay.OriginalBetaSearchEndpoints.highMargin
      OriginalCoupledBetaAlgebra.center
    fun_prop
  have hTolerance : Measurable (fun u : U =>
      OriginalBorelWarmReplay.OriginalZeroCurvatureSearch.initialTolerance
        (u.1.1 0) (u.1.1 1) (u.1.1 2) (u.1.1 3) (u.1.1 4) u.1.2.1 u.1.2.2 u.2) := by
    unfold OriginalBorelWarmReplay.OriginalZeroCurvatureSearch.initialTolerance
      OriginalBorelWarmReplay.OriginalBetaATSUniform.uniformTolerance
      OriginalBorelWarmReplay.OriginalBetaATSUniform.uniformStepFloor CertifiedATS.stepFloor
    fun_prop
  have hRho : Measurable (fun u : U => u.1.1 4) := by fun_prop
  have hDeltaY : Measurable (fun u : U => u.1.1 5) := by fun_prop
  have hArgs : Measurable (fun u : U =>
      (OriginalBorelWarmReplay.OriginalZeroCurvatureSearch.initialCenter
          (u.1.1 0) (u.1.1 1) (u.1.1 2) (u.1.1 3) (u.1.1 4) u.1.2.1 u.1.2.2 u.2,
        (OriginalBorelWarmReplay.OriginalZeroCurvatureSearch.initialLambda
          (u.1.1 0) (u.1.1 1) (u.1.1 2) (u.1.1 3) (u.1.1 4) u.1.2.1 u.1.2.2 u.2,
          (OriginalBorelWarmReplay.OriginalZeroCurvatureSearch.initialTolerance
            (u.1.1 0) (u.1.1 1) (u.1.1 2) (u.1.1 3) (u.1.1 4) u.1.2.1 u.1.2.2 u.2,
            (u.1.1 4,u.1.1 5))))) :=
    hCenter.prodMk (hLambda.prodMk (hTolerance.prodMk (hRho.prodMk hDeltaY)))
  have hCont := precomp_family _ (actual_trial_program_family (E := E) 0) _ hArgs
  have hQuery : Measurable (fun z : Input E => (z.2.2,(1:ℝ))) :=
    (measurable_snd.snd : Measurable (fun z : Input E => z.2.2)).prodMk measurable_const
  have hall := ask_family _ hQuery _ hCont
  simpa only [OriginalBorelWarmReplay.OriginalZeroCurvatureSearch.zeroProgram] using hall

end
end FangqingBorelWarmZero
end

section
-- Source component: BorelWarmBoundedReplay.lean

open MeasureTheory
namespace FangqingBorelWarmBoundedReplay
open OriginalBetaATSTrial FangqingGetterComposition FangqingBorelGetterProgramFamily
  FangqingBorelBoundedPrimitiveLower
noncomputable section
universe u
variable {X Q A R BQ BA : Type u}

/-- A total implementation of primitive substitution. The fallback is used only
on answer streams exhausting the independently certified OUTER-query fuel. -/
def resolvedLower (oracle : Q → GetterProgram BQ BA A) (fuel : ℕ) (fallback : R)
    (p : GetterProgram Q A R) : GetterProgram BQ BA R :=
  FangqingGetterComposition.map (Sum.elim (fun _ : Unit => fallback) id)
    (boundedLower oracle fuel p)

section Borel
variable [MeasurableSpace X] [MeasurableSpace Q] [MeasurableSpace A] [MeasurableSpace R]
  [MeasurableSpace BQ] [MeasurableSpace BA]

theorem resolved_lower_family (a0 : A) (q0 : Q) (fuel : ℕ)
    (p : X → GetterProgram Q A R) (hp : BorelFamily p)
    (oracle : X × Q → GetterProgram BQ BA A) (ho : BorelFamily oracle)
    (fallback : X → R) (hf : Measurable fallback) :
    BorelFamily (fun x => resolvedLower (fun q => oracle (x,q)) fuel (fallback x) (p x)) := by
  have hb := bounded_lower_family a0 q0 fuel p hp oracle ho
  have hleft : Measurable (fun z : X × Unit => fallback z.1) := hf.comp measurable_fst
  have hright : Measurable (fun z : X × R => z.2) := measurable_snd
  have hm : Measurable (fun z : X × (Unit ⊕ R) => Sum.elim (fun _ => fallback z.1) id z.2) := by
    have hs := measurable_fun_sum (f:=Sum.elim (fun z : X × Unit => fallback z.1)
      (fun z : X × R => z.2)) hleft hright
    convert hs.comp (MeasurableEquiv.prodSumDistrib X Unit R).measurable using 1
    funext z
    rcases z with ⟨x,r⟩
    cases r <;> rfl
  simpa only [resolvedLower] using map_family _ hb _ hm
end Borel

theorem resolved_lower_execution (base : BQ → BA) (oracle : Q → GetterProgram BQ BA A)
    (p : GetterProgram Q A R) (fuel : ℕ) (fallback : R)
    (hbudget : (execute (implementedGetter base oracle) p).2 ≤ fuel) :
    execute base (resolvedLower oracle fuel fallback p) = execute base (primitiveLower oracle p) := by
  have h := (bounded_lower_actual_execution base oracle p fuel hbudget).1
  simp only [resolvedLower,execute_map,h,Sum.elim_inr,id_eq]

end
end FangqingBorelWarmBoundedReplay
end

section
-- Source component: BorelWarmSecondOrderProgram.lean

open MeasureTheory
namespace FangqingBorelWarmSecondOrder
open OriginalSaddleImplicit OriginalBetaATSTrial FangqingBorelGetterProgramFamily
  FangqingBorelWarmData FangqingBorelWarmProgramBridges FangqingBorelWarmBoundedReplay
  FangqingBorelWarmDualGetterFamily FangqingBorelDualOracleSimulator FangqingBorelDualOracleProgram
noncomputable section
set_option maxHeartbeats 6000000
universe u
variable {E F : Type u}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F] [FiniteDimensional ℝ F]
local instance : MeasurableSpace E := borel E
local instance : BorelSpace E := ⟨rfl⟩
local instance : MeasurableSpace F := borel F
local instance : BorelSpace F := ⟨rfl⟩
local instance : MeasurableSpace (Joint E F) := borel (Joint E F)
local instance : BorelSpace (Joint E F) := ⟨rfl⟩
local instance : MeasurableSpace (Joint E F →L[ℝ] Joint E F) := borel (Joint E F →L[ℝ] Joint E F)
local instance : BorelSpace (Joint E F →L[ℝ] Joint E F) := ⟨rfl⟩

abbrev Input (E F : Type*) := E × (E × F)

def positiveFuel (mu L rho D tol : ℝ) : ℕ :=
  let c := OriginalBorelWarmReplay.OriginalActualDualPositiveContraction.parameters mu L rho D
  let r := OriginalBorelWarmReplay.FangqingHysteresis.halvingCount D tol
  OriginalBorelWarmReplay.OriginalRobustTrajectory.contractionIterations c (1/2) D * r *
    OriginalBorelWarmReplay.OriginalRobustTrajectory.coefficientMaximum
      (OriginalBorelWarmReplay.OriginalRobustTrajectory.radiusGetterFactor c (1/2)) r D

noncomputable def positiveDualProgram (mu L rho D tol : ℝ) (x uInit : E) (yin : F) :=
  if 0 < D then resolvedLower
    (OriginalBorelWarmReplay.OriginalDualGetterImplementation.oracleProgram L rho x uInit)
    (positiveFuel mu L rho D tol) yin
    (OriginalBorelWarmReplay.OriginalRobustTrajectory.restartProgram
      (OriginalBorelWarmReplay.OriginalActualDualPositiveContraction.parameters mu L rho D)
      (1/2) (OriginalBorelWarmReplay.FangqingHysteresis.halvingCount D tol) D yin)
  else GetterProgram.pure yin

theorem positive_dual_program_family (mu L rho D tol : ℝ) :
    BorelFamily (fun z : Input E F => positiveDualProgram mu L rho D tol z.1 z.2.1 z.2.2) := by
  have hp := precomp_family _
    (FangqingBorelWarmTrajectory.actual_positive_restarts_family (E:=F)
      (OriginalBorelWarmReplay.OriginalActualDualPositiveContraction.parameters mu L rho D)
      (1/2) (OriginalBorelWarmReplay.FangqingHysteresis.halvingCount D tol) D)
      (fun z : Input E F => z.2.2) measurable_snd.snd
  have ho := precomp_family _ (actual_dual_getter_program_family (E:=E) (F:=F) L rho)
    (fun z : Input E F × (F×ℝ) => (z.1.1,(z.1.2.1,z.2)))
    (measurable_fst.fst.prodMk (measurable_fst.snd.fst.prodMk measurable_snd))
  have hb := resolved_lower_family (⟨0,0⟩ : BAnswer F) (0,0) (positiveFuel mu L rho D tol)
    _ hp _ ho (fun z : Input E F => z.2.2) measurable_snd.snd
  classical
  by_cases hD : 0 < D
  · simpa only [positiveDualProgram,if_pos hD] using hb
  · simpa only [positiveDualProgram,if_neg hD] using
      pure_family (Q:=Joint E F) (A:=OriginalDualOracleProgram.OracleAnswer (Joint E F))
        (fun z : Input E F => z.2.2) measurable_snd.snd

/-- Full-space Borel final primal simulator, attached to any already checked
Borel dual program. It is the original charged recovery, not a free map. -/
theorem recovery_family (L tau : ℝ)
    (p : Input E F → GetterProgram (Joint E F) (OriginalDualOracleProgram.OracleAnswer (Joint E F)) F)
    (hp : BorelFamily p) :
    BorelFamily (fun z : Input E F =>
      OriginalBorelWarmReplay.OriginalDualPrimalRecovery.program L tau z.1 z.2.1 (p z)) := by
  have hi : Measurable (fun z : Input E F × F => (z.1.1,(z.2,(z.1.2.1,tau/4)))) :=
    measurable_fst.fst.prodMk (measurable_snd.prodMk (measurable_fst.snd.fst.prodMk measurable_const))
  have hs := precomp_family _ (simulator_family (E:=E) (F:=F) L) _ hi
  have hout : Measurable (fun z : (Input E F × F) × OriginalDualOracleProgram.QueryState E F =>
      JointSliceRegularity.point z.2.u z.1.2) := by
    exact ((JointSliceRegularity.axisX (E:=E) (F:=F)).continuous.measurable.comp
      (state_u_measurable.comp measurable_snd)).add
      ((JointSliceRegularity.axisY (E:=E) (F:=F)).continuous.measurable.comp measurable_fst.snd)
  have hm := map_family _ hs _ hout
  have hb := bind_family _ hp _ hm
  simpa only [OriginalBorelWarmReplay.OriginalDualPrimalRecovery.program,bind_eq_original,map_eq_original,
    lift_query_eq_original] using hb

noncomputable def positiveWarmProgram (mu L rho D tau : ℝ) (x uInit : E) (yin : F) :=
  OriginalBorelWarmReplay.OriginalDualPrimalRecovery.program L tau x uInit
    (positiveDualProgram mu L rho D (tau/4) x uInit yin)

theorem positive_warm_program_family (mu L rho D tau : ℝ) :
    BorelFamily (fun z : Input E F => positiveWarmProgram mu L rho D tau z.1 z.2.1 z.2.2) :=
  recovery_family L tau _ (positive_dual_program_family mu L rho D (tau/4))

end
end FangqingBorelWarmSecondOrder
end

section
-- Source component: BorelWarmSecondOrderCorrectness.lean

namespace FangqingBorelWarmSecondOrder
open OriginalSaddleImplicit OriginalSaddleTransfer OriginalSaddleStability
  OriginalDualCurvature OriginalDualMinimizer
open OriginalBorelWarmReplay.OriginalBetaATSTrial
  OriginalBorelWarmReplay.OriginalRobustTrajectory
  OriginalBorelWarmReplay.OriginalDualGetterImplementation
  OriginalBorelWarmReplay.OriginalActualDualPositiveContraction
noncomputable section
set_option maxHeartbeats 6000000
universe u
variable {E F : Type u}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F] [FiniteDimensional ℝ F]

theorem actual_positive_raw_query_bound
    (J : Joint E F → ℝ) (mu L rho D tol : ℝ)
    (hmu : 0 < mu) (hL : 0 < L) (hrho : 0 < rho) (hD : 0 < D) (htol : 0 < tol)
    (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (hHess : ∀ z w : Joint E F, ‖fderiv ℝ (gradient J) z - fderiv ℝ (gradient J) w‖ ≤ rho * ‖z - w‖)
    (hsc : ∀ u : E, StrongConvexOn (Set.univ : Set F) mu (fun y => -JointSliceRegularity.curry J u y))
    (x uInit : E) (yin : F) (hwarm : ‖yin - vStar (JointSliceRegularity.curry J) L x‖ ≤ D) :
    (execute (actualGetter J L rho x uInit)
      (restartProgram (parameters mu L rho D) (1/2)
        (OriginalBorelWarmReplay.FangqingHysteresis.halvingCount D tol) D yin)).2 ≤
      positiveFuel mu L rho D tol := by
  let g := psi J L x
  let c := parameters mu L rho D
  let getter := actualGetter J L rho x uInit
  let r := OriginalBorelWarmReplay.FangqingHysteresis.halvingCount D tol
  let p := restartProgram c (1 / 2) r D yin
  have hgC2 := psi_contDiff2 J L hL hC2 hLip x
  have hgsc := psi_strongConvex J L mu hL hC2 hLip hsc x
  have hglip := psi_gradient_lipschitz J L hL hC2 hLip x
  have hgHess := psi_hessian_lipschitz J L rho hL hrho.le hC2 hLip hHess x
  have hgetter := actual_getter_accuracy J L rho hL hrho.le hC2 hLip hHess x uInit
  have H : Hypotheses g c (1 / 2) D getter :=
    ⟨parameters_common mu L rho D hmu hL hrho hD, hD, by norm_num [c, parameters],
      by norm_num, rfl, hgC2, hgsc, hglip, hgHess, hgetter⟩
  have hJ := JointSliceRegularity.differentiable_joint_of_contDiff2 J hC2
  have hmin := actual_dual_saddle_minimizes J L mu hL hmu hJ hLip hsc x
  have hvs : vStar (JointSliceRegularity.curry J) L x = RobustAHPE.globalMinimizer g :=
    RobustAHPE.globalMinimizer_unique g mu hmu (hgC2.differentiable (by norm_num)) hgsc _ hmin
  have hstart : ‖yin - RobustAHPE.globalMinimizer g‖ ≤ D := by rwa [← hvs]
  have h := actual_positive_restarts_to_accuracy H tol htol yin hstart
  exact h.2.2.1


theorem positive_dual_execution_eq_original
    (J : Joint E F → ℝ) (mu L rho D tol : ℝ)
    (hmu : 0 < mu) (hL : 0 < L) (hrho : 0 < rho) (htol : 0 < tol)
    (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (hHess : ∀ z w : Joint E F, ‖fderiv ℝ (gradient J) z - fderiv ℝ (gradient J) w‖ ≤ rho * ‖z - w‖)
    (hsc : ∀ u : E, StrongConvexOn (Set.univ : Set F) mu (fun y => -JointSliceRegularity.curry J u y))
    (x uInit : E) (yin : F) (hwarm : ‖yin - vStar (JointSliceRegularity.curry J) L x‖ ≤ D) :
    execute (OriginalDualOracleProgram.actualOracle J) (positiveDualProgram mu L rho D tol x uInit yin) =
      execute (OriginalDualOracleProgram.actualOracle J)
        (OriginalBorelWarmReplay.OriginalActualDualSecondOrderWarm.dualProgram mu L rho D tol x uInit yin) := by
  classical
  by_cases hD : 0 < D
  · let oracle : F × ℝ → OriginalBetaATSTrial.GetterProgram (Joint E F)
      (OriginalDualOracleProgram.OracleAnswer (Joint E F)) (OriginalBorelWarmReplay.OriginalBetaATSTrial.Answer F) := OriginalBorelWarmReplay.OriginalDualGetterImplementation.oracleProgram L rho x uInit
    let p := restartProgram (parameters mu L rho D) (1/2)
      (OriginalBorelWarmReplay.FangqingHysteresis.halvingCount D tol) D yin
    have hb := actual_positive_raw_query_bound J mu L rho D tol hmu hL hrho hD htol
      hC2 hLip hHess hsc x uInit yin hwarm
    have heq : _root_.FangqingGetterComposition.implementedGetter (OriginalDualOracleProgram.actualOracle J) oracle =
        actualGetter J L rho x uInit := by
      funext q
      exact congrArg Prod.fst (OriginalBorelWarmReplay.OriginalBetaATSTrial.execute_eq_original _ _).symm
    have hb' : (_root_.OriginalBetaATSTrial.execute
        (_root_.FangqingGetterComposition.implementedGetter (OriginalDualOracleProgram.actualOracle J) oracle) p).2 ≤
          positiveFuel mu L rho D tol := by
      rw [heq,← OriginalBorelWarmReplay.OriginalBetaATSTrial.execute_eq_original]
      exact hb
    have h := FangqingBorelWarmBoundedReplay.resolved_lower_execution
      (OriginalDualOracleProgram.actualOracle J) oracle p (positiveFuel mu L rho D tol) yin hb'
    simpa only [positiveDualProgram,OriginalBorelWarmReplay.OriginalActualDualSecondOrderWarm.dualProgram,
      if_pos hD,FangqingBorelWarmProgramBridges.primitive_lower_eq_original,
      OriginalBorelWarmReplay.OriginalBetaATSTrial.execute_eq_original] using h
  · simp only [positiveDualProgram,OriginalBorelWarmReplay.OriginalActualDualSecondOrderWarm.dualProgram,if_neg hD]

theorem positive_warm_execution_eq_original
    (J : Joint E F → ℝ) (mu L rho D tau : ℝ)
    (hmu : 0 < mu) (hL : 0 < L) (hrho : 0 < rho) (htau : 0 < tau)
    (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (hHess : ∀ z w : Joint E F, ‖fderiv ℝ (gradient J) z - fderiv ℝ (gradient J) w‖ ≤ rho * ‖z - w‖)
    (hsc : ∀ u : E, StrongConvexOn (Set.univ : Set F) mu (fun y => -JointSliceRegularity.curry J u y))
    (x uInit : E) (yin : F) (hwarm : ‖yin - vStar (JointSliceRegularity.curry J) L x‖ ≤ D) :
    execute (OriginalDualOracleProgram.actualOracle J) (positiveWarmProgram mu L rho D tau x uInit yin) =
      execute (OriginalDualOracleProgram.actualOracle J)
        (OriginalBorelWarmReplay.OriginalActualDualSecondOrderWarm.warmProgram mu L rho D tau x uInit yin) := by
  have hd := positive_dual_execution_eq_original J mu L rho D (tau/4) hmu hL hrho (by positivity)
    hC2 hLip hHess hsc x uInit yin hwarm
  simp only [positiveWarmProgram,OriginalBorelWarmReplay.OriginalActualDualSecondOrderWarm.warmProgram,
    OriginalBorelWarmReplay.OriginalDualPrimalRecovery.program,
    OriginalBorelWarmReplay.FangqingGetterComposition.execute_bind,hd]


end
end FangqingBorelWarmSecondOrder
end

section
-- Source component: BorelWarmZeroSecondOrderProgram.lean

open MeasureTheory
namespace FangqingBorelWarmSecondOrder
open OriginalSaddleImplicit OriginalBetaATSTrial FangqingBorelGetterProgramFamily
  FangqingBorelWarmData FangqingBorelWarmProgramBridges FangqingBorelWarmBoundedReplay
  FangqingBorelWarmDualGetterFamily FangqingBorelDualOracleSimulator FangqingBorelDualOracleProgram
noncomputable section
set_option maxHeartbeats 6000000
universe u
variable {E F : Type u}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F] [FiniteDimensional ℝ F]
local instance : MeasurableSpace E := borel E
local instance : BorelSpace E := ⟨rfl⟩
local instance : MeasurableSpace F := borel F
local instance : BorelSpace F := ⟨rfl⟩
local instance : MeasurableSpace (Joint E F) := borel (Joint E F)
local instance : BorelSpace (Joint E F) := ⟨rfl⟩
local instance : MeasurableSpace (Joint E F →L[ℝ] Joint E F) := borel (Joint E F →L[ℝ] Joint E F)
local instance : BorelSpace (Joint E F →L[ℝ] Joint E F) := ⟨rfl⟩

noncomputable def zeroDualProgram (mu L tol : ℝ) (x uInit : E) (yin : F) :=
  resolvedLower (OriginalBorelWarmReplay.OriginalDualGetterImplementation.oracleProgram L 0 x uInit)
    3 (OriginalBorelWarmReplay.OriginalBetaATSTrial.TrialResult.stop yin)
    (OriginalBorelWarmReplay.OriginalZeroCurvatureDualWarm.dualProgram mu L tol yin)

theorem zero_dual_program_family (mu L tol : ℝ) :
    BorelFamily (fun z : Input E F => zeroDualProgram mu L tol z.1 z.2.1 z.2.2) := by
  have hi : Measurable (fun z : Input E F =>
      ((![mu,2*L,1,1/4,mu*tol,mu*tol/8] : Fin 6 → ℝ),(z.2.2,z.2.2))) :=
    measurable_const.prodMk (measurable_snd.snd.prodMk measurable_snd.snd)
  have hp := precomp_family _ (FangqingBorelWarmZero.actual_zero_program_family (E:=F)) _ hi
  have ho := precomp_family _ (actual_dual_getter_program_family (E:=E) (F:=F) L 0)
    (fun z : Input E F × (F×ℝ) => (z.1.1,(z.1.2.1,z.2)))
    (measurable_fst.fst.prodMk (measurable_fst.snd.fst.prodMk measurable_snd))
  have hb := resolved_lower_family (⟨0,0⟩ : BAnswer F) (0,0) 3 _ hp _ ho
    (fun z : Input E F => (.stop z.2.2 : BTrial F))
    (FangqingBorelWarmATS.trial_stop_measurable.comp measurable_snd.snd)
  simpa [zeroDualProgram,OriginalBorelWarmReplay.OriginalZeroCurvatureDualWarm.dualProgram] using hb

theorem zero_recovery_family (L tau : ℝ) :
    BorelFamily (fun z : Input E F × BTrial F =>
      OriginalBorelWarmReplay.OriginalZeroCurvatureDualWarm.recoverProgram L tau z.1.1 z.1.2.1 z.1.2.2 z.2) := by
  have hi : Measurable (fun z : Input E F × F => (z.1.1,(z.2,(z.1.2.1,tau/4)))) :=
    measurable_fst.fst.prodMk (measurable_snd.prodMk (measurable_fst.snd.fst.prodMk measurable_const))
  have hs := precomp_family _ (simulator_family (E:=E) (F:=F) L) _ hi
  have hout : Measurable (fun z : (Input E F × F) × OriginalDualOracleProgram.QueryState E F =>
      JointSliceRegularity.point z.2.u z.1.2) :=
    ((JointSliceRegularity.axisX (E:=E) (F:=F)).continuous.measurable.comp
      (state_u_measurable.comp measurable_snd)).add
      ((JointSliceRegularity.axisY (E:=E) (F:=F)).continuous.measurable.comp measurable_fst.snd)
  have hm := map_family _ hs _ hout
  have hf := pure_family (Q:=Joint E F) (A:=OriginalDualOracleProgram.OracleAnswer (Joint E F))
    (fun z : Input E F × (F × BAnswer F) => JointSliceRegularity.point z.1.2.1 z.1.2.2)
    (((JointSliceRegularity.axisX (E:=E) (F:=F)).continuous.measurable.comp measurable_fst.snd.fst).add
      ((JointSliceRegularity.axisY (E:=E) (F:=F)).continuous.measurable.comp measurable_fst.snd.snd))
  have h := FangqingBorelWarmEncodedCases.encoded_case_family trialEquiv _ _ hm hf
  convert h using 1
  funext z
  rcases z with ⟨s,r⟩
  cases r <;> simp only [OriginalBorelWarmReplay.OriginalZeroCurvatureDualWarm.recoverProgram,
    map_eq_original,lift_query_eq_original] <;> rfl

noncomputable def zeroWarmProgram (mu L tau : ℝ) (x uInit : E) (yin : F) :=
  FangqingGetterComposition.bind (zeroDualProgram mu L (tau/4) x uInit yin)
    (OriginalBorelWarmReplay.OriginalZeroCurvatureDualWarm.recoverProgram L tau x uInit yin)

theorem zero_warm_program_family (mu L tau : ℝ) :
    BorelFamily (fun z : Input E F => zeroWarmProgram mu L tau z.1 z.2.1 z.2.2) :=
  bind_family _ (zero_dual_program_family mu L (tau/4)) _ (zero_recovery_family L tau)

end
end FangqingBorelWarmSecondOrder
end

section
-- Source component: BorelWarmZeroSecondOrderCorrectness.lean

namespace FangqingBorelWarmSecondOrder
open OriginalSaddleImplicit
open OriginalBorelWarmReplay.OriginalBetaATSTrial
  OriginalBorelWarmReplay.OriginalZeroCurvatureSearch
noncomputable section
set_option maxHeartbeats 6000000
universe u
variable {E F : Type u}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F] [FiniteDimensional ℝ F]

theorem zero_raw_query_bound (getter : F × ℝ → Answer F)
    (mu L tol : ℝ) (yin : F) :
    (execute getter (OriginalBorelWarmReplay.OriginalZeroCurvatureDualWarm.dualProgram mu L tol yin)).2 ≤ 3 := by
  unfold OriginalBorelWarmReplay.OriginalZeroCurvatureDualWarm.dualProgram zeroProgram
  simp only [execute]
  have h := trial_getter_calls getter 0
    (initialLambda mu (2*L) 1 (1/4) (mu*tol) yin yin (getter (yin,1)))
    (initialTolerance mu (2*L) 1 (1/4) (mu*tol) yin yin (getter (yin,1)))
    (mu*tol) (mu*tol/8)
    (initialCenter mu (2*L) 1 (1/4) (mu*tol) yin yin (getter (yin,1)))
  omega

theorem zero_dual_execution_eq_original
    (J : Joint E F → ℝ) (mu L tol : ℝ) (x uInit : E) (yin : F) :
    execute (OriginalDualOracleProgram.actualOracle J) (zeroDualProgram mu L tol x uInit yin) =
      execute (OriginalDualOracleProgram.actualOracle J)
        (OriginalBorelWarmReplay.OriginalZeroCurvatureDualWarm.dualOriginalProgram mu L tol x uInit yin) := by
  let oracle := OriginalBorelWarmReplay.OriginalDualGetterImplementation.oracleProgram (F:=F) L 0 x uInit
  let p := OriginalBorelWarmReplay.OriginalZeroCurvatureDualWarm.dualProgram mu L tol yin
  have hb := zero_raw_query_bound
    (_root_.FangqingGetterComposition.implementedGetter (OriginalDualOracleProgram.actualOracle J) oracle) mu L tol yin
  have hb' : (_root_.OriginalBetaATSTrial.execute
      (_root_.FangqingGetterComposition.implementedGetter (OriginalDualOracleProgram.actualOracle J) oracle) p).2 ≤ 3 := by
    rwa [← execute_eq_original]
  have h := FangqingBorelWarmBoundedReplay.resolved_lower_execution
    (OriginalDualOracleProgram.actualOracle J) oracle p 3 (.stop yin) hb'
  simpa only [zeroDualProgram,OriginalBorelWarmReplay.OriginalZeroCurvatureDualWarm.dualOriginalProgram,
    FangqingBorelWarmProgramBridges.primitive_lower_eq_original,execute_eq_original] using h

theorem zero_warm_execution_eq_original
    (J : Joint E F → ℝ) (mu L tau : ℝ) (x uInit : E) (yin : F) :
    execute (OriginalDualOracleProgram.actualOracle J) (zeroWarmProgram mu L tau x uInit yin) =
      execute (OriginalDualOracleProgram.actualOracle J)
        (OriginalBorelWarmReplay.OriginalZeroCurvatureDualWarm.warmProgram mu L tau x uInit yin) := by
  have hd := zero_dual_execution_eq_original J mu L (tau/4) x uInit yin
  simp only [zeroWarmProgram,OriginalBorelWarmReplay.OriginalZeroCurvatureDualWarm.warmProgram,
    FangqingBorelWarmProgramBridges.bind_eq_original,execute_eq_original,
    _root_.FangqingGetterComposition.execute_bind] at hd ⊢
  rw [hd]

end
end FangqingBorelWarmSecondOrder
end

section
-- Source component: BorelWarmDyadicRounding.lean

open MeasureTheory
namespace OriginalWarmDyadicRounding
noncomputable section
set_option maxHeartbeats 3000000

def dyadic (k : ℤ) : ℝ := (2:ℝ)^(k:ℝ)
def upperIndex (D : ℝ) : ℤ := Int.ceil (Real.logb 2 D)
def lowerIndex (tau : ℝ) : ℤ := Int.floor (Real.logb 2 tau)
def upper (D : ℝ) : ℝ := dyadic (upperIndex D)
def lower (tau : ℝ) : ℝ := dyadic (lowerIndex tau)

theorem dyadic_positive (k : ℤ) : 0 < dyadic k := Real.rpow_pos_of_pos (by norm_num) _

theorem upper_index_measurable : Measurable upperIndex := by
  unfold upperIndex Real.logb
  exact Int.measurable_ceil.comp (Real.measurable_log.div_const _)

theorem lower_index_measurable : Measurable lowerIndex := by
  unfold lowerIndex Real.logb
  exact Int.measurable_floor.comp (Real.measurable_log.div_const _)

theorem upper_measurable : Measurable upper :=
  (measurable_of_countable dyadic).comp upper_index_measurable

theorem lower_measurable : Measurable lower :=
  (measurable_of_countable dyadic).comp lower_index_measurable

theorem upper_bounds (D : ℝ) (hD : 0 < D) : D ≤ upper D ∧ upper D ≤ 2*D := by
  have hlog : (2:ℝ)^(Real.logb 2 D) = D := Real.rpow_logb (by norm_num) (by norm_num) hD
  have hl : Real.logb 2 D ≤ (upperIndex D : ℝ) := Int.le_ceil _
  have hu : (upperIndex D : ℝ) ≤ Real.logb 2 D+1 := (Int.ceil_lt_add_one _).le
  have hlow := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤2) hl
  have hhigh := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤2) hu
  rw [Real.rpow_add (by norm_num : (0:ℝ)<2),Real.rpow_one,hlog] at hhigh
  exact ⟨by simpa only [hlog,upper,dyadic] using hlow,
    by simpa only [upper,dyadic,mul_comm] using hhigh⟩

theorem lower_bounds (tau : ℝ) (ht : 0 < tau) : tau/2 ≤ lower tau ∧ lower tau ≤ tau := by
  have hlog : (2:ℝ)^(Real.logb 2 tau) = tau := Real.rpow_logb (by norm_num) (by norm_num) ht
  have hl : (lowerIndex tau : ℝ) ≤ Real.logb 2 tau := Int.floor_le _
  have hu : Real.logb 2 tau ≤ (lowerIndex tau : ℝ)+1 := (Int.lt_floor_add_one _).le
  have hlow := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤2) hl
  have hhigh := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤2) hu
  rw [hlog,Real.rpow_add (by norm_num : (0:ℝ)<2),Real.rpow_one] at hhigh
  constructor
  · change tau/2 ≤ (2:ℝ)^(lowerIndex tau:ℝ)
    linarith
  · simpa only [hlog,lower,dyadic] using hlow

theorem upper_abs_log_bound (D : ℝ) (hD : 0 < D) :
    |Real.log (upper D)| ≤ |Real.log D|+Real.log 2 := by
  have hb := upper_bounds D hD
  have hu : 0 < upper D := dyadic_positive _
  have hlo := Real.log_le_log hD hb.1
  have hhi := Real.log_le_log hu hb.2
  rw [Real.log_mul (by norm_num : (2:ℝ)≠0) (ne_of_gt hD)] at hhi
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  rw [abs_le]
  constructor <;> nlinarith [le_abs_self (Real.log D),neg_abs_le (Real.log D)]

theorem lower_abs_log_bound (tau : ℝ) (ht : 0 < tau) :
    |Real.log (lower tau)| ≤ |Real.log tau|+Real.log 2 := by
  have hb := lower_bounds tau ht
  have hu : 0 < lower tau := dyadic_positive _
  have hlo := Real.log_le_log (div_pos ht (by norm_num)) hb.1
  have hhi := Real.log_le_log hu hb.2
  rw [Real.log_div (ne_of_gt ht) (by norm_num : (2:ℝ)≠0)] at hlo
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  rw [abs_le]
  constructor <;> nlinarith [le_abs_self (Real.log tau),neg_abs_le (Real.log tau)]

/-- Explicit universal factor for the SAME min of first- and second-order
scales after rounding the warm radius upward. -/
theorem rounded_minimum_factor_bound (mu L rho D : ℝ)
    (hmu : 0 < mu) (hrho : 0 ≤ rho) (hD : 0 < D) :
    1+min (Real.sqrt (L/mu)) ((rho*upper D/mu)^(2/7:ℝ)) ≤
      2*(1+min (Real.sqrt (L/mu)) ((rho*D/mu)^(2/7:ℝ))) := by
  have harg : rho*upper D/mu ≤ 2*(rho*D/mu) := by
    have hh := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (upper_bounds D hD).2 hrho) hmu.le
    calc
      _ ≤ rho * (2*D) / mu := hh
      _ = _ := by ring
  have hu0 : 0 < upper D := dyadic_positive _
  have ha0 : 0 ≤ rho*upper D/mu := by positivity
  have hb0 : 0 ≤ rho*D/mu := by positivity
  have hp := Real.rpow_le_rpow ha0 harg (by norm_num : (0:ℝ)≤2/7)
  rw [Real.mul_rpow (by norm_num : (0:ℝ)≤2) hb0] at hp
  have hc : (2:ℝ)^(2/7:ℝ) ≤ 2 := by
    have hh := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤2)
      (by norm_num : (2/7:ℝ)≤1)
    simpa only [Real.rpow_one] using hh
  have hb : (rho*upper D/mu)^(2/7:ℝ) ≤ 2*(rho*D/mu)^(2/7:ℝ) :=
    hp.trans (mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hb0 _))
  have hs := Real.sqrt_nonneg (L/mu)
  have hm := min_le_min (show Real.sqrt (L/mu) ≤ 2*Real.sqrt (L/mu) by linarith) hb
  rw [← mul_min_of_nonneg _ _ (by norm_num : (0:ℝ)≤2)] at hm
  linarith

end
end OriginalWarmDyadicRounding
end

section
-- Source component: BorelCountableProgramSelection.lean

open MeasureTheory
namespace FangqingBorelCountableSelection
open OriginalBetaATSTrial FangqingBorelGetterProgramFamily
noncomputable section
variable {I X Q A R : Type*} [Countable I] [MeasurableSpace I] [MeasurableSingletonClass I]
  [MeasurableSpace X] [MeasurableSpace Q] [MeasurableSpace A] [MeasurableSpace R]

theorem measurable_countable_select (f : I → X → R) (hf : ∀ i, Measurable (f i))
    (i : X → I) (hi : Measurable i) : Measurable (fun x => f (i x) x) := by
  have h : Measurable (fun z : X × I => f z.2 z.1) :=
    measurable_from_prod_countable_left (fun j => hf j)
  exact h.comp (measurable_id.prodMk hi)

theorem countable_select_family (p : I → X → GetterProgram Q A R)
    (hp : ∀ i, BorelFamily (p i)) (i : X → I) (hi : Measurable i) :
    BorelFamily (fun x => p (i x) x) := by
  exact ⟨measurable_countable_select _ (fun j => (hp j).result)
      (fun z : X × (ℕ → A) => i z.1) (hi.comp measurable_fst),
    measurable_countable_select _ (fun j => (hp j).count)
      (fun z : X × (ℕ → A) => i z.1) (hi.comp measurable_fst),
    fun q0 n => measurable_countable_select _ (fun j => (hp j).request q0 n)
      (fun z : X × (ℕ → A) => i z.1) (hi.comp measurable_fst)⟩

end
end FangqingBorelCountableSelection
end

section
-- Source component: BorelWarmDyadicSecondOrder.lean

open MeasureTheory
namespace FangqingBorelWarmSecondOrder
open OriginalSaddleImplicit OriginalBetaATSTrial FangqingBorelGetterProgramFamily
  FangqingBorelWarmData OriginalWarmDyadicRounding FangqingBorelCountableSelection
noncomputable section
set_option maxHeartbeats 6000000
universe u
variable {E F : Type u}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F] [FiniteDimensional ℝ F]
local instance : MeasurableSpace E := borel E
local instance : BorelSpace E := ⟨rfl⟩
local instance : MeasurableSpace F := borel F
local instance : BorelSpace F := ⟨rfl⟩
local instance : MeasurableSpace (Joint E F) := borel (Joint E F)
local instance : BorelSpace (Joint E F) := ⟨rfl⟩
local instance : MeasurableSpace (Joint E F →L[ℝ] Joint E F) := borel (Joint E F →L[ℝ] Joint E F)
local instance : BorelSpace (Joint E F →L[ℝ] Joint E F) := ⟨rfl⟩

abbrev WarmInput (E F : Type*) := (ℝ × ℝ) × Input E F

noncomputable def fixedProgram (mu L rho D tau : ℝ) (x uInit : E) (yin : F) :=
  if 0 < rho then positiveWarmProgram mu L rho D tau x uInit yin
  else zeroWarmProgram mu L tau x uInit yin

theorem fixed_program_family (mu L rho D tau : ℝ) :
    BorelFamily (fun z : Input E F => fixedProgram mu L rho D tau z.1 z.2.1 z.2.2) := by
  classical
  by_cases h : 0 < rho
  · simpa only [fixedProgram,if_pos h] using positive_warm_program_family (E:=E) (F:=F) mu L rho D tau
  · simpa only [fixedProgram,if_neg h] using zero_warm_program_family (E:=E) (F:=F) mu L tau

/-- Public dyadic rounding makes the complete SO algorithm jointly Borel in
changing radius and tolerance. Invalid radii extend by the exact-dual case. -/
noncomputable def dyadicProgram (mu L rho D tau : ℝ) (x uInit : E) (yin : F) :=
  fixedProgram mu L rho (if 0 < D then upper D else 0) (lower tau) x uInit yin

theorem actual_dyadic_second_order_program_family (mu L rho : ℝ) :
    BorelFamily (fun z : WarmInput E F => dyadicProgram mu L rho z.1.1 z.1.2 z.2.1 z.2.2.1 z.2.2.2) := by
  have hp : ∀ ij : ℤ × ℤ, BorelFamily (fun z : WarmInput E F =>
      fixedProgram mu L rho (dyadic ij.1) (dyadic ij.2) z.2.1 z.2.2.1 z.2.2.2) := by
    intro ij
    exact precomp_family _ (fixed_program_family mu L rho (dyadic ij.1) (dyadic ij.2)) _ measurable_snd
  have hi : Measurable (fun z : WarmInput E F => (upperIndex z.1.1,lowerIndex z.1.2)) :=
    (upper_index_measurable.comp measurable_fst.fst).prodMk
      (lower_index_measurable.comp measurable_fst.snd)
  have hp' := countable_select_family _ hp _ hi
  have hz : ∀ i : ℤ, BorelFamily (fun z : WarmInput E F =>
      fixedProgram mu L rho 0 (dyadic i) z.2.1 z.2.2.1 z.2.2.2) := by
    intro i
    exact precomp_family _ (fixed_program_family mu L rho 0 (dyadic i)) _ measurable_snd
  have hz' := countable_select_family _ hz (fun z : WarmInput E F => lowerIndex z.1.2)
    (lower_index_measurable.comp measurable_fst.snd)
  have ht : MeasurableSet {z : WarmInput E F | 0 < z.1.1} :=
    measurableSet_lt measurable_const measurable_fst.fst
  have h := ite_family (fun z : WarmInput E F => 0 < z.1.1) ht _ _ hp' hz'
  convert h using 1
  funext z
  unfold dyadicProgram upper lower
  split_ifs <;> rfl

end
end FangqingBorelWarmSecondOrder
end

section
-- Source component: BorelWarmFirstOrderFamily.lean

open MeasureTheory Function
namespace FangqingBorelWarmFirstOrder
open OriginalSaddleImplicit OriginalBetaATSTrial FangqingBorelGetterProgramFamily
  FangqingBorelDualOracleProgram FangqingBorelDualOracleSimulator
  FangqingBorelWarmDualGetterFamily
noncomputable section
set_option maxHeartbeats 6000000

variable {Q A R S : Type*}

theorem lift_query_qbind (p : OriginalDualOracleProgram.QueryProgram Q A R)
    (k : R → OriginalDualOracleProgram.QueryProgram Q A S) :
    OriginalBorelWarmReplay.OriginalDualGetterImplementation.liftQuery
      (OriginalBorelWarmReplay.CertifiedFirstOrderLowering.qbind p k) =
    FangqingGetterComposition.bind
      (OriginalBorelWarmReplay.OriginalDualGetterImplementation.liftQuery p)
      (fun r => OriginalBorelWarmReplay.OriginalDualGetterImplementation.liftQuery (k r)) := by
  induction p with
  | pure r => rfl
  | ask q cont ih =>
      simp only [OriginalBorelWarmReplay.CertifiedFirstOrderLowering.qbind,
        OriginalBorelWarmReplay.OriginalDualGetterImplementation.liftQuery,FangqingGetterComposition.bind]
      congr 1
      funext a
      exact ih a

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F] [FiniteDimensional ℝ F]
local instance : MeasurableSpace E := borel E
local instance : BorelSpace E := ⟨rfl⟩
local instance : MeasurableSpace F := borel F
local instance : BorelSpace F := ⟨rfl⟩
local instance : MeasurableSpace (Joint E F) := borel (Joint E F)
local instance : BorelSpace (Joint E F) := ⟨rfl⟩
local instance : MeasurableSpace (Joint E F →L[ℝ] Joint E F) := borel (Joint E F →L[ℝ] Joint E F)
local instance : BorelSpace (Joint E F →L[ℝ] Joint E F) := ⟨rfl⟩

abbrev FOState (D : Type*) := OriginalBorelWarmReplay.CertifiedFirstOrder.State D

def stateEncode (s : FOState F) : ℝ × (F × F) := (s.weight,(s.x,s.y))
instance foStateMeasurableSpace : MeasurableSpace (FOState F) := MeasurableSpace.comap stateEncode inferInstance

theorem state_encode_measurable : Measurable (stateEncode (F := F)) := Measurable.of_comap_le le_rfl

theorem state_weight_measurable : Measurable (fun s : FOState F => s.weight) := measurable_fst.comp state_encode_measurable

theorem state_x_measurable : Measurable (fun s : FOState F => s.x) := measurable_snd.fst.comp state_encode_measurable

theorem state_y_measurable : Measurable (fun s : FOState F => s.y) := measurable_snd.snd.comp state_encode_measurable

theorem state_mk_measurable {X : Type*} [MeasurableSpace X]
    (a : X → ℝ) (x y : X → F) (ha : Measurable a) (hx : Measurable x) (hy : Measurable y) :
    Measurable (fun z => (⟨a z,x z,y z⟩ : FOState F)) := by
  apply measurable_comap_iff.mpr
  exact ha.prodMk (hx.prodMk hy)

theorem center_measurable (lam : ℝ) :
    Measurable (OriginalBorelWarmReplay.CertifiedFirstOrder.center (E := F) lam) := by
  have hw := state_weight_measurable (F := F)
  have hx := state_x_measurable (F := F)
  have hy := state_y_measurable (F := F)
  unfold OriginalBorelWarmReplay.CertifiedFirstOrder.center OriginalBorelWarmReplay.CertifiedFirstOrder.increment
  fun_prop

theorem next_measurable (lam : ℝ) :
    Measurable (fun z : FOState F × (F × F) =>
      OriginalBorelWarmReplay.CertifiedFirstOrder.next lam z.1 z.2.1 z.2.2) := by
  have hw : Measurable (fun z : FOState F × (F × F) => z.1.weight) :=
    (state_weight_measurable (F := F)).comp measurable_fst
  have hx : Measurable (fun z : FOState F × (F × F) => z.1.x) :=
    (state_x_measurable (F := F)).comp measurable_fst
  have hy : Measurable (fun z : FOState F × (F × F) => OriginalBorelWarmReplay.CertifiedFirstOrder.center lam z.1) :=
    (center_measurable (F := F) lam).comp measurable_fst
  unfold OriginalBorelWarmReplay.CertifiedFirstOrder.next
  apply state_mk_measurable
  · unfold OriginalBorelWarmReplay.CertifiedFirstOrder.increment
    fun_prop
  · unfold OriginalBorelWarmReplay.CertifiedFirstOrder.increment
    fun_prop
  · fun_prop

theorem result_point_measurable :
    Measurable (OriginalBorelWarmReplay.CertifiedFirstOrder.resultPoint (E := F)) :=
  measurable_id.sumElim state_y_measurable

abbrev GradientInput (E F : Type*) := (E × E) × (F × ℝ)

theorem actual_gradient_getter_family (L rho : ℝ) :
    BorelFamily (fun z : GradientInput E F =>
      OriginalBorelWarmReplay.OriginalDualGetterImplementation.liftQuery
        (OriginalBorelWarmReplay.OriginalDualFirstOrder.gradientGetter L rho z.1.1 z.1.2 z.2.1 z.2.2)) := by
  have ha : Measurable (fun z : GradientInput E F =>
      (z.1.1,(z.2.1,(z.1.2,min 1 (z.2.2/(1+3*L+4*rho)))))) := by fun_prop
  have hs := precomp_family _ (simulator_family (E := E) (F := F) L) _ ha
  have hm := map_family _ hs (fun z : GradientInput E F × OriginalDualOracleProgram.QueryState E F =>
      OriginalDualOracleProgram.gradientOutput z.2) (gradient_output_measurable.comp measurable_snd)
  simp_rw [OriginalBorelWarmReplay.OriginalDualFirstOrder.gradientGetter,lift_query_qbind]
  simpa only [lift_query_eq_original,FangqingGetterComposition.map,OriginalDualGetterImplementation.liftQuery] using hm

end
end FangqingBorelWarmFirstOrder
end

section
-- Source component: BorelWarmFirstOrderContraction.lean

open MeasureTheory Function
namespace FangqingBorelWarmFirstOrder
open OriginalSaddleImplicit OriginalBetaATSTrial FangqingBorelGetterProgramFamily
  FangqingBorelDualOracleProgram FangqingBorelDualOracleSimulator
  FangqingBorelWarmDualGetterFamily
noncomputable section
set_option maxHeartbeats 6000000
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F] [FiniteDimensional ℝ F]
local instance : MeasurableSpace E := borel E
local instance : BorelSpace E := ⟨rfl⟩
local instance : MeasurableSpace F := borel F
local instance : BorelSpace F := ⟨rfl⟩
local instance : MeasurableSpace (Joint E F) := borel (Joint E F)
local instance : BorelSpace (Joint E F) := ⟨rfl⟩
local instance : MeasurableSpace (Joint E F →L[ℝ] Joint E F) := borel (Joint E F →L[ℝ] Joint E F)
local instance : BorelSpace (Joint E F →L[ℝ] Joint E F) := ⟨rfl⟩

abbrev BaseProgram (E F R : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] :=
  GetterProgram (Joint E F) (OriginalDualOracleProgram.OracleAnswer (Joint E F)) R

def contractionLoop (mu L rho : ℝ) (n : ℕ) (D : ℝ) (x u0 : E) (s : FOState F) :
    BaseProgram E F (Sum F (FOState F)) :=
  OriginalBorelWarmReplay.OriginalDualGetterImplementation.liftQuery
    (OriginalBorelWarmReplay.CertifiedFirstOrderLowering.lower
      (OriginalBorelWarmReplay.OriginalDualFirstOrder.gradientGetter L rho x u0)
      (OriginalBorelWarmReplay.CertifiedFirstOrder.contractionProgram mu (2*L) D n s))

theorem contraction_loop_succ (mu L rho : ℝ) (n : ℕ) (D : ℝ) (x u0 : E) (s : FOState F) :
    contractionLoop mu L rho (n+1) D x u0 s =
      let lam := (2*(2*L))⁻¹
      let z := OriginalBorelWarmReplay.CertifiedFirstOrder.center lam s
      let tol := OriginalBorelWarmReplay.CertifiedFirstOrder.centerTolerance mu D
      FangqingGetterComposition.bind
        (OriginalBorelWarmReplay.OriginalDualGetterImplementation.liftQuery
          (OriginalBorelWarmReplay.OriginalDualFirstOrder.gradientGetter L rho x u0 z tol))
        (fun gz => if ‖gz‖+tol ≤ mu*D/2 then .pure (.inl z) else
          let y := z-lam • gz
          let dt := OriginalBorelWarmReplay.RobustAHPE.outputGradientTolerance mu lam (3/64) ‖y-z‖
          FangqingGetterComposition.bind
            (OriginalBorelWarmReplay.OriginalDualGetterImplementation.liftQuery
              (OriginalBorelWarmReplay.OriginalDualFirstOrder.gradientGetter L rho x u0 y dt))
            (fun vy => contractionLoop mu L rho n D x u0
              (OriginalBorelWarmReplay.CertifiedFirstOrder.next lam s gz vy))) := by
  dsimp only [contractionLoop,OriginalBorelWarmReplay.CertifiedFirstOrder.contractionProgram,
    OriginalBorelWarmReplay.CertifiedFirstOrderLowering.lower]
  rw [lift_query_qbind]
  congr 1
  funext gz
  by_cases ht : ‖gz‖+OriginalBorelWarmReplay.CertifiedFirstOrder.centerTolerance mu D ≤ mu*D/2
  · simp only [if_pos ht,OriginalBorelWarmReplay.CertifiedFirstOrderLowering.lower,
      OriginalBorelWarmReplay.OriginalDualGetterImplementation.liftQuery]
  · simp only [if_neg ht,OriginalBorelWarmReplay.CertifiedFirstOrderLowering.lower,lift_query_qbind]

abbrev ContractInput (E F : Type*) := (ℝ × (E × E)) × FOState F

theorem actual_contraction_loop_family (mu L rho : ℝ) (n : ℕ) :
    BorelFamily (fun p : ContractInput E F => contractionLoop mu L rho n p.1.1 p.1.2.1 p.1.2.2 p.2) := by
  induction n with
  | zero =>
      exact pure_family (Q := Joint E F) (A := OriginalDualOracleProgram.OracleAnswer (Joint E F))
        (fun p : ContractInput E F => (Sum.inr p.2 : Sum F (FOState F))) (measurable_inr.comp measurable_snd)
  | succ n ih =>
      let X := ContractInput E F
      let V := X × F
      let W := V × F
      let lam := (2*(2*L))⁻¹
      let z : X → F := fun p => OriginalBorelWarmReplay.CertifiedFirstOrder.center lam p.2
      let tol : X → ℝ := fun p => OriginalBorelWarmReplay.CertifiedFirstOrder.centerTolerance mu p.1.1
      let y : V → F := fun v => z v.1-lam • v.2
      let dt : V → ℝ := fun v => OriginalBorelWarmReplay.RobustAHPE.outputGradientTolerance mu lam (3/64) ‖y v-z v.1‖
      have hz : Measurable z := (center_measurable lam).comp measurable_snd
      have htol : Measurable tol := by unfold tol OriginalBorelWarmReplay.CertifiedFirstOrder.centerTolerance; fun_prop
      have hy : Measurable y := (hz.comp measurable_fst).sub (measurable_const.smul measurable_snd)
      have hdt : Measurable dt := by
        unfold dt OriginalBorelWarmReplay.RobustAHPE.outputGradientTolerance
        exact (measurable_const.mul ((hy.sub (hz.comp measurable_fst)).norm)).mul measurable_const
      have hfirst := precomp_family _ (actual_gradient_getter_family (E := E) (F := F) L rho)
        (fun p : X => (p.1.2,(z p,tol p)))
        ((measurable_fst.snd : Measurable (fun p : X => p.1.2)).prodMk (hz.prodMk htol))
      have hsecond := precomp_family _ (actual_gradient_getter_family (E := E) (F := F) L rho)
        (fun v : V => (v.1.1.2,(y v,dt v)))
        ((measurable_fst.fst.snd : Measurable (fun v : V => v.1.1.2)).prodMk (hy.prodMk hdt))
      have hnext : Measurable (fun w : W =>
          (w.1.1.1,OriginalBorelWarmReplay.CertifiedFirstOrder.next lam w.1.1.2 w.1.2 w.2)) :=
        measurable_fst.fst.fst.prodMk ((next_measurable lam).comp
          (measurable_fst.fst.snd.prodMk (measurable_fst.snd.prodMk measurable_snd)))
      have htail := precomp_family _ ih _ hnext
      have hgo := bind_family _ hsecond _ htail
      have hstop := pure_family (Q := Joint E F) (A := OriginalDualOracleProgram.OracleAnswer (Joint E F))
        (fun v : V => (Sum.inl (z v.1) : Sum F (FOState F))) (measurable_inl.comp (hz.comp measurable_fst))
      have hD : Measurable (fun v : V => v.1.1.1) := measurable_fst.fst.fst
      have ht : MeasurableSet {v : V | ‖v.2‖+tol v.1 ≤ mu*v.1.1.1/2} :=
        measurableSet_le (measurable_snd.norm.add (htol.comp measurable_fst)) ((measurable_const.mul hD).div measurable_const)
      classical
      have hcont := ite_family _ ht _ _ hstop hgo
      have hall := bind_family _ hfirst _ hcont
      convert! hall using 1
      funext p
      exact contraction_loop_succ mu L rho n p.1.1 p.1.2.1 p.1.2.2 p.2

end
end FangqingBorelWarmFirstOrder
end

section
-- Source component: BorelWarmFirstOrderSolve.lean

open MeasureTheory Function
namespace FangqingBorelWarmFirstOrder
open OriginalSaddleImplicit OriginalBetaATSTrial FangqingBorelGetterProgramFamily
  FangqingBorelDualOracleProgram FangqingBorelDualOracleSimulator FangqingBorelWarmDualGetterFamily
noncomputable section
set_option maxHeartbeats 6000000
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F] [FiniteDimensional ℝ F]
local instance : MeasurableSpace E := borel E
local instance : BorelSpace E := ⟨rfl⟩
local instance : MeasurableSpace F := borel F
local instance : BorelSpace F := ⟨rfl⟩
local instance : MeasurableSpace (Joint E F) := borel (Joint E F)
local instance : BorelSpace (Joint E F) := ⟨rfl⟩
local instance : MeasurableSpace (Joint E F →L[ℝ] Joint E F) := borel (Joint E F →L[ℝ] Joint E F)
local instance : BorelSpace (Joint E F →L[ℝ] Joint E F) := ⟨rfl⟩

abbrev DualInput (E F : Type*) := ℝ × ((E × E) × F)
abbrev RestartInput (E F : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] := ℝ × (E × Joint E F)
abbrev SolveInput (E F : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] := (ℝ × ℝ) × (E × Joint E F)
abbrev WarmInput (E F : Type*) := (ℝ × ℝ) × (E × (E × F))

theorem point_measurable : Measurable (fun p : E × F => JointSliceRegularity.point p.1 p.2) := by
  unfold JointSliceRegularity.point
  fun_prop

theorem actual_dual_contraction_family (mu L rho : ℝ) :
    BorelFamily (fun z : DualInput E F =>
      OriginalBorelWarmReplay.OriginalDualGetterImplementation.liftQuery
        (OriginalBorelWarmReplay.OriginalDualFirstOrder.contractionProgram mu L rho z.1 z.2.1.1 z.2.1.2 z.2.2)) := by
  have hi : Measurable (fun z : DualInput E F => ((z.1,z.2.1),(⟨0,z.2.2,z.2.2⟩ : FOState F))) :=
    (measurable_fst.prodMk measurable_snd.fst).prodMk
      (state_mk_measurable _ _ _ measurable_const measurable_snd.snd measurable_snd.snd)
  have hs := precomp_family _ (actual_contraction_loop_family (E := E) (F := F) mu L rho
    (OriginalBorelWarmReplay.CertifiedFirstOrder.iterationCount mu (2*L))) _ hi
  have hm := map_family _ hs (fun z : DualInput E F × Sum F (FOState F) =>
    OriginalBorelWarmReplay.CertifiedFirstOrder.resultPoint z.2) (result_point_measurable.comp measurable_snd)
  simp_rw [OriginalBorelWarmReplay.OriginalDualFirstOrder.contractionProgram,lift_query_qbind]
  simpa only [contractionLoop,FangqingGetterComposition.map,
    OriginalBorelWarmReplay.OriginalDualGetterImplementation.liftQuery] using hm

theorem actual_saddle_stage_family (mu L rho : ℝ) :
    BorelFamily (fun z : DualInput E F =>
      OriginalBorelWarmReplay.OriginalDualGetterImplementation.liftQuery
        (OriginalBorelWarmReplay.OriginalSaddleFirstOrder.program mu L rho z.1 z.2.1.1 z.2.1.2 z.2.2)) := by
  let X := DualInput E F
  let V := X × F
  let W := V × F
  have hsecondMap : Measurable (fun v : V => (v.1.1/2,(v.1.2.1,v.2))) :=
    (measurable_fst.fst.div measurable_const).prodMk (measurable_fst.snd.fst.prodMk measurable_snd)
  have hsecond := precomp_family _ (actual_dual_contraction_family (E := E) (F := F) mu L rho) _ hsecondMap
  have hsimMap : Measurable (fun w : W => (w.1.1.2.1.1,(w.2,(w.1.1.2.1.2,w.1.1.1/8)))) :=
    measurable_fst.fst.snd.fst.fst.prodMk
      (measurable_snd.prodMk (measurable_fst.fst.snd.fst.snd.prodMk (measurable_fst.fst.fst.div measurable_const)))
  have hsim := precomp_family _ (simulator_family (E := E) (F := F) L) _ hsimMap
  have hOut : Measurable (fun z : W × OriginalDualOracleProgram.QueryState E F =>
      JointSliceRegularity.point z.2.u z.1.2) :=
    point_measurable.comp ((state_u_measurable.comp measurable_snd).prodMk measurable_fst.snd)
  have hlast := map_family _ hsim _ hOut
  have hlast' : BorelFamily (fun w : W =>
      FangqingGetterComposition.bind
        (OriginalBorelWarmReplay.OriginalDualGetterImplementation.liftQuery
          (OriginalDualOracleProgram.simulator L w.1.1.2.1.1 w.2 w.1.1.2.1.2 (w.1.1.1/8)))
        (fun s => .pure (JointSliceRegularity.point s.u w.2))) := by
    simpa only [FangqingGetterComposition.map,lift_query_eq_original] using hlast
  have hrest := bind_family _ hsecond _ hlast'
  have hall := bind_family _ (actual_dual_contraction_family (E := E) (F := F) mu L rho) _ hrest
  simp_rw [OriginalBorelWarmReplay.OriginalSaddleFirstOrder.program,lift_query_qbind]
  simpa only [OriginalBorelWarmReplay.OriginalDualGetterImplementation.liftQuery] using hall

theorem actual_saddle_restarts_family (mu L rho : ℝ) (n : ℕ) :
    BorelFamily (fun z : RestartInput E F =>
      OriginalBorelWarmReplay.OriginalDualGetterImplementation.liftQuery
        (OriginalBorelWarmReplay.OriginalSaddleFirstOrder.restartProgram mu L rho z.2.1 n z.1 z.2.2)) := by
  induction n with
  | zero => exact pure_family _ measurable_snd.snd
  | succ n ih =>
      have hw : Measurable (fun z : RestartInput E F => z.2.2) := measurable_snd.snd
      have hxu := (WithLp.fstL 2 ℝ E F).continuous.measurable.comp hw
      have hxv := (WithLp.sndL 2 ℝ E F).continuous.measurable.comp hw
      have hstageMap : Measurable (fun z : RestartInput E F => (z.1,((z.2.1,z.2.2.fst),z.2.2.snd))) :=
        measurable_fst.prodMk ((measurable_snd.fst.prodMk hxu).prodMk hxv)
      have hstage := precomp_family _ (actual_saddle_stage_family (E := E) (F := F) mu L rho) _ hstageMap
      have hnext : Measurable (fun z : RestartInput E F × Joint E F => (z.1.1/2,(z.1.2.1,z.2))) :=
        (measurable_fst.fst.div measurable_const).prodMk (measurable_fst.snd.fst.prodMk measurable_snd)
      have htail := precomp_family _ ih _ hnext
      have hall := bind_family _ hstage _ htail
      simp_rw [OriginalBorelWarmReplay.OriginalSaddleFirstOrder.restartProgram,lift_query_qbind]
      exact hall

theorem actual_saddle_solve_family (mu L rho : ℝ) :
    BorelFamily (fun z : SolveInput E F =>
      OriginalBorelWarmReplay.OriginalDualGetterImplementation.liftQuery
        (OriginalBorelWarmReplay.OriginalSaddleFirstOrder.solveProgram mu L rho z.1.1 z.1.2 z.2.1 z.2.2)) := by
  have hi : Measurable (fun z : SolveInput E F => (z.1.1,z.2)) := measurable_fst.fst.prodMk measurable_snd
  have hn : Measurable (fun z : SolveInput E F =>
      OriginalBorelWarmReplay.FangqingHysteresis.halvingCount z.1.1 z.1.2) := by
    unfold OriginalBorelWarmReplay.FangqingHysteresis.halvingCount Real.logb
    apply Nat.measurable_ceil.comp
    fun_prop
  have hall := nat_select_family
    (fun n (z : SolveInput E F) => OriginalBorelWarmReplay.OriginalDualGetterImplementation.liftQuery
      (OriginalBorelWarmReplay.OriginalSaddleFirstOrder.restartProgram mu L rho z.2.1 n z.1.1 z.2.2))
    (fun n => precomp_family _ (actual_saddle_restarts_family (E := E) (F := F) mu L rho n) _ hi) _ hn
  simpa only [OriginalBorelWarmReplay.OriginalSaddleFirstOrder.solveProgram] using hall

/-- The actual first-order cap, jointly Borel in both changing warm distance
and requested precision, in the primal center/start, and in every response. -/
theorem actual_first_order_warm_program_family (mu L rho : ℝ) :
    BorelFamily (fun z : WarmInput E F =>
      OriginalBorelWarmReplay.OriginalDualGetterImplementation.liftQuery
        (OriginalBorelWarmReplay.OriginalDualWarmFirstOrder.program mu L rho z.1.1 z.1.2 z.2.1 z.2.2.1 z.2.2.2)) := by
  let X := WarmInput E F
  let R : X → ℝ := fun z => OriginalBorelWarmReplay.OriginalDualWarmFirstOrder.workingRadius z.1.1 z.1.2
  have hR : Measurable R := by unfold R OriginalBorelWarmReplay.OriginalDualWarmFirstOrder.workingRadius; fun_prop
  have hi : Measurable (fun z : X => (z.2.1,(z.2.2.2,(z.2.2.1,R z/4)))) :=
    measurable_snd.fst.prodMk (measurable_snd.snd.snd.prodMk
      (measurable_snd.snd.fst.prodMk (hR.div measurable_const)))
  have hprep := precomp_family _ (simulator_family (E := E) (F := F) L) _ hi
  have hprep' : BorelFamily (fun z : X => OriginalBorelWarmReplay.OriginalDualGetterImplementation.liftQuery
      (OriginalDualOracleProgram.simulator L z.2.1 z.2.2.2 z.2.2.1 (R z/4))) := by
    simpa only [lift_query_eq_original] using hprep
  have hpoint : Measurable (fun z : X × OriginalDualOracleProgram.QueryState E F =>
      JointSliceRegularity.point z.2.u z.1.2.2.2) :=
    point_measurable.comp ((state_u_measurable.comp measurable_snd).prodMk measurable_fst.snd.snd.snd)
  have hnext : Measurable (fun z : X × OriginalDualOracleProgram.QueryState E F =>
      ((2*R z.1,z.1.1.2),(z.1.2.1,JointSliceRegularity.point z.2.u z.1.2.2.2))) :=
    ((measurable_const.mul (hR.comp measurable_fst)).prodMk measurable_fst.fst.snd).prodMk
      (measurable_fst.snd.fst.prodMk hpoint)
  have htail := precomp_family _ (actual_saddle_solve_family (E := E) (F := F) mu L rho) _ hnext
  have hall := bind_family _ hprep' _ htail
  simp_rw [OriginalBorelWarmReplay.OriginalDualWarmFirstOrder.program,lift_query_qbind]
  exact hall

end
end FangqingBorelWarmFirstOrder
end

section
-- Source component: BorelWarmMinimumProgram.lean

open MeasureTheory
namespace FangqingBorelWarmMinimum
open OriginalSaddleImplicit OriginalSaddleTransfer OriginalSaddleStability
  OriginalBetaATSTrial FangqingBorelGetterProgramFamily FangqingBorelWarmSecondOrder
noncomputable section
set_option maxHeartbeats 6000000
universe u
variable {E F : Type u}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F] [FiniteDimensional ℝ F]
local instance : MeasurableSpace E := borel E
local instance : BorelSpace E := ⟨rfl⟩
local instance : MeasurableSpace F := borel F
local instance : BorelSpace F := ⟨rfl⟩
local instance : MeasurableSpace (Joint E F) := borel (Joint E F)
local instance : BorelSpace (Joint E F) := ⟨rfl⟩
local instance : MeasurableSpace (Joint E F →L[ℝ] Joint E F) := borel (Joint E F →L[ℝ] Joint E F)
local instance : BorelSpace (Joint E F →L[ℝ] Joint E F) := ⟨rfl⟩

noncomputable def program (mu L rho D tau : ℝ) (x uInit : E) (yin : F) :=
  if OriginalBorelWarmReplay.OriginalMinimumWarmSolver.firstScale mu L ≤
      OriginalBorelWarmReplay.OriginalMinimumWarmSolver.secondScale mu rho D then
    OriginalBorelWarmReplay.OriginalDualGetterImplementation.liftQuery
      (OriginalBorelWarmReplay.OriginalDualWarmFirstOrder.program mu L rho D tau x uInit yin)
  else fixedProgram mu L rho D tau x uInit yin

/-- The actual min algorithm is Borel on the complete response space. Every
optimizer, adaptive beta trial, restart and primitive oracle continuation has
been instantiated; this is not an arbitrary-syntax admissibility assumption. -/
theorem actual_minimum_program_family (mu L rho D tau : ℝ) :
    BorelFamily (fun z : Input E F => program mu L rho D tau z.1 z.2.1 z.2.2) := by
  have hf := precomp_family _
    (FangqingBorelWarmFirstOrder.actual_first_order_warm_program_family (E:=E) (F:=F) mu L rho)
    (fun z : Input E F => ((D,tau),z)) (measurable_const.prodMk measurable_id)
  classical
  by_cases h : OriginalBorelWarmReplay.OriginalMinimumWarmSolver.firstScale mu L ≤
      OriginalBorelWarmReplay.OriginalMinimumWarmSolver.secondScale mu rho D
  · simpa only [program,if_pos h] using hf
  · simpa only [program,if_neg h] using fixed_program_family (E:=E) (F:=F) mu L rho D tau

theorem fixed_execution_eq_original
    (J : Joint E F → ℝ) (mu L rho D tau : ℝ)
    (hmu : 0 < mu) (hL : 0 < L) (htau : 0 < tau)
    (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (hHess : ∀ z w : Joint E F, ‖fderiv ℝ (gradient J) z - fderiv ℝ (gradient J) w‖ ≤ rho * ‖z - w‖)
    (hsc : ∀ u : E, StrongConvexOn (Set.univ : Set F) mu (fun y => -JointSliceRegularity.curry J u y))
    (x uInit : E) (yin : F) (hwarm : ‖yin - vStar (JointSliceRegularity.curry J) L x‖ ≤ D) :
    OriginalBorelWarmReplay.OriginalBetaATSTrial.execute (OriginalDualOracleProgram.actualOracle J)
      (fixedProgram mu L rho D tau x uInit yin) =
    OriginalBorelWarmReplay.OriginalBetaATSTrial.execute (OriginalDualOracleProgram.actualOracle J)
      (OriginalBorelWarmReplay.OriginalSecondOrderWarmAll.program mu L rho D tau x uInit yin) := by
  classical
  by_cases hr : 0 < rho
  · simpa only [fixedProgram,OriginalBorelWarmReplay.OriginalSecondOrderWarmAll.program,if_pos hr] using
      positive_warm_execution_eq_original J mu L rho D tau hmu hL hr htau hC2 hLip hHess hsc x uInit yin hwarm
  · simpa only [fixedProgram,OriginalBorelWarmReplay.OriginalSecondOrderWarmAll.program,if_neg hr] using
      zero_warm_execution_eq_original J mu L tau x uInit yin

theorem actual_minimum_execution_eq_original
    (J : Joint E F → ℝ) (mu L rho D tau : ℝ)
    (hmu : 0 < mu) (hL : 0 < L) (htau : 0 < tau)
    (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (hHess : ∀ z w : Joint E F, ‖fderiv ℝ (gradient J) z - fderiv ℝ (gradient J) w‖ ≤ rho * ‖z - w‖)
    (hsc : ∀ u : E, StrongConvexOn (Set.univ : Set F) mu (fun y => -JointSliceRegularity.curry J u y))
    (x uInit : E) (yin : F) (hwarm : ‖yin - vStar (JointSliceRegularity.curry J) L x‖ ≤ D) :
    OriginalBorelWarmReplay.OriginalBetaATSTrial.execute (OriginalDualOracleProgram.actualOracle J)
      (program mu L rho D tau x uInit yin) =
    OriginalBorelWarmReplay.OriginalBetaATSTrial.execute (OriginalDualOracleProgram.actualOracle J)
      (OriginalBorelWarmReplay.OriginalMinimumWarmSolver.program mu L rho D tau x uInit yin) := by
  classical
  unfold program OriginalBorelWarmReplay.OriginalMinimumWarmSolver.program
  split_ifs
  · rfl
  · exact fixed_execution_eq_original J mu L rho D tau hmu hL htau hC2 hLip hHess hsc x uInit yin hwarm

/-- Residual-log interpretation only: the displayed logarithmic factor keeps
the observable initial primal residual. No uniformity in that residual is
asserted. The returned pair and every charged original-O2 query are actual. -/
theorem admissible_minimum_warm_from_standing_joint
    (J : Joint E F → ℝ) (mu L rho D tau : ℝ)
    (hmu : 0 < mu) (hLmu : mu ≤ L) (hrho : 0 ≤ rho) (htau : 0 < tau)
    (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (hHess : ∀ z w : Joint E F, ‖fderiv ℝ (gradient J) z - fderiv ℝ (gradient J) w‖ ≤ rho * ‖z - w‖)
    (hconcave : ∀ u : E, StrongConcaveOn (Set.univ : Set F) mu
      (fun y => J (WithLp.toLp 2 (u,y))))
    (x uInit : E) (yin : F) (hwarm : ‖yin - vStar (JointSliceRegularity.curry J) L x‖ ≤ D) :
    BorelFamily (fun z : Input E F => program mu L rho D tau z.1 z.2.1 z.2.2) ∧
    let run := execute (OriginalDualOracleProgram.actualOracle J) (program mu L rho D tau x uInit yin)
    ‖run.1 - zStar (JointSliceRegularity.curry J) L x‖ ≤ tau ∧
      (run.2 : ℝ) ≤ (1+min (Real.sqrt (L/mu)) ((rho*D/mu)^(2/7:ℝ))) *
        OriginalBorelWarmReplay.OriginalMinimumWarmSolver.logFactor J mu L rho D tau x uInit yin := by
  have hc' : ∀ u : E, StrongConcaveOn (Set.univ : Set F) mu (JointSliceRegularity.curry J u) := by
    intro u
    convert hconcave u using 1
    funext y
    exact congrArg J (JointSliceRegularity.point_eq_toLp u y)
  have hsc := JointSliceRegularity.strongConvex_negative_y_slice J mu hc'
  have heq := actual_minimum_execution_eq_original J mu L rho D tau hmu (hmu.trans_le hLmu) htau
    hC2 hLip hHess hsc x uInit yin hwarm
  refine ⟨actual_minimum_program_family mu L rho D tau,?_⟩
  dsimp only
  rw [← OriginalBorelWarmReplay.OriginalBetaATSTrial.execute_eq_original,heq]
  exact OriginalBorelWarmReplay.OriginalMinimumWarmSolver.warm_solve_from_standing_joint
    J mu L rho D tau hmu hLmu hrho htau hC2 hLip hHess hconcave x uInit yin hwarm

end
end FangqingBorelWarmMinimum
end

section
-- Source component: BorelGetterOperationalReplay.lean

open MeasureTheory Function
namespace FangqingBorelGetterOperationalReplay
open OriginalBetaATSTrial FangqingGetterComposition FangqingBorelGetterProgramFamily
noncomputable section
set_option maxHeartbeats 4500000
variable {X Q A R : Type*}
local instance (p : Prop) : Decidable p := Classical.propDecidable p

def oracleAnswers (getter : Q → A) (a0 : A) : GetterProgram Q A R → ℕ → A
  | .pure _, _ => a0
  | .ask q k, 0 => getter q
  | .ask q k, n+1 => oracleAnswers getter a0 (k (getter q)) n

theorem oracle_answers_drop (getter : Q → A) (a0 : A) (q : Q) (k : A → GetterProgram Q A R) :
    streamDrop 1 (oracleAnswers getter a0 (.ask q k)) = oracleAnswers getter a0 (k (getter q)) := by
  funext n
  simp only [streamDrop,Nat.add_comm 1 n,oracleAnswers]

theorem stream_run_actual_oracle (getter : Q → A) (a0 : A) (p : GetterProgram Q A R) :
    streamRun p (oracleAnswers getter a0 p) = ((execute getter p).1,trace getter p) := by
  induction p with
  | pure r => rfl
  | ask q k ih => simp only [streamRun,oracleAnswers,oracle_answers_drop,execute,trace,ih]

theorem oracle_answer_is_actual_reply (getter : Q → A) (a0 : A) (q0 : Q)
    (p : GetterProgram Q A R) (n : ℕ) (hn : n < (trace getter p).length) :
    oracleAnswers getter a0 p n = getter ((trace getter p).getD n q0) := by
  induction p generalizing n with
  | pure r => simp only [trace,List.length_nil] at hn; omega
  | ask q k ih =>
      cases n with
      | zero => rfl
      | succ n =>
          exact ih (getter q) n (by simpa only [trace,List.length_cons,Nat.add_lt_add_iff_right] using hn)

theorem requests_equal_under_prefix (p : GetterProgram Q A R) (a b : ℕ → A)
    (q0 : Q) (n : ℕ) (hab : ∀ j<n, a j=b j) :
    (streamRun p a).2.getD n q0 = (streamRun p b).2.getD n q0 := by
  have he := congrArg (fun l : List Q => l[n]?) (prefix_causality p a b n hab).1
  have he' : (streamRun p a).2[n]? = (streamRun p b).2[n]? := by
    simpa only [List.getElem?_take,Nat.lt_succ_self,if_true] using he
  simpa only [List.getD_eq_getElem?_getD] using congrArg (fun o : Option Q => o.getD q0) he'

def onlineHistory (getter : Q → A) (a0 : A) (q0 : Q) (p : GetterProgram Q A R) : ℕ → ℕ → A
  | 0 => fun _ => a0
  | n+1 =>
      let a := onlineHistory getter a0 q0 p n
      if (streamRun p (streamPad n a0 a)).2.length ≤ n then a
      else Function.update a n (getter ((streamRun p (streamPad n a0 a)).2.getD n q0))

theorem online_history_is_actual_answer_prefix
    (getter : Q → A) (a0 : A) (q0 : Q) (p : GetterProgram Q A R)
    (n : ℕ) (hn : n ≤ (trace getter p).length) :
    ∀ j<n, onlineHistory getter a0 q0 p n j = oracleAnswers getter a0 p j := by
  induction n with
  | zero => intro j hj; omega
  | succ n ih =>
      have hn' : n ≤ (trace getter p).length := by omega
      have hnlt : n < (trace getter p).length := by omega
      have hpast := ih hn'
      let a := onlineHistory getter a0 q0 p n
      have hprefix : ∀ j<n, oracleAnswers getter a0 p j = streamPad n a0 a j := by
        intro j hj
        simp only [streamPad,if_pos hj]
        exact (hpast j hj).symm
      have hc := prefix_causality p (oracleAnswers getter a0 p) (streamPad n a0 a) n hprefix
      have hstop : ¬ (streamRun p (streamPad n a0 a)).2.length ≤ n := by
        intro hh
        have he := hc.2.1.mpr hh
        rw [stream_run_actual_oracle] at he
        change (trace getter p).length ≤ n at he
        omega
      have hquery : (streamRun p (streamPad n a0 a)).2.getD n q0 = (trace getter p).getD n q0 := by
        rw [← requests_equal_under_prefix p (oracleAnswers getter a0 p) (streamPad n a0 a) q0 n hprefix,
          stream_run_actual_oracle]
      have hstep : onlineHistory getter a0 q0 p (n+1) =
          Function.update a n (getter ((trace getter p).getD n q0)) := by
        change (if (streamRun p (streamPad n a0 a)).2.length ≤ n then a
          else Function.update a n (getter ((streamRun p (streamPad n a0 a)).2.getD n q0))) = _
        rw [if_neg hstop,hquery]
      intro j hj
      rw [hstep]
      by_cases hjn : j=n
      · subst j
        rw [Function.update_self]
        exact (oracle_answer_is_actual_reply getter a0 q0 p n hnlt).symm
      · rw [Function.update_of_ne hjn]
        exact hpast j (by omega)

theorem online_replay_before_stop (getter : Q → A) (a0 : A) (q0 : Q) (p : GetterProgram Q A R)
    (n : ℕ) (hn : n < (trace getter p).length) :
    let a := onlineHistory getter a0 q0 p n
    ¬ (streamRun p (streamPad n a0 a)).2.length ≤ n ∧
      (streamRun p (streamPad n a0 a)).2.getD n q0 = (trace getter p).getD n q0 := by
  intro a
  have hprefix : ∀ j<n, oracleAnswers getter a0 p j = streamPad n a0 a j := by
    intro j hj
    simp only [streamPad,if_pos hj]
    exact (online_history_is_actual_answer_prefix getter a0 q0 p n hn.le j hj).symm
  refine ⟨?_,?_⟩
  · intro hh
    have he := (prefix_causality p (oracleAnswers getter a0 p) (streamPad n a0 a) n hprefix).2.1.mpr hh
    rw [stream_run_actual_oracle] at he
    change (trace getter p).length ≤ n at he
    omega
  · rw [← requests_equal_under_prefix p (oracleAnswers getter a0 p) (streamPad n a0 a) q0 n hprefix,
      stream_run_actual_oracle]

theorem online_replay_exact_result_and_charged_count
    (getter : Q → A) (a0 : A) (q0 : Q) (p : GetterProgram Q A R) :
    let K := (execute getter p).2
    let a := onlineHistory getter a0 q0 p K
    streamRun p (streamPad K a0 a) = ((execute getter p).1,trace getter p) ∧
      (trace getter p).length = K := by
  intro K a
  have hK : (trace getter p).length = K := trace_length_eq_count getter p
  have hprefix : ∀ j<K, oracleAnswers getter a0 p j = streamPad K a0 a j := by
    intro j hj
    simp only [streamPad,if_pos hj]
    exact (online_history_is_actual_answer_prefix getter a0 q0 p K (by omega) j hj).symm
  have hc := prefix_causality p (oracleAnswers getter a0 p) (streamPad K a0 a) K hprefix
  have hh : (streamRun p (oracleAnswers getter a0 p)).2.length ≤ K := by
    rw [stream_run_actual_oracle]
    exact hK.le
  exact ⟨(hc.2.2 hh).symm.trans (stream_run_actual_oracle getter a0 p),hK⟩

section Measurable
variable [MeasurableSpace X] [MeasurableSpace Q] [MeasurableSpace A] [MeasurableSpace R]

theorem online_history_measurable (p : X → GetterProgram Q A R) (hp : BorelFamily p)
    (getter : X × Q → A) (hg : Measurable getter) (a0 : A) (q0 : Q) (n : ℕ) :
    Measurable (fun x => onlineHistory (fun q => getter (x,q)) a0 q0 (p x) n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
      have hi : Measurable (fun x : X => (x,onlineHistory (fun q => getter (x,q)) a0 q0 (p x) n)) :=
        measurable_id.prodMk ih
      have hquery := (actual_next_query_measurable p hp n a0 q0).comp hi
      have hreply := hg.comp (measurable_id.prodMk hquery)
      have hstop := (actual_stop_measurable p hp n a0).preimage hi
      have hupdate : Measurable (fun x => Function.update
          (onlineHistory (fun q => getter (x,q)) a0 q0 (p x) n) n
          (getter (x,(streamRun (p x) (streamPad n a0
            (onlineHistory (fun q => getter (x,q)) a0 q0 (p x) n))).2.getD n q0))) := by
        apply measurable_pi_lambda
        intro j
        by_cases hj : j=n
        · subst j
          simpa only [Function.update_self,Function.comp_def,id_eq] using hreply
        · simpa only [Function.update_of_ne hj,Function.comp_def] using (measurable_pi_apply j).comp ih
      convert! ih.ite hstop hupdate using 1

end Measurable
end
end FangqingBorelGetterOperationalReplay

namespace FangqingBorelGetterOperationalReplay
open OriginalBetaATSTrial FangqingGetterComposition FangqingBorelGetterProgramFamily
noncomputable section
set_option maxHeartbeats 4500000
local instance (p : Prop) : Decidable p := Classical.propDecidable p
variable {X Q A R : Type*}
variable [MeasurableSpace X] [MeasurableSpace Q] [MeasurableSpace A] [MeasurableSpace R]

/-- Certified stream syntax yields the actual finite adaptive oracle execution,
including its exact stopping time. The proof constructs each paid online query
from the finite answer prefix and then uses a measurable least stopping index. -/
theorem actual_execution_result_and_count_measurable
    (p : X → GetterProgram Q A R) (hp : BorelFamily p)
    (getter : X × Q → A) (hg : Measurable getter) (a0 : A) (q0 : Q) :
    Measurable (fun x => execute (fun q => getter (x,q)) (p x)) := by
  let hist : ℕ → X → ℕ → A := fun n x => onlineHistory (fun q => getter (x,q)) a0 q0 (p x) n
  let stopped : ℕ → X → Prop := fun n x => (streamRun (p x) (streamPad n a0 (hist n x))).2.length ≤ n
  have hh : ∀ n, Measurable (hist n) := fun n => online_history_measurable p hp getter hg a0 q0 n
  have hs : ∀ n, MeasurableSet {x | stopped n x} := by
    intro n
    exact (actual_stop_measurable p hp n a0).preimage (measurable_id.prodMk (hh n))
  have hterm : ∀ x, ∃ n, stopped n x := by
    intro x
    let K := (execute (fun q => getter (x,q)) (p x)).2
    refine ⟨K,?_⟩
    have he := online_replay_exact_result_and_charged_count (fun q => getter (x,q)) a0 q0 (p x)
    change (streamRun (p x) (streamPad K a0 (hist K x))).2.length ≤ K
    rw [he.1]
    exact he.2.le
  let halt : X → ℕ := fun x => Nat.find (hterm x)
  have hhalt : Measurable halt := measurable_find hterm hs
  have hhaltEq : ∀ x, halt x = (execute (fun q => getter (x,q)) (p x)).2 := by
    intro x
    let K := (execute (fun q => getter (x,q)) (p x)).2
    have hK : stopped K x := by
      have he := online_replay_exact_result_and_charged_count (fun q => getter (x,q)) a0 q0 (p x)
      change (streamRun (p x) (streamPad K a0 (hist K x))).2.length ≤ K
      rw [he.1]
      exact he.2.le
    have hle : halt x ≤ K := Nat.find_min' (hterm x) hK
    apply le_antisymm hle
    by_contra hn
    have hlt : halt x < (trace (fun q => getter (x,q)) (p x)).length := by
      rw [trace_length_eq_count]
      change halt x < K
      omega
    exact (online_replay_before_stop (fun q => getter (x,q)) a0 q0 (p x) (halt x) hlt).1 (Nat.find_spec (hterm x))
  let result : ℕ → X → R := fun n x => (streamRun (p x) (streamPad n a0 (hist n x))).1
  have hr : ∀ n, Measurable (result n) := by
    intro n
    exact (actual_stopped_output_measurable p hp n a0).comp (measurable_id.prodMk (hh n))
  have hresult := measurable_nat_select result hr halt hhalt
  have heq : (fun x => execute (fun q => getter (x,q)) (p x)) = fun x => (result (halt x) x,halt x) := by
    funext x
    rw [hhaltEq x]
    have he := online_replay_exact_result_and_charged_count (fun q => getter (x,q)) a0 q0 (p x)
    apply Prod.ext
    · exact (congrArg Prod.fst he.1).symm
    · rfl
  rw [heq]
  exact hresult.prodMk hhalt

end
end FangqingBorelGetterOperationalReplay
end

section
-- Source component: BorelWarmMinimumOperational.lean

open MeasureTheory
namespace FangqingBorelWarmMinimum
open OriginalSaddleImplicit OriginalBetaATSTrial FangqingBorelGetterProgramFamily
  FangqingBorelGetterOperationalReplay FangqingBorelDualOracleProgram FangqingBorelWarmSecondOrder
noncomputable section
set_option maxHeartbeats 6000000
universe u
variable {E F : Type u}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F] [FiniteDimensional ℝ F]
local instance : MeasurableSpace E := borel E
local instance : BorelSpace E := ⟨rfl⟩
local instance : MeasurableSpace F := borel F
local instance : BorelSpace F := ⟨rfl⟩
local instance : MeasurableSpace (Joint E F) := borel (Joint E F)
local instance : BorelSpace (Joint E F) := ⟨rfl⟩
local instance : MeasurableSpace (Joint E F →L[ℝ] Joint E F) := borel (Joint E F →L[ℝ] Joint E F)
local instance : BorelSpace (Joint E F →L[ℝ] Joint E F) := ⟨rfl⟩

theorem actual_bundle_measurable (J : Joint E F → ℝ) (hC2 : ContDiff ℝ 2 J) :
    Measurable (OriginalDualOracleProgram.actualOracle J) := by
  have hg := OriginalSaddleImplicit.contDiff_gradient_of_contDiff2 J hC2
  have hh : ContDiff ℝ 0 (fderiv ℝ (gradient J)) := hg.fderiv_right (by norm_num)
  exact answer_mk_measurable _ _ _ hC2.continuous.measurable hg.continuous.measurable
    hh.continuous.measurable

/-- Online interpretation is the original execute, with its exact charged
count. All request, stop and output maps come from the proved full-stream
family, rather than arbitrary GetterProgram continuations. -/
theorem actual_minimum_execution_measurable (J : Joint E F → ℝ)
    (hC2 : ContDiff ℝ 2 J) (mu L rho D tau : ℝ) :
    Measurable (fun z : Input E F => execute (OriginalDualOracleProgram.actualOracle J)
      (program mu L rho D tau z.1 z.2.1 z.2.2)) := by
  exact actual_execution_result_and_count_measurable _
    (actual_minimum_program_family mu L rho D tau)
    (fun z : Input E F × Joint E F => OriginalDualOracleProgram.actualOracle J z.2)
    ((actual_bundle_measurable J hC2).comp measurable_snd) ⟨0,0,0⟩ 0

end
end FangqingBorelWarmMinimum
end

section
-- Source component: BorelWarmJointMinimum.lean

open MeasureTheory
namespace FangqingBorelWarmMinimum
open OriginalSaddleImplicit OriginalSaddleTransfer OriginalSaddleStability
  OriginalBetaATSTrial FangqingBorelGetterProgramFamily FangqingBorelWarmSecondOrder
  OriginalWarmDyadicRounding FangqingBorelCountableSelection
noncomputable section
set_option maxHeartbeats 6000000
universe u
variable {E F : Type u}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F] [FiniteDimensional ℝ F]
local instance : MeasurableSpace E := borel E
local instance : BorelSpace E := ⟨rfl⟩
local instance : MeasurableSpace F := borel F
local instance : BorelSpace F := ⟨rfl⟩
local instance : MeasurableSpace (Joint E F) := borel (Joint E F)
local instance : BorelSpace (Joint E F) := ⟨rfl⟩
local instance : MeasurableSpace (Joint E F →L[ℝ] Joint E F) := borel (Joint E F →L[ℝ] Joint E F)
local instance : BorelSpace (Joint E F →L[ℝ] Joint E F) := ⟨rfl⟩

def roundedRadius (D : ℝ) : ℝ := if 0 < D then upper D else 0

noncomputable def jointProgram (mu L rho D tau : ℝ) (x uInit : E) (yin : F) :=
  program mu L rho (roundedRadius D) (lower tau) x uInit yin

theorem rounded_radius_bounds (D : ℝ) (hD : 0 ≤ D) : D ≤ roundedRadius D ∧ roundedRadius D ≤ 2*D := by
  classical
  by_cases hp : 0 < D
  · simpa only [roundedRadius,if_pos hp] using upper_bounds D hp
  · have hz : D=0 := le_antisymm (le_of_not_gt hp) hD
    simp [roundedRadius,hz]

theorem actual_joint_minimum_program_family (mu L rho : ℝ) :
    BorelFamily (fun z : WarmInput E F => jointProgram mu L rho z.1.1 z.1.2 z.2.1 z.2.2.1 z.2.2.2) := by
  have hp : ∀ ij : ℤ × ℤ, BorelFamily (fun z : WarmInput E F =>
      program mu L rho (dyadic ij.1) (dyadic ij.2) z.2.1 z.2.2.1 z.2.2.2) := by
    intro ij
    exact precomp_family _ (actual_minimum_program_family mu L rho (dyadic ij.1) (dyadic ij.2)) _ measurable_snd
  have hi : Measurable (fun z : WarmInput E F => (upperIndex z.1.1,lowerIndex z.1.2)) :=
    (upper_index_measurable.comp measurable_fst.fst).prodMk (lower_index_measurable.comp measurable_fst.snd)
  have hp' := countable_select_family _ hp _ hi
  have hz : ∀ i : ℤ, BorelFamily (fun z : WarmInput E F =>
      program mu L rho 0 (dyadic i) z.2.1 z.2.2.1 z.2.2.2) := by
    intro i
    exact precomp_family _ (actual_minimum_program_family mu L rho 0 (dyadic i)) _ measurable_snd
  have hz' := countable_select_family _ hz (fun z : WarmInput E F => lowerIndex z.1.2)
    (lower_index_measurable.comp measurable_fst.snd)
  have ht : MeasurableSet {z : WarmInput E F | 0 < z.1.1} :=
    measurableSet_lt measurable_const measurable_fst.fst
  have h := ite_family (fun z : WarmInput E F => 0 < z.1.1) ht _ _ hp' hz'
  convert h using 1
  funext z
  unfold jointProgram roundedRadius upper lower
  split_ifs <;> rfl

theorem rounded_factor_bound (mu L rho D : ℝ) (hmu : 0 < mu) (hrho : 0 ≤ rho) (hD : 0 ≤ D) :
    1+min (Real.sqrt (L/mu)) ((rho*roundedRadius D/mu)^(2/7:ℝ)) ≤
      2*(1+min (Real.sqrt (L/mu)) ((rho*D/mu)^(2/7:ℝ))) := by
  classical
  by_cases hp : 0 < D
  · simpa only [roundedRadius,if_pos hp] using rounded_minimum_factor_bound mu L rho D hmu hrho hp
  · have hz : D=0 := le_antisymm (le_of_not_gt hp) hD
    simp only [roundedRadius,if_neg hp,hz,mul_zero,zero_div,Real.zero_rpow (by norm_num : (2/7:ℝ) ≠ 0)]
    have hs := Real.sqrt_nonneg (L/mu)
    rw [min_eq_right hs]
    norm_num

/-- A genuinely joint-radius/joint-tolerance Borel warm callback for adaptive
main algorithms. Rounding costs at most the explicit universal factor TWO;
its remaining logarithmic factor is evaluated at the explicit dyadic scales. -/
theorem admissible_joint_minimum_warm_from_standing_joint
    (J : Joint E F → ℝ) (mu L rho D tau : ℝ)
    (hmu : 0 < mu) (hLmu : mu ≤ L) (hrho : 0 ≤ rho) (htau : 0 < tau)
    (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (hHess : ∀ z w : Joint E F, ‖fderiv ℝ (gradient J) z - fderiv ℝ (gradient J) w‖ ≤ rho * ‖z - w‖)
    (hconcave : ∀ u : E, StrongConcaveOn (Set.univ : Set F) mu
      (fun y => J (WithLp.toLp 2 (u,y))))
    (x uInit : E) (yin : F) (hwarm : ‖yin - vStar (JointSliceRegularity.curry J) L x‖ ≤ D) :
    BorelFamily (fun z : WarmInput E F => jointProgram mu L rho z.1.1 z.1.2 z.2.1 z.2.2.1 z.2.2.2) ∧
    let run := execute (OriginalDualOracleProgram.actualOracle J) (jointProgram mu L rho D tau x uInit yin)
    ‖run.1-zStar (JointSliceRegularity.curry J) L x‖ ≤ tau ∧
      (run.2 : ℝ) ≤ 2*(1+min (Real.sqrt (L/mu)) ((rho*D/mu)^(2/7:ℝ))) *
        OriginalBorelWarmReplay.OriginalMinimumWarmSolver.logFactor J mu L rho
          (roundedRadius D) (lower tau) x uInit yin := by
  have hD : 0 ≤ D := (norm_nonneg _).trans hwarm
  have hL : 0 < L := hmu.trans_le hLmu
  have ht : 0 < lower tau := dyadic_positive _
  have h := admissible_minimum_warm_from_standing_joint J mu L rho (roundedRadius D) (lower tau)
    hmu hLmu hrho ht hC2 hLip hHess hconcave x uInit yin (hwarm.trans (rounded_radius_bounds D hD).1)
  have hf := OriginalBorelWarmReplay.OriginalMinimumWarmSolver.first_order_factorization
    mu L rho (roundedRadius D) (lower tau)
    (‖OriginalPrimalElimination.residual J L x (yin,uInit)‖/L) hmu hLmu hrho ht (by positivity)
  have hnonneg : 0 ≤ OriginalBorelWarmReplay.OriginalMinimumWarmSolver.logFactor J mu L rho
      (roundedRadius D) (lower tau) x uInit yin :=
    hf.1.trans (le_max_left _ _)
  refine ⟨actual_joint_minimum_program_family mu L rho,?_,?_⟩
  · exact h.2.1.trans (lower_bounds tau htau).2
  · exact h.2.2.trans (mul_le_mul_of_nonneg_right (rounded_factor_bound mu L rho D hmu hrho hD) hnonneg)

end
end FangqingBorelWarmMinimum
end

section
-- Source component: BorelWarmScalarTransport.lean

namespace FangqingBorelWarmScalarTransport
noncomputable section
abbrev N := OriginalBorelWarmReplay.OriginalCoupledBetaSearch.Settings
abbrev O := OriginalCoupledBetaSearch.Settings
def settings (c:N) : O := ⟨c.mu,c.Lg,c.M,c.A,c.sigma,c.sigmaLow,c.sigmaUp,c.rho⟩
theorem uniform_precision_floor_eq (c:N) (s D:ℝ) (n:ℕ) : OriginalBorelWarmReplay.OriginalRobustTrajectory.uniformPrecisionFloor c s D n = OriginalRobustTrajectory.uniformPrecisionFloor (settings c) s D n := by rfl
theorem getter_count_ceiling_eq (c:N) (D:ℝ) (n:ℕ) : OriginalBorelWarmReplay.OriginalRobustTrajectory.getterCountCeiling c D n = OriginalRobustTrajectory.getterCountCeiling (settings c) D n := by rfl
theorem uniform_query_radius_eq (c:N) (D:ℝ) : OriginalBorelWarmReplay.OriginalRobustTrajectory.uniformQueryRadius c D = OriginalRobustTrajectory.uniformQueryRadius (settings c) D := by rfl
theorem radius_precision_eq (c:N) (s R:ℝ) : OriginalBorelWarmReplay.OriginalRobustTrajectory.radiusPrecision c s R = OriginalRobustTrajectory.radiusPrecision (settings c) s R := by rfl
theorem radius_getter_factor_eq (c:N) (s R:ℝ) : OriginalBorelWarmReplay.OriginalRobustTrajectory.radiusGetterFactor c s R = OriginalRobustTrajectory.radiusGetterFactor (settings c) s R := by rfl
theorem first_log_factor_eq (mu L rho D tau Dobs:ℝ) : OriginalBorelWarmReplay.OriginalMinimumWarmSolver.firstLogFactor mu L rho D tau Dobs = OriginalMinimumWarmSolver.firstLogFactor mu L rho D tau Dobs := by rfl
end
end FangqingBorelWarmScalarTransport
namespace FangqingBorelWarmScalarTransport
noncomputable section
theorem precision_minimum_eq (c:N) (s:ℝ) (r:ℕ) (D:ℝ) :
    OriginalBorelWarmReplay.OriginalRobustTrajectory.precisionMinimum c s r D =
      OriginalRobustTrajectory.precisionMinimum (settings c) s r D := by
  induction r generalizing D with
  | zero => rfl
  | succ r ih =>
    simp only [OriginalBorelWarmReplay.OriginalRobustTrajectory.precisionMinimum,
      OriginalRobustTrajectory.precisionMinimum,ih]
    rfl
theorem coefficient_maximum_eq (f:ℝ→ℕ) (r:ℕ) (D:ℝ) : OriginalBorelWarmReplay.OriginalRobustTrajectory.coefficientMaximum f r D = OriginalRobustTrajectory.coefficientMaximum f r D := by
  induction r generalizing D with
  | zero => rfl
  | succ r ih => simp only [OriginalBorelWarmReplay.OriginalRobustTrajectory.coefficientMaximum,
      OriginalRobustTrajectory.coefficientMaximum,ih]
end
end FangqingBorelWarmScalarTransport

namespace FangqingBorelWarmScalarTransport
open OriginalSaddleImplicit
noncomputable section
set_option maxHeartbeats 4000000

theorem parameters_eq (mu L rho D:ℝ) :
    settings (OriginalBorelWarmReplay.OriginalActualDualPositiveContraction.parameters mu L rho D) =
      OriginalActualDualPositiveContraction.parameters mu L rho D := rfl

theorem positive_log_factor_eq
    {E F:Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F] [FiniteDimensional ℝ F]
    (J:Joint E F→ℝ) (mu L rho D tau:ℝ) (x u:E) (y:F) :
    OriginalBorelWarmReplay.OriginalMinimumWarmSolver.positiveLogFactor J mu L rho D tau x u y =
      OriginalMinimumWarmSolver.positiveLogFactor J mu L rho D tau x u y := by
  let c := OriginalBorelWarmReplay.OriginalActualDualPositiveContraction.parameters mu L rho D
  have hf : OriginalBorelWarmReplay.OriginalRobustTrajectory.radiusGetterFactor c (1/2) =
      OriginalRobustTrajectory.radiusGetterFactor (settings c) (1/2) := by
    funext R
    exact radius_getter_factor_eq c (1/2) R
  simp only [OriginalBorelWarmReplay.OriginalMinimumWarmSolver.positiveLogFactor,
    OriginalMinimumWarmSolver.positiveLogFactor,coefficient_maximum_eq,precision_minimum_eq]
  split_ifs
  · rw [show OriginalBorelWarmReplay.OriginalRobustTrajectory.radiusGetterFactor
      (OriginalBorelWarmReplay.OriginalActualDualPositiveContraction.parameters mu L rho D) (1/2) =
      OriginalRobustTrajectory.radiusGetterFactor
        (settings (OriginalBorelWarmReplay.OriginalActualDualPositiveContraction.parameters mu L rho D)) (1/2) from hf]
    rfl
  · rfl

end
end FangqingBorelWarmScalarTransport

namespace FangqingBorelWarmScalarTransport
open OriginalSaddleImplicit
noncomputable section

theorem log_factor_eq_of_positive_rho
    {E F:Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F] [FiniteDimensional ℝ F]
    (J:Joint E F→ℝ) (mu L rho D tau:ℝ) (hrho:0<rho) (x u:E) (y:F) :
    OriginalBorelWarmReplay.OriginalMinimumWarmSolver.logFactor J mu L rho D tau x u y =
      OriginalMinimumWarmSolver.logFactor J mu L rho D tau x u y := by
  simp only [OriginalBorelWarmReplay.OriginalMinimumWarmSolver.logFactor,
    OriginalMinimumWarmSolver.logFactor,
    OriginalBorelWarmReplay.OriginalMinimumWarmSolver.secondLogFactor,
    OriginalMinimumWarmSolver.secondLogFactor,if_pos hrho,first_log_factor_eq,positive_log_factor_eq]

end
end FangqingBorelWarmScalarTransport
end

section
-- Source component: AdmissibleMainWarmBridge.lean

namespace OriginalAdmissibleMainReplay
namespace OriginalMinimumWarmSolver
open OriginalSaddleImplicit OriginalSaddleTransfer OriginalSaddleStability
noncomputable section
set_option maxHeartbeats 6000000
universe u
variable {E F : Type u}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F] [FiniteDimensional ℝ F]

def program (mu L rho D tau : ℝ) (x uInit : E) (yin : F) :=
  FangqingBorelWarmMinimum.jointProgram mu L rho D tau x uInit yin

def logFactor (J : Joint E F → ℝ) (mu L rho D tau : ℝ) (x uInit : E) (yin : F) :=
  2*OriginalBorelWarmReplay.OriginalMinimumWarmSolver.logFactor J mu L rho
    (FangqingBorelWarmMinimum.roundedRadius D) (OriginalWarmDyadicRounding.lower tau) x uInit yin

theorem actual_minimum_warm_solver
    (J : Joint E F → ℝ) (mu L rho D tau : ℝ)
    (hmu : 0 < mu) (hLmu : mu ≤ L) (hrho : 0 ≤ rho) (htau : 0 < tau)
    (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (hHess : ∀ z w : Joint E F, ‖fderiv ℝ (gradient J) z - fderiv ℝ (gradient J) w‖ ≤ rho * ‖z - w‖)
    (hsc : ∀ u : E, StrongConvexOn (Set.univ : Set F) mu (fun y => -JointSliceRegularity.curry J u y))
    (x uInit : E) (yin : F) (hwarm : ‖yin-vStar (JointSliceRegularity.curry J) L x‖ ≤ D) :
    let run := OriginalBetaATSTrial.execute (OriginalDualOracleProgram.actualOracle J) (program mu L rho D tau x uInit yin)
    ‖run.1-zStar (JointSliceRegularity.curry J) L x‖ ≤ tau ∧
      (run.2 : ℝ) ≤ (1+min (Real.sqrt (L/mu)) ((rho*D/mu)^(2/7:ℝ))) *
        logFactor J mu L rho D tau x uInit yin := by
  have hc : ∀ u : E, StrongConcaveOn (Set.univ : Set F) mu (fun y => J (WithLp.toLp 2 (u,y))) := by
    intro u
    have he : (fun y : F => J (WithLp.toLp 2 (u,y))) = JointSliceRegularity.curry J u := by
      funext y
      exact (congrArg J (JointSliceRegularity.point_eq_toLp u y)).symm
    rw [he]
    simpa only [StrongConcaveOn,Pi.neg_def,neg_neg] using (hsc u).neg
  have h := (FangqingBorelWarmMinimum.admissible_joint_minimum_warm_from_standing_joint
    J mu L rho D tau hmu hLmu hrho htau hC2 hLip hHess hc x uInit yin hwarm).2
  refine ⟨h.1,?_⟩
  dsimp only [program,logFactor]
  convert h.2 using 1 <;> ring

end
end OriginalMinimumWarmSolver

namespace OriginalUniformMinimumWarmLog
open OriginalSaddleImplicit OriginalSaddleTransfer OriginalDualResidualQueryBound
noncomputable section
set_option maxHeartbeats 6000000

def uniformFactor (mu L rho Dmax tau Obsmax : ℝ) :=
  2*_root_.OriginalUniformMinimumWarmLog.uniformFactor mu L rho (2*Dmax)
    (OriginalWarmDyadicRounding.lower tau) Obsmax

universe u
variable {E F : Type u}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F] [FiniteDimensional ℝ F]

theorem actual_minimum_log_factor_uniform
    (J : Joint E F → ℝ) (mu L rho D tau Dmax Obsmax : ℝ)
    (hmu : 0 < mu) (hL : 0 < L) (hrho : 0 < rho) (htau : 0 < tau)
    (hD : 0 ≤ D) (hDhi : D ≤ Dmax) (htauMax : tau ≤ Dmax)
    (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z-gradient J w‖ ≤ L*‖z-w‖)
    (hHess : ∀ z w : Joint E F, ‖fderiv ℝ (gradient J) z-fderiv ℝ (gradient J) w‖ ≤ rho*‖z-w‖)
    (hsc : ∀ u : E, StrongConvexOn (Set.univ : Set F) mu (fun y => -JointSliceRegularity.curry J u y))
    (x uInit : E) (yin : F) (hobs : observedRadius J L x uInit yin ≤ Obsmax) :
    0 ≤ uniformFactor mu L rho Dmax tau Obsmax ∧
      OriginalMinimumWarmSolver.logFactor J mu L rho D tau x uInit yin ≤
        uniformFactor mu L rho Dmax tau Obsmax := by
  have ht : 0 < OriginalWarmDyadicRounding.lower tau := OriginalWarmDyadicRounding.dyadic_positive _
  have hb := FangqingBorelWarmMinimum.rounded_radius_bounds D hD
  have hmax : 0 ≤ Dmax := hD.trans hDhi
  have h := _root_.OriginalUniformMinimumWarmLog.actual_minimum_log_factor_uniform
    J mu L rho (FangqingBorelWarmMinimum.roundedRadius D) (OriginalWarmDyadicRounding.lower tau)
    (2*Dmax) Obsmax hmu hL hrho ht (hD.trans hb.1)
    (hb.2.trans (mul_le_mul_of_nonneg_left hDhi (by norm_num)))
    ((OriginalWarmDyadicRounding.lower_bounds tau htau).2.trans (htauMax.trans (by linarith)))
    hC2 hLip hHess hsc x uInit yin hobs
  unfold uniformFactor OriginalMinimumWarmSolver.logFactor
  rw [FangqingBorelWarmScalarTransport.log_factor_eq_of_positive_rho J mu L rho _ _ hrho]
  change 0 ≤ 2*_ ∧ 2*_ ≤ 2*_
  constructor
  · exact mul_nonneg (by norm_num) h.1
  · exact mul_le_mul_of_nonneg_left h.2 (by norm_num)

end
end OriginalUniformMinimumWarmLog
end OriginalAdmissibleMainReplay
end

section
-- Source component: AdmissibleMainAnalyticReplay.lean

namespace OriginalAdmissibleMainReplay



namespace OriginalStatefulEnvelopeGD
open _root_.OriginalStatefulEnvelopeGD

open OriginalSaddleImplicit OriginalSaddleTransfer OriginalSaddleStability
open OriginalBetaATSTrial FangqingGetterComposition

noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 5000

structure Move (E F : Type*) where
  previous : E
  next : E
  warm : F
  radius : ℝ

structure Result (E F : Type*) where
  point : E
  saddle : Joint E F
  success : Bool
  moves : List (Move E F)

universe u
variable {E F : Type u}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

def squaredMovement (moves : List (Move E F)) : ℝ :=
  (moves.map (fun m => ‖m.next - m.previous‖ ^ 2)).sum

def moveCost (J : Joint E F → ℝ) (mu L rho tau : ℝ) (m : Move E F) : ℝ :=
  (1 + min (Real.sqrt (L / mu)) ((rho * m.radius / mu) ^ (2 / 7 : ℝ))) *
    OriginalMinimumWarmSolver.logFactor J mu L rho m.radius tau m.next m.next m.warm

def costSum (J : Joint E F → ℝ) (mu L rho tau : ℝ) (moves : List (Move E F)) : ℝ :=
  (moves.map (moveCost J mu L rho tau)).sum

def appendMove (m : Move E F) (out : Result E F) : Result E F :=
  { out with moves := m :: out.moves }

/-- A genuine stateful outer program. The next inner solve receives the previous
returned dual point. Every inner query is lowered to the original exact bundled oracle. -/
def loop (mu L rho tau eps : ℝ) : ℕ → E → Joint E F →
    GetterProgram (Joint E F) (OriginalDualOracleProgram.OracleAnswer (Joint E F)) (Result E F)
  | 0, x, w => .pure ⟨x, w, false, []⟩
  | n + 1, x, w =>
      let g := OriginalEnvelopeOracle.plugInGradient L x w
      if ‖g‖ ≤ eps / 2 then .pure ⟨x, w, true, []⟩
      else
        let s := OriginalOuterGD.step (2 * L) g
        let y := x + s
        let D := tau + 2 * Real.sqrt (L / mu) * ‖s‖
        let m : Move E F := ⟨x, y, w.snd, D⟩
        bind (OriginalMinimumWarmSolver.program mu L rho D tau y y w.snd) (fun wy =>
          map (appendMove m) (loop mu L rho tau eps n y wy))

def LoopSpec (J : Joint E F → ℝ) (mu L rho tau eps : ℝ) (n : ℕ) (x : E)
    (run : Result E F × ℕ) : Prop :=
  ‖run.1.saddle - zStar (JointSliceRegularity.curry J) L run.1.point‖ ≤ tau ∧
  (2 * L) / 4 * squaredMovement run.1.moves ≤
    saddleEnvelope (JointSliceRegularity.curry J) L x - saddleEnvelope (JointSliceRegularity.curry J) L run.1.point ∧
  (run.1.moves.length : ℝ) * (eps ^ 2 / (16 * (2 * L))) ≤
    saddleEnvelope (JointSliceRegularity.curry J) L x - saddleEnvelope (JointSliceRegularity.curry J) L run.1.point ∧
  (run.1.success = true → ‖gradient (saddleEnvelope (JointSliceRegularity.curry J) L) run.1.point‖ ≤ eps) ∧
  (run.1.success = false → run.1.moves.length = n) ∧
  (run.2 : ℝ) ≤ costSum J mu L rho tau run.1.moves ∧
  (∀ m ∈ run.1.moves,
    ‖m.warm - vStar (JointSliceRegularity.curry J) L m.next‖ ≤ m.radius ∧
    m.radius = tau + 2 * Real.sqrt (L / mu) * ‖m.next - m.previous‖ ∧
    saddleEnvelope (JointSliceRegularity.curry J) L m.previous ≤ saddleEnvelope (JointSliceRegularity.curry J) L x ∧
    saddleEnvelope (JointSliceRegularity.curry J) L m.next ≤ saddleEnvelope (JointSliceRegularity.curry J) L x)


theorem actual_loop_spec
    (J : Joint E F → ℝ) (mu L rho tau eps : ℝ)
    (hmu : 0 < mu) (hLmu : mu ≤ L) (hrho : 0 ≤ rho) (htau : 0 < tau) (heps : 0 < eps)
    (htolerance : 2 * L * tau ≤ eps / 16)
    (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (hHess : ∀ z w : Joint E F, ‖fderiv ℝ (gradient J) z - fderiv ℝ (gradient J) w‖ ≤ rho * ‖z - w‖)
    (hsc : ∀ u : E, StrongConvexOn (Set.univ : Set F) mu
      (fun y => -JointSliceRegularity.curry J u y))
    (n : ℕ) (x : E) (w : Joint E F)
    (hclose : ‖w - zStar (JointSliceRegularity.curry J) L x‖ ≤ tau) :
    LoopSpec J mu L rho tau eps n x
      (execute (OriginalDualOracleProgram.actualOracle J) (loop mu L rho tau eps n x w)) := by
  have hL : 0 < L := hmu.trans_le hLmu
  let Ef := saddleEnvelope (JointSliceRegularity.curry J) L
  have hJ := JointSliceRegularity.differentiable_joint_of_contDiff2 J hC2
  have hEdiff : Differentiable ℝ Ef :=
    OriginalEnvelopeRegularity.actual_envelope_differentiable J L mu hL hmu hC2 hsc hLip
  have hELip : ∀ x y : E, ‖gradient Ef x - gradient Ef y‖ ≤ (2 * L) * ‖x - y‖ := by
    intro a b
    exact OriginalEnvelopeGradientRegularity.envelope_gradient_lipschitz_from_slices
      (JointSliceRegularity.curry J) L mu hL hmu
      (JointSliceRegularity.differentiable_x_slice J hJ)
      (JointSliceRegularity.differentiable_y_slice J hJ) hsc
      (fun y a b => JointSliceRegularity.gradient_x_lipschitz_in_x J hJ L hLip a b y)
      (fun a y z => JointSliceRegularity.gradient_x_lipschitz_in_y J hJ L hLip a y z) a b
  induction n generalizing x w with
  | zero => simp [loop, execute, LoopSpec, squaredMovement, costSum, hclose]

  | succ n ih =>
      let g := OriginalEnvelopeOracle.plugInGradient L x w
      have hg : ‖g - gradient Ef x‖ ≤ eps / 16 :=
        ((OriginalEnvelopeOracle.envelope_oracle_from_joint_negative_slice J L mu rho hL hmu hrho
          hC2 hsc hLip hHess x w tau hclose).1).trans htolerance
      by_cases hstop : ‖g‖ ≤ eps / 2
      · have htrue : ‖gradient Ef x‖ ≤ eps := by
          have hn := norm_sub_le g (g - gradient Ef x)
          rw [show g - (g - gradient Ef x) = gradient Ef x by abel] at hn
          linarith only [hn, hg, hstop, heps]
        have hstop' : ‖OriginalEnvelopeOracle.plugInGradient L x w‖ ≤ eps / 2 := hstop
        simpa [loop, hstop', execute, LoopSpec, squaredMovement, costSum, hclose] using htrue

      · let s := OriginalOuterGD.step (2 * L) g
        let y := x + s
        let D := tau + 2 * Real.sqrt (L / mu) * ‖s‖
        let m : Move E F := ⟨x, y, w.snd, D⟩
        let p := OriginalMinimumWarmSolver.program mu L rho D tau y y w.snd
        let first := execute (OriginalDualOracleProgram.actualOracle J) p
        let rest := execute (OriginalDualOracleProgram.actualOracle J) (loop mu L rho tau eps n y first.1)
        have hs : y - x = s := by dsimp only [y]; abel
        have hprevious : ‖w.snd - vStar (JointSliceRegularity.curry J) L x‖ ≤ tau := by
          have hp := WithLp.norm_snd_le E (w - zStar (JointSliceRegularity.curry J) L x)
          exact hp.trans hclose
        have hwarm : ‖w.snd - vStar (JointSliceRegularity.curry J) L y‖ ≤ D := by
          have hd := OriginalWarmAmortization.actual_warm_dual_distance J L mu hL hmu hJ hLip hsc x y w.snd tau hprevious
          simpa only [hs] using hd
        have hfirst := OriginalMinimumWarmSolver.actual_minimum_warm_solver J mu L rho D tau
          hmu hLmu hrho htau hC2 hLip hHess hsc y y w.snd hwarm
        have hfirstClose : ‖first.1 - zStar (JointSliceRegularity.curry J) L y‖ ≤ tau := hfirst.1
        have hfirstCost : (first.2 : ℝ) ≤ moveCost J mu L rho tau m := hfirst.2
        have hrec := ih y first.1 hfirstClose
        change LoopSpec J mu L rho tau eps n y rest at hrec
        rcases hrec with ⟨hfinalClose, henergy, hcount, hterminal, hfuel, hqueries, htrace⟩
        have hdec := OriginalOuterGD.one_step_descent Ef (2 * L) eps (by positivity) heps hEdiff hELip x g hg hstop
        change (2 * L) / 4 * ‖s‖ ^ 2 ≤ Ef x - Ef y ∧
          eps ^ 2 / (16 * (2 * L)) ≤ Ef x - Ef y at hdec
        change (2 * L) / 4 * squaredMovement rest.1.moves ≤ Ef y - Ef rest.1.point at henergy
        change (rest.1.moves.length : ℝ) * (eps ^ 2 / (16 * (2 * L))) ≤ Ef y - Ef rest.1.point at hcount
        have hdescent : Ef y ≤ Ef x := by
          have hp : 0 ≤ (2 * L) / 4 * ‖s‖ ^ 2 := by positivity
          linarith only [hdec.1, hp]
        have hexec : execute (OriginalDualOracleProgram.actualOracle J) (loop mu L rho tau eps (n + 1) x w) =
            (appendMove m rest.1, first.2 + rest.2) := by
          have hstop' : ¬ ‖OriginalEnvelopeOracle.plugInGradient L x w‖ ≤ eps / 2 := hstop
          simp only [loop, if_neg hstop', execute_bind, execute_map]
          rfl
        rw [hexec]
        have hsq : squaredMovement (m :: rest.1.moves) = ‖s‖ ^ 2 + squaredMovement rest.1.moves := by
          simp only [squaredMovement, List.map_cons, List.sum_cons]
          change ‖y - x‖ ^ 2 + _ = _
          rw [hs]
        have hcost : costSum J mu L rho tau (m :: rest.1.moves) =
            moveCost J mu L rho tau m + costSum J mu L rho tau rest.1.moves := by
          simp only [costSum, List.map_cons, List.sum_cons]
        refine ⟨hfinalClose, ?_, ?_, hterminal, ?_, ?_, ?_⟩
        · change (2 * L) / 4 * squaredMovement (m :: rest.1.moves) ≤ Ef x - Ef rest.1.point
          rw [hsq]
          nlinarith only [hdec.1, henergy]
        · change ((m :: rest.1.moves).length : ℝ) * (eps ^ 2 / (16 * (2 * L))) ≤ Ef x - Ef rest.1.point
          simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
          nlinarith only [hdec.2, hcount]
        · intro hh
          exact congrArg Nat.succ (hfuel hh)
        · change ((first.2 + rest.2 : ℕ) : ℝ) ≤ costSum J mu L rho tau (m :: rest.1.moves)
          rw [Nat.cast_add, hcost]
          exact add_le_add hfirstCost hqueries
        · intro move hmem
          rcases List.mem_cons.mp hmem with hm | hm
          · subst move
            refine ⟨hwarm, ?_, le_refl _, hdescent⟩
            change D = tau + 2 * Real.sqrt (L / mu) * ‖y - x‖
            rw [hs]
          · obtain ⟨hlegal, hradius, hprev, hnext⟩ := htrace move hm
            exact ⟨hlegal, hradius, hprev.trans hdescent, hnext.trans hdescent⟩


def program (mu L rho D0 tau eps Delta : ℝ) (start : E) (yin : F) :
    GetterProgram (Joint E F) (OriginalDualOracleProgram.OracleAnswer (Joint E F)) (Result E F) :=
  bind (OriginalMinimumWarmSolver.program mu L rho D0 tau start start yin) (fun w =>
    loop mu L rho tau eps (OriginalOuterGD.fuel Delta (2 * L) eps) start w)

def initialCost (J : Joint E F → ℝ) (mu L rho D0 tau : ℝ) (start : E) (yin : F) : ℝ :=
  (1 + min (Real.sqrt (L / mu)) ((rho * D0 / mu) ^ (2 / 7 : ℝ))) *
    OriginalMinimumWarmSolver.logFactor J mu L rho D0 tau start start yin

/-- Finite actual original-oracle execution. The one-time initial warm solve is
separated from the one actual warm solve per executed outer move. All subsequent
centers retain the initial envelope gap, rather than importing an arbitrary-center
uniform primal-initialization assumption. -/
theorem actual_finite_termination_with_warm_trace
    (J : Joint E F → ℝ) (mu L rho D0 tau eps Delta lower : ℝ)
    (hmu : 0 < mu) (hLmu : mu ≤ L) (hrho : 0 ≤ rho) (htau : 0 < tau) (heps : 0 < eps)
    (htolerance : 2 * L * tau ≤ eps / 16)
    (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (hHess : ∀ z w : Joint E F, ‖fderiv ℝ (gradient J) z - fderiv ℝ (gradient J) w‖ ≤ rho * ‖z - w‖)
    (hsc : ∀ u : E, StrongConvexOn (Set.univ : Set F) mu
      (fun y => -JointSliceRegularity.curry J u y))
    (hbelow : ∀ x, lower ≤ saddleEnvelope (JointSliceRegularity.curry J) L x)
    (start : E) (yin : F)
    (hgap : saddleEnvelope (JointSliceRegularity.curry J) L start - lower ≤ Delta)
    (hwarm : ‖yin - vStar (JointSliceRegularity.curry J) L start‖ ≤ D0) :
    let run := execute (OriginalDualOracleProgram.actualOracle J)
      (program mu L rho D0 tau eps Delta start yin)
    run.1.success = true ∧
    ‖gradient (saddleEnvelope (JointSliceRegularity.curry J) L) run.1.point‖ ≤ eps ∧
    ‖run.1.saddle - zStar (JointSliceRegularity.curry J) L run.1.point‖ ≤ tau ∧
    squaredMovement run.1.moves ≤ 2 * Delta / L ∧
    (run.1.moves.length : ℝ) ≤ 32 * Delta * L / eps ^ 2 ∧
    (run.2 : ℝ) ≤ initialCost J mu L rho D0 tau start yin + costSum J mu L rho tau run.1.moves ∧
    (∀ m ∈ run.1.moves,
      ‖m.warm - vStar (JointSliceRegularity.curry J) L m.next‖ ≤ m.radius ∧
      m.radius = tau + 2 * Real.sqrt (L / mu) * ‖m.next - m.previous‖ ∧
      saddleEnvelope (JointSliceRegularity.curry J) L m.previous - lower ≤ Delta ∧
      saddleEnvelope (JointSliceRegularity.curry J) L m.next - lower ≤ Delta) := by
  let p0 := OriginalMinimumWarmSolver.program mu L rho D0 tau start start yin
  let first := execute (OriginalDualOracleProgram.actualOracle J) p0
  let n := OriginalOuterGD.fuel Delta (2 * L) eps
  let rest := execute (OriginalDualOracleProgram.actualOracle J) (loop mu L rho tau eps n start first.1)
  have hL : 0 < L := hmu.trans_le hLmu
  have hfirst := OriginalMinimumWarmSolver.actual_minimum_warm_solver J mu L rho D0 tau
    hmu hLmu hrho htau hC2 hLip hHess hsc start start yin hwarm
  have hfirstClose : ‖first.1 - zStar (JointSliceRegularity.curry J) L start‖ ≤ tau := hfirst.1
  have hfirstCost : (first.2 : ℝ) ≤ initialCost J mu L rho D0 tau start yin := hfirst.2
  have hloop := actual_loop_spec J mu L rho tau eps hmu hLmu hrho htau heps htolerance
    hC2 hLip hHess hsc n start first.1 hfirstClose
  change LoopSpec J mu L rho tau eps n start rest at hloop
  rcases hloop with ⟨hclose, henergy, hcount, hterminal, hfuel, hqueries, htrace⟩
  have hvalue : saddleEnvelope (JointSliceRegularity.curry J) L start -
      saddleEnvelope (JointSliceRegularity.curry J) L rest.1.point ≤ Delta := by
    linarith only [hbelow rest.1.point, hgap]
  have hcount' : (rest.1.moves.length : ℝ) ≤ 32 * Delta * L / eps ^ 2 := by
    have hc : 0 < eps ^ 2 / (16 * (2 * L)) := by positivity
    have hh := (le_div_iff₀ hc).mpr (hcount.trans hvalue)
    convert! hh using 1 <;> field_simp <;> ring
  have hsuccess : rest.1.success = true := by
    cases hb : rest.1.success with
    | true => rfl
    | false =>
        have hs := hfuel hb
        have hceil := Nat.le_ceil (16 * Delta * (2 * L) / eps ^ 2)
        rw [hs] at hcount'
        dsimp [n, OriginalOuterGD.fuel] at hcount'
        push_cast at hcount'
        have he : 16 * Delta * (2 * L) / eps ^ 2 = 32 * Delta * L / eps ^ 2 := by ring
        rw [he] at hceil hcount'
        linarith only [hcount', hceil]
  have hexec : execute (OriginalDualOracleProgram.actualOracle J)
      (program mu L rho D0 tau eps Delta start yin) = (rest.1, first.2 + rest.2) := by
    simp only [program, execute_bind]
    rfl
  rw [hexec]
  refine ⟨hsuccess, hterminal hsuccess, hclose, ?_, hcount', ?_, ?_⟩
  · apply (le_div_iff₀ hL).mpr
    linarith only [henergy, hvalue]
  · simp only [Nat.cast_add]
    exact add_le_add hfirstCost hqueries
  · intro m hm
    obtain ⟨hlegal, hradius, hprev, hnext⟩ := htrace m hm
    exact ⟨hlegal, hradius, by linarith only [hprev, hgap], by linarith only [hnext, hgap]⟩

end
end OriginalStatefulEnvelopeGD




namespace OriginalStatefulEnvelopeGD
open _root_.OriginalStatefulEnvelopeGD

open OriginalSaddleImplicit OriginalSaddleTransfer OriginalSaddleStability
open OriginalBetaATSTrial FangqingGetterComposition

universe u
variable {E F : Type u}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 5000

theorem actual_phi_gradient_lipschitz
    (J : Joint E F → ℝ) (mu L : ℝ) (hmu : 0 < mu) (hL : 0 < L)
    (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (hsc : ∀ u : E, StrongConvexOn (Set.univ : Set F) mu
      (fun y => -JointSliceRegularity.curry J u y))
    (x z : E) :
    ‖gradient (phi (JointSliceRegularity.curry J)) x - gradient (phi (JointSliceRegularity.curry J)) z‖ ≤
      L * (1 + L / mu) * ‖x - z‖ := by
  let f := JointSliceRegularity.curry J
  have hJ := JointSliceRegularity.differentiable_joint_of_contDiff2 J hC2
  have hdx := JointSliceRegularity.differentiable_x_slice J hJ
  have hdy := JointSliceRegularity.differentiable_y_slice J hJ
  have hxx := fun y u v => JointSliceRegularity.gradient_x_lipschitz_in_x J hJ L hLip u v y
  have hxy := fun u y v => JointSliceRegularity.gradient_x_lipschitz_in_y J hJ L hLip u y v
  have hg (u : E) : gradient (phi f) u = gradient (fun t => f t (yStar f u)) u :=
    (phi_hasGradientAt_yStar f L mu hL hmu hdx hdy hsc hxx hxy u).gradient
  rw [hg x, hg z]
  have h1 := hxx (yStar f x) x z
  have h2 := hxy z (yStar f x) (yStar f z)
  have hy := OriginalInitialSaddleRadius.actual_yStar_lipschitz J L mu hL hmu hJ hLip hsc x z
  have ht := norm_sub_le_norm_sub_add_norm_sub
    (gradient (fun t => f t (yStar f x)) x)
    (gradient (fun t => f t (yStar f x)) z)
    (gradient (fun t => f t (yStar f z)) z)
  have hmul := mul_le_mul_of_nonneg_left hy hL.le
  nlinarith only [h1, h2, ht, hmul]

def callerTolerance (mu L eps : ℝ) := eps / (128 * L * (1 + L / mu))

def caller (mu L rho Delta Ry eps : ℝ) (start : E) (yin : F) :
    GetterProgram (Joint E F) (OriginalDualOracleProgram.OracleAnswer (Joint E F)) (Result E F) :=
  program mu L rho (Ry + (L / mu) * Real.sqrt (Delta / L)) (callerTolerance mu L eps)
    (eps / 2) Delta start yin

/-- Original standing and original initialization data suffice for a real stateful
outer/inner execution and true primal-value stationarity. This result deliberately
retains the actual inner log-factor sum; its global frontier normalization is separate. -/
theorem actual_gradient_caller_from_original_inputs
    (J : Joint E F → ℝ) (mu L rho Delta Ry eps : ℝ)
    (hmu : 0 < mu) (hLmu : mu ≤ L) (hrho : 0 ≤ rho) (heps : 0 < eps)
    (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (hHess : ∀ z w : Joint E F, ‖fderiv ℝ (gradient J) z - fderiv ℝ (gradient J) w‖ ≤ rho * ‖z - w‖)
    (hsc : ∀ u : E, StrongConvexOn (Set.univ : Set F) mu
      (fun y => -JointSliceRegularity.curry J u y))
    (hbelow : BddBelow (Set.range (phi (JointSliceRegularity.curry J))))
    (start : E) (yin : F)
    (hgap : phi (JointSliceRegularity.curry J) start - sInf (Set.range (phi (JointSliceRegularity.curry J))) ≤ Delta)
    (hdual : ‖yin - yStar (JointSliceRegularity.curry J) start‖ ≤ Ry) :
    let tau := callerTolerance mu L eps
    let D0 := Ry + (L / mu) * Real.sqrt (Delta / L)
    let run := execute (OriginalDualOracleProgram.actualOracle J) (caller mu L rho Delta Ry eps start yin)
    run.1.success = true ∧
    ‖gradient (phi (JointSliceRegularity.curry J)) run.1.saddle.fst‖ ≤ eps ∧
    (run.1.moves.length : ℝ) ≤ 128 * Delta * L / eps ^ 2 ∧
    squaredMovement run.1.moves ≤ 2 * Delta / L ∧
    (run.2 : ℝ) ≤ initialCost J mu L rho D0 tau start yin + costSum J mu L rho tau run.1.moves ∧
    (∀ m ∈ run.1.moves,
      ‖m.warm - vStar (JointSliceRegularity.curry J) L m.next‖ ≤ m.radius ∧
      m.radius = tau + 2 * Real.sqrt (L / mu) * ‖m.next - m.previous‖ ∧
      OriginalDualResidualQueryBound.observedRadius J L m.next m.next m.warm ≤
        3 * (Real.sqrt (Delta / L) + m.radius)) := by
  let f := JointSliceRegularity.curry J
  let lower := sInf (Set.range (phi f))
  let tau := callerTolerance mu L eps
  let D0 := Ry + (L / mu) * Real.sqrt (Delta / L)
  let run := execute (OriginalDualOracleProgram.actualOracle J) (caller mu L rho Delta Ry eps start yin)
  have hL : 0 < L := hmu.trans_le hLmu
  have hratio : 0 < L / mu := by positivity
  have htau : 0 < tau := by unfold tau callerTolerance; positivity
  have htol : 2 * L * tau ≤ (eps / 2) / 16 := by
    dsimp [tau, callerTolerance]
    rw [show 2 * L * (eps / (128 * L * (1 + L / mu))) =
      (2 * L * eps) / (128 * L * (1 + L / mu)) by ring]
    apply (div_le_iff₀ (show 0 < 128 * L * (1 + L / mu) by positivity)).mpr
    have hp : 0 < L * eps := mul_pos hL heps
    have hq : 0 < L * eps * (L / mu) := mul_pos hp hratio
    nlinarith only [hp, hq]

  have hJ := JointSliceRegularity.differentiable_joint_of_contDiff2 J hC2
  have hdx := JointSliceRegularity.differentiable_x_slice J hJ
  have hdy := JointSliceRegularity.differentiable_y_slice J hJ
  have hxx := fun y u v => JointSliceRegularity.gradient_x_lipschitz_in_x J hJ L hLip u v y
  have hxy := fun u y v => JointSliceRegularity.gradient_x_lipschitz_in_y J hJ L hLip u y v
  obtain ⟨hPhi, hweak⟩ := phi_regular_from_slices f L mu hL hmu hdx hdy hsc hxx hxy
  have hE := saddleEnvelope_eq_moreau f L mu hmu hsc hdy
  have hElower : ∀ x, lower ≤ saddleEnvelope f L x := by
    intro x
    rw [hE, MoreauTransfer.envelope_eq_prox_objective (phi f) L hL hPhi hweak]
    have hp := csInf_le hbelow (Set.mem_range_self (MoreauTransfer.prox (phi f) L x))
    unfold MoreauTransfer.objective
    have hn : 0 ≤ L * ‖MoreauTransfer.prox (phi f) L x - x‖ ^ 2 := by positivity
    change lower ≤ phi f (MoreauTransfer.prox (phi f) L x) + _
    linarith only [hp, hn]
  have hEgap : saddleEnvelope f L start - lower ≤ Delta := by
    have hh := MoreauTransfer.envelope_le_original (phi f) L hL hPhi hweak start
    rw [← hE] at hh
    linarith only [hh, hgap]
  have hinit := OriginalInitialSaddleRadius.actual_initial_dual_radius J L mu Delta Ry
    hL hmu hC2 hLip hsc hbelow start yin hgap hdual
  have hh := actual_finite_termination_with_warm_trace J mu L rho D0 tau (eps / 2) Delta lower
    hmu hLmu hrho htau (by positivity) htol hC2 hLip hHess hsc hElower start yin hEgap hinit
  change run.1.success = true ∧ _ at hh
  rcases hh with ⟨htrue, hgradE, hclose, hsquares, hcount, hcost, htrace⟩
  change ‖gradient (saddleEnvelope f L) run.1.point‖ ≤ eps / 2 at hgradE
  have htransfer := exact_transfer_from_slices f L mu hL hmu hdx hdy hsc hxx hxy hbelow start Delta hgap
  have hPhiLip := actual_phi_gradient_lipschitz J mu L hmu hL hC2 hLip hsc
  have hfirst : ‖run.1.saddle.fst - uStar f L run.1.point‖ ≤ tau := by
    exact (WithLp.norm_fst_le E (run.1.saddle - zStar f L run.1.point)).trans hclose
  have houtput : ‖gradient (phi f) run.1.saddle.fst‖ ≤ eps := by
    have hd := hPhiLip run.1.saddle.fst (uStar f L run.1.point)
    have hm := mul_le_mul_of_nonneg_left hfirst (show 0 ≤ L * (1 + L / mu) by positivity)
    have hn := norm_le_norm_sub_add (gradient (phi f) run.1.saddle.fst)
      (gradient (phi f) (uStar f L run.1.point))
    change ‖gradient (phi f) run.1.saddle.fst - gradient (phi f) (uStar f L run.1.point)‖ ≤ _ at hd
    rw [← (htransfer.1 run.1.point).2] at hn hd
    have he : L * (1 + L / mu) * tau = eps / 128 := by
      dsimp [tau, callerTolerance]
      field_simp
      <;> ring
    rw [he] at hm
    linarith only [hd, hm, hn, hgradE, heps]
  refine ⟨htrue, houtput, ?_, hsquares, hcost, ?_⟩
  · have he : 32 * Delta * L / (eps / 2) ^ 2 = 128 * Delta * L / eps ^ 2 := by field_simp; ring
    rwa [he] at hcount
  · intro m hm
    obtain ⟨hlegal, hradius, hprev, hnext⟩ := htrace m hm
    have hb := (OriginalOuterPrimalInitialization.standing_primal_residual_bound J L mu lower Delta m.radius
      hL hmu hC2 hLip hsc (fun u => csInf_le hbelow ⟨u, rfl⟩) m.next m.warm hnext hlegal).2.2
    exact ⟨hlegal, hradius, hb⟩

end
end OriginalStatefulEnvelopeGD




open scoped BigOperators

namespace OriginalStatefulEnvelopeGD
open _root_.OriginalStatefulEnvelopeGD

open OriginalSaddleImplicit OriginalSaddleTransfer OriginalSaddleStability

universe u
variable {E F : Type u}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

noncomputable section
set_option maxHeartbeats 3000000

def moveLog (J : Joint E F → ℝ) (mu L rho tau : ℝ) (m : Move E F) : ℝ :=
  OriginalMinimumWarmSolver.logFactor J mu L rho m.radius tau m.next m.next m.warm

def maximumLog (J : Joint E F → ℝ) (mu L rho tau : ℝ) (moves : List (Move E F)) : ℝ :=
  (moves.map (moveLog J mu L rho tau)).foldr max 1

def polynomialBound (mu L rho tau : ℝ) (moves : List (Move E F)) : ℝ :=
  (moves.length : ℝ) * (1 + (rho * tau / mu) ^ (2 / 7 : ℝ)) +
    (rho / mu * (2 * Real.sqrt (L / mu))) ^ (2 / 7 : ℝ) *
      (moves.length : ℝ) ^ (6 / 7 : ℝ) * squaredMovement moves ^ (1 / 7 : ℝ)

theorem list_sum_as_fin {T : Type*} (l : List T) (f : T → ℝ) :
    (l.map f).sum = ∑ i : Fin l.length, f (l.get i) := by
  have he : List.ofFn (fun i : Fin l.length => f (l.get i)) = l.map f := by
    change List.ofFn (f ∘ l.get) = l.map f
    rw [← List.map_ofFn, List.ofFn_get]
  rw [← he, List.sum_ofFn]

theorem maximum_log_positive (J : Joint E F → ℝ) (mu L rho tau : ℝ) (moves : List (Move E F)) :
    1 ≤ maximumLog J mu L rho tau moves := by
  induction moves with
  | nil => rfl
  | cons m moves ih =>
      exact ih.trans (le_max_right _ _)

/-- Actual per-move costs are amortized over the actual physical step trace.
The finite maximum of log-factors is retained explicitly, rather than assumed to be
uniformly polylogarithmic. -/
theorem actual_cost_sum_holder_bound
    (J : Joint E F → ℝ) (mu L rho tau : ℝ) (hmu : 0 < mu) (hL : 0 < L)
    (hrho : 0 ≤ rho) (htau : 0 ≤ tau) (moves : List (Move E F))
    (hradii : ∀ m ∈ moves, m.radius = tau + 2 * Real.sqrt (L / mu) * ‖m.next - m.previous‖) :
    costSum J mu L rho tau moves ≤
      maximumLog J mu L rho tau moves * polynomialBound mu L rho tau moves := by
  let N := moves.length
  let step : Fin N → ℝ := fun i => ‖(moves.get i).next - (moves.get i).previous‖
  let radius : Fin N → ℝ := fun i => rho * (moves.get i).radius / mu
  have hradius : ∀ i : Fin N, 0 ≤ (moves.get i).radius := by
    intro i
    rw [hradii (moves.get i) (List.get_mem _ _)]
    positivity
  have hM : 0 ≤ maximumLog J mu L rho tau moves :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (maximum_log_positive J mu L rho tau moves)
  have hpoint : ∀ i : Fin N,
      moveCost J mu L rho tau (moves.get i) ≤
        maximumLog J mu L rho tau moves * (1 + radius i ^ (2 / 7 : ℝ)) := by
    intro i
    have hlog : moveLog J mu L rho tau (moves.get i) ≤ maximumLog J mu L rho tau moves := by
      exact List.le_max_of_le' 1 (List.mem_map.mpr ⟨moves.get i, List.get_mem _ _, rfl⟩) le_rfl
    have hscale : 0 ≤ 1 + min (Real.sqrt (L / mu)) (radius i ^ (2 / 7 : ℝ)) := by
      have hp : 0 ≤ radius i := div_nonneg (mul_nonneg hrho (hradius i)) hmu.le
      exact add_nonneg zero_le_one (le_min (Real.sqrt_nonneg _) (Real.rpow_nonneg hp _))
    have ha := mul_le_mul_of_nonneg_left hlog hscale
    have hb := mul_le_mul_of_nonneg_left
      (add_le_add_left (min_le_right (Real.sqrt (L / mu)) (radius i ^ (2 / 7 : ℝ))) 1) hM
    change (1 + min (Real.sqrt (L / mu)) (radius i ^ (2 / 7 : ℝ))) *
      moveLog J mu L rho tau (moves.get i) ≤ _
    exact ha.trans (by nlinarith only [hb])
  have hholder := OriginalWarmAmortization.warm_cost_sum_from_squared_steps
    (Finset.univ : Finset (Fin N)) step radius (rho * tau / mu)
    (rho / mu * (2 * Real.sqrt (L / mu))) (by positivity) (by positivity)
    (fun _ _ => norm_nonneg _) (fun i _ => div_nonneg (mul_nonneg hrho (hradius i)) hmu.le) (by
      intro i _
      have hi := hradii (moves.get i) (List.get_mem _ _)
      change rho * (moves.get i).radius / mu ≤ rho * tau / mu +
        rho / mu * (2 * Real.sqrt (L / mu)) * ‖(moves.get i).next - (moves.get i).previous‖
      rw [hi]
      ring_nf
      exact le_rfl)
  have hsq : ∑ i : Fin N, step i ^ 2 = squaredMovement moves :=
    (list_sum_as_fin moves (fun m => ‖m.next - m.previous‖ ^ 2)).symm
  have hpoly : ∑ i : Fin N, (1 + radius i ^ (2 / 7 : ℝ)) ≤ polynomialBound mu L rho tau moves := by
    simpa only [Finset.card_univ, Fintype.card_fin, hsq, N, polynomialBound] using hholder
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hpoint i)
  rw [← Finset.mul_sum] at hsum
  rw [costSum, list_sum_as_fin]
  exact hsum.trans (mul_le_mul_of_nonneg_left hpoly hM)


theorem squared_movement_nonnegative (moves : List (Move E F)) : 0 ≤ squaredMovement moves := by
  exact List.sum_nonneg (fun x hx => by
    obtain ⟨m, _, rfl⟩ := List.mem_map.mp hx
    exact sq_nonneg _)

theorem one_step_squared_le_total (moves : List (Move E F)) (m : Move E F) (hm : m ∈ moves) :
    ‖m.next - m.previous‖ ^ 2 ≤ squaredMovement moves := by
  induction moves with
  | nil => cases hm
  | cons head tail ih =>
      simp only [squaredMovement, List.map_cons, List.sum_cons]
      rcases List.mem_cons.mp hm with h | h
      · subst m
        exact le_add_of_nonneg_right (squared_movement_nonnegative tail)
      · exact (ih h).trans (le_add_of_nonneg_left (sq_nonneg _))

theorem warm_radii_uniform_bound (L mu tau Delta : ℝ) (hL : 0 < L)
    (moves : List (Move E F))
    (hsquares : squaredMovement moves ≤ 2 * Delta / L)
    (hradii : ∀ m ∈ moves, m.radius = tau + 2 * Real.sqrt (L / mu) * ‖m.next - m.previous‖) :
    ∀ m ∈ moves, m.radius ≤ tau + 2 * Real.sqrt (L / mu) * Real.sqrt (2 * Delta / L) := by
  have hnonneg : 0 ≤ 2 * Delta / L := (squared_movement_nonnegative moves).trans hsquares
  have hsq := Real.sq_sqrt hnonneg
  intro m hm
  have hstep := (one_step_squared_le_total moves m hm).trans hsquares
  have hnorm : ‖m.next - m.previous‖ ≤ Real.sqrt (2 * Delta / L) := by
    nlinarith only [hstep, hsq, norm_nonneg (m.next - m.previous), Real.sqrt_nonneg (2 * Delta / L)]
  rw [hradii m hm]
  have hh := mul_le_mul_of_nonneg_left hnorm (show 0 ≤ 2 * Real.sqrt (L / mu) by positivity)
  linarith only [hh]

end
end OriginalStatefulEnvelopeGD




namespace OriginalStatefulEnvelopeGD
open _root_.OriginalStatefulEnvelopeGD

open OriginalSaddleImplicit OriginalSaddleTransfer OriginalSaddleStability
open OriginalBetaATSTrial

universe u
variable {E F : Type u}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

noncomputable section
set_option maxHeartbeats 3000000

/-- The actual original-input caller, normalized to the middle-branch polynomial.
The only retained resource factor is the explicitly defined finite maximum of genuine
inner log-factors. Its global parameter-only majorant is not an assumption or conclusion. -/
theorem actual_gradient_frontier_with_explicit_logs
    (J : Joint E F → ℝ) (mu L rho Delta Ry eps : ℝ)
    (hmu : 0 < mu) (hLmu : mu ≤ L) (hrho : 0 ≤ rho) (heps : 0 < eps)
    (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (hHess : ∀ z w : Joint E F, ‖fderiv ℝ (gradient J) z - fderiv ℝ (gradient J) w‖ ≤ rho * ‖z - w‖)
    (hsc : ∀ u : E, StrongConvexOn (Set.univ : Set F) mu
      (fun y => -JointSliceRegularity.curry J u y))
    (hbelow : BddBelow (Set.range (phi (JointSliceRegularity.curry J))))
    (start : E) (yin : F)
    (hgap : phi (JointSliceRegularity.curry J) start - sInf (Set.range (phi (JointSliceRegularity.curry J))) ≤ Delta)
    (hdual : ‖yin - yStar (JointSliceRegularity.curry J) start‖ ≤ Ry) :
    let tau := callerTolerance mu L eps
    let D0 := Ry + (L / mu) * Real.sqrt (Delta / L)
    let run := execute (OriginalDualOracleProgram.actualOracle J) (caller mu L rho Delta Ry eps start yin)
    run.1.success = true ∧
    ‖gradient (phi (JointSliceRegularity.curry J)) run.1.saddle.fst‖ ≤ eps ∧
    (run.2 : ℝ) ≤ initialCost J mu L rho D0 tau start yin +
      512 * maximumLog J mu L rho tau run.1.moves * OriginalGDRateNormalization.A1 Delta L eps *
        (1 + OriginalGDRateNormalization.ratio mu L rho eps ^ (2 / 7 : ℝ)) ∧
    (∀ m ∈ run.1.moves, m.radius ≤
      tau + 2 * Real.sqrt (L / mu) * Real.sqrt (2 * Delta / L)) := by
  let tau := callerTolerance mu L eps
  let D0 := Ry + (L / mu) * Real.sqrt (Delta / L)
  let run := execute (OriginalDualOracleProgram.actualOracle J) (caller mu L rho Delta Ry eps start yin)
  have hL : 0 < L := hmu.trans_le hLmu
  have htau : 0 < tau := by unfold tau callerTolerance; positivity
  have h := actual_gradient_caller_from_original_inputs J mu L rho Delta Ry eps hmu hLmu hrho heps
    hC2 hLip hHess hsc hbelow start yin hgap hdual
  change run.1.success = true ∧ _ at h
  rcases h with ⟨htrue, hstationary, hcount, hsquares, hcost, htrace⟩
  have hradii : ∀ m ∈ run.1.moves, m.radius = tau + 2 * Real.sqrt (L / mu) * ‖m.next - m.previous‖ :=
    fun m hm => (htrace m hm).2.1
  have hholder := actual_cost_sum_holder_bound J mu L rho tau hmu hL hrho htau.le run.1.moves hradii
  have hDelta : 0 ≤ Delta := by
    have hh := csInf_le hbelow (Set.mem_range_self start)
    linarith only [hgap, hh]
  have hn : (run.1.moves.length : ℝ) ≤ 128 * OriginalGDRateNormalization.A1 Delta L eps := by
    convert! hcount using 1 <;> unfold OriginalGDRateNormalization.A1 <;> ring
  have hnormalize := OriginalGDRateNormalization.full_gradient_polynomial_normalization
    mu L rho eps Delta (run.1.moves.length : ℝ) (squaredMovement run.1.moves)
    hmu hLmu heps hrho hDelta (by positivity) (squared_movement_nonnegative _) hn hsquares
  have hp : polynomialBound mu L rho tau run.1.moves ≤
      512 * OriginalGDRateNormalization.A1 Delta L eps *
        (1 + OriginalGDRateNormalization.ratio mu L rho eps ^ (2 / 7 : ℝ)) := hnormalize
  have hM : 0 ≤ maximumLog J mu L rho tau run.1.moves :=
    zero_le_one.trans (maximum_log_positive J mu L rho tau run.1.moves)
  have hfinal := hholder.trans (mul_le_mul_of_nonneg_left hp hM)
  refine ⟨htrue, hstationary, ?_, warm_radii_uniform_bound L mu tau Delta hL _ hsquares hradii⟩
  have hc := add_le_add_left hfinal (initialCost J mu L rho D0 tau start yin)
  have hh := hcost.trans (by convert! hc using 1 <;> ring)
  convert! hh using 1 <;> ring

end
end OriginalStatefulEnvelopeGD




open scoped BigOperators

namespace OriginalStatefulEnvelopeGD
open _root_.OriginalStatefulEnvelopeGD

open OriginalSaddleImplicit

universe u
variable {E F : Type u}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

noncomputable section
set_option maxHeartbeats 2000000

/-- The same actual min-solver program also has the first-order polynomial cap;
no choice based on hidden instance data is required. -/
theorem actual_cost_sum_first_order_cap
    (J : Joint E F → ℝ) (mu L rho tau : ℝ) (hmu : 0 < mu) (hL : 0 < L)
    (hrho : 0 ≤ rho) (moves : List (Move E F))
    (hradii : ∀ m ∈ moves, 0 ≤ m.radius) :
    costSum J mu L rho tau moves ≤
      maximumLog J mu L rho tau moves * (moves.length : ℝ) * (1 + Real.sqrt (L / mu)) := by
  let M := maximumLog J mu L rho tau moves
  have hM : 0 ≤ M := zero_le_one.trans (maximum_log_positive J mu L rho tau moves)
  have hpoint (i : Fin moves.length) : moveCost J mu L rho tau (moves.get i) ≤ M * (1 + Real.sqrt (L / mu)) := by
    let m := moves.get i
    have hm : m ∈ moves := List.get_mem _ _
    have hD := hradii m hm
    have hlog : moveLog J mu L rho tau m ≤ M :=
      List.le_max_of_le' 1 (List.mem_map.mpr ⟨m, hm, rfl⟩) le_rfl
    have hscale : 0 ≤ 1 + min (Real.sqrt (L / mu)) ((rho * m.radius / mu) ^ (2 / 7 : ℝ)) := by
      have hp : 0 ≤ rho * m.radius / mu := by positivity
      exact add_nonneg zero_le_one (le_min (Real.sqrt_nonneg _) (Real.rpow_nonneg hp _))
    have hfirst := mul_le_mul_of_nonneg_left hlog hscale
    have hcap : 1 + min (Real.sqrt (L / mu)) ((rho * m.radius / mu) ^ (2 / 7 : ℝ)) ≤
        1 + Real.sqrt (L / mu) := add_le_add (le_refl (1 : ℝ)) (min_le_left _ _)
    have hsecond := mul_le_mul_of_nonneg_left hcap hM
    exact hfirst.trans (by convert! hsecond using 1 <;> ring)
  rw [costSum, list_sum_as_fin]
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hpoint i)
  apply hs.trans_eq
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

end
end OriginalStatefulEnvelopeGD




namespace OriginalStatefulEnvelopeGD
open _root_.OriginalStatefulEnvelopeGD

open OriginalSaddleImplicit OriginalSaddleTransfer OriginalSaddleStability
open OriginalBetaATSTrial

universe u
variable {E F : Type u}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 5000

def initialRadius (mu L Delta Ry : ℝ) := Ry + (L / mu) * Real.sqrt (Delta / L)

def globalWarmRadius (mu L Delta Ry eps : ℝ) :=
  max (initialRadius mu L Delta Ry)
    (callerTolerance mu L eps + 2 * Real.sqrt (L / mu) * Real.sqrt (2 * Delta / L))

def globalObservedRadius (mu L Delta Ry eps : ℝ) :=
  3 * (Real.sqrt (Delta / L) + globalWarmRadius mu L Delta Ry eps)

def globalLogFactor (mu L rho Delta Ry eps : ℝ) :=
  OriginalUniformMinimumWarmLog.uniformFactor mu L rho (globalWarmRadius mu L Delta Ry eps)
    (callerTolerance mu L eps) (globalObservedRadius mu L Delta Ry eps)

def initializationPolynomial (mu L rho Delta Ry : ℝ) :=
  1 + min (Real.sqrt (L / mu)) ((rho * initialRadius mu L Delta Ry / mu) ^ (2 / 7 : ℝ))

theorem maximum_log_le_of_all (J : Joint E F → ℝ) (mu L rho tau U : ℝ)
    (hU : 1 ≤ U) (moves : List (Move E F))
    (hall : ∀ m ∈ moves, moveLog J mu L rho tau m ≤ U) :
    maximumLog J mu L rho tau moves ≤ U := by
  induction moves with
  | nil => exact hU
  | cons m moves ih =>
      exact max_le (hall m List.mem_cons_self)
        (ih (fun a ha => hall a (List.mem_cons_of_mem _ ha)))

theorem uniform_minimum_factor_ge_one (mu L rho Dmax tau Obsmax : ℝ)
    (hmu : 0 < mu) (hL : 0 < L) (hrho : 0 ≤ rho) (htau : 0 < tau)
    (hmax : 0 ≤ Dmax) (hobs : 0 ≤ Obsmax) :
    1 ≤ OriginalUniformMinimumWarmLog.uniformFactor mu L rho Dmax tau Obsmax := by
  have ht : 0 < OriginalWarmDyadicRounding.lower tau := OriginalWarmDyadicRounding.dyadic_positive _
  have h := _root_.OriginalStatefulEnvelopeGD.uniform_minimum_factor_ge_one mu L rho (2*Dmax)
    (OriginalWarmDyadicRounding.lower tau) Obsmax hmu hL hrho ht (by positivity) hobs
  change 1 ≤ 2*_root_.OriginalUniformMinimumWarmLog.uniformFactor mu L rho (2*Dmax)
    (OriginalWarmDyadicRounding.lower tau) Obsmax
  linarith only [h]

/-- Both GD upper branches are realized by one actual stateful original bundled
oracle program, with an explicit common parameter-only product of logarithmic factors.
This theorem is a main-upper sub-result for rho>0, rather than the cubic/zero-rho branch. -/
theorem actual_uniform_gradient_main_branches
    (J : Joint E F → ℝ) (mu L rho Delta Ry eps : ℝ)
    (hmu : 0 < mu) (hLmu : mu ≤ L) (hrho : 0 < rho) (heps : 0 < eps)
    (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (hHess : ∀ z w : Joint E F, ‖fderiv ℝ (gradient J) z - fderiv ℝ (gradient J) w‖ ≤ rho * ‖z - w‖)
    (hsc : ∀ u : E, StrongConvexOn (Set.univ : Set F) mu (fun y => -JointSliceRegularity.curry J u y))
    (hbelow : BddBelow (Set.range (phi (JointSliceRegularity.curry J))))
    (start : E) (yin : F)
    (hgap : phi (JointSliceRegularity.curry J) start - sInf (Set.range (phi (JointSliceRegularity.curry J))) ≤ Delta)
    (hdual : ‖yin - yStar (JointSliceRegularity.curry J) start‖ ≤ Ry) :
    let run := execute (OriginalDualOracleProgram.actualOracle J) (caller mu L rho Delta Ry eps start yin)
    let U := globalLogFactor mu L rho Delta Ry eps
    1 ≤ U ∧ run.1.success = true ∧
    ‖gradient (phi (JointSliceRegularity.curry J)) run.1.saddle.fst‖ ≤ eps ∧
    (run.2 : ℝ) ≤ U * (initializationPolynomial mu L rho Delta Ry +
      512 * OriginalGDRateNormalization.A1 Delta L eps *
        (1 + OriginalGDRateNormalization.ratio mu L rho eps ^ (2 / 7 : ℝ))) ∧
    (run.2 : ℝ) ≤ U * (initializationPolynomial mu L rho Delta Ry +
      256 * Real.sqrt (L / mu) * OriginalGDRateNormalization.A1 Delta L eps) := by
  let tau := callerTolerance mu L eps
  let D0 := initialRadius mu L Delta Ry
  let R := globalWarmRadius mu L Delta Ry eps
  let Obs := globalObservedRadius mu L Delta Ry eps
  let U := globalLogFactor mu L rho Delta Ry eps
  let run := execute (OriginalDualOracleProgram.actualOracle J) (caller mu L rho Delta Ry eps start yin)
  have hL : 0 < L := hmu.trans_le hLmu
  have htau : 0 < tau := by dsimp [tau, callerTolerance]; positivity
  have hRtau : tau ≤ R := by
    apply le_trans ?_ (le_max_right _ _)
    exact le_add_of_nonneg_right (by positivity)
  have hR0 : D0 ≤ R := le_max_left _ _
  have hR : 0 < R := htau.trans_le hRtau
  have hObs : 0 ≤ Obs := by dsimp [Obs, globalObservedRadius]; positivity
  have hU : 1 ≤ U := uniform_minimum_factor_ge_one mu L rho R tau Obs hmu hL hrho.le htau hR.le hObs
  have hU0 : 0 ≤ U := zero_le_one.trans hU
  have hbase := actual_gradient_caller_from_original_inputs J mu L rho Delta Ry eps hmu hLmu hrho.le heps
    hC2 hLip hHess hsc hbelow start yin hgap hdual
  change run.1.success = true ∧ _ at hbase
  rcases hbase with ⟨htrue, hstationary, hcount, hsquares, hcost, htrace⟩
  have hfront := actual_gradient_frontier_with_explicit_logs J mu L rho Delta Ry eps hmu hLmu hrho.le heps
    hC2 hLip hHess hsc hbelow start yin hgap hdual
  change run.1.success = true ∧ _ at hfront
  have hrad : ∀ m ∈ run.1.moves, m.radius ≤ R := by
    intro m hm
    exact ((hfront.2.2.2 m hm)).trans (le_max_right _ _)
  have hlogs : ∀ m ∈ run.1.moves, moveLog J mu L rho tau m ≤ U := by
    intro m hm
    obtain ⟨hlegal, _, hobs⟩ := htrace m hm
    have hD : 0 ≤ m.radius := (norm_nonneg _).trans hlegal
    have hobsR : OriginalDualResidualQueryBound.observedRadius J L m.next m.next m.warm ≤ Obs := by
      exact hobs.trans (by dsimp [Obs, globalObservedRadius]; linarith only [hrad m hm])
    exact (OriginalUniformMinimumWarmLog.actual_minimum_log_factor_uniform J mu L rho m.radius tau R Obs
      hmu hL hrho htau hD (hrad m hm) hRtau hC2 hLip hHess hsc m.next m.next m.warm hobsR).2
  have hM := maximum_log_le_of_all J mu L rho tau U hU run.1.moves hlogs
  have hinit := OriginalInitialSaddleRadius.actual_initial_dual_radius J L mu Delta Ry hL hmu hC2 hLip hsc hbelow start yin hgap hdual
  have hD0 : 0 ≤ D0 := (norm_nonneg _).trans hinit
  have hinitObs := OriginalInitialSaddleRadius.actual_initial_primal_residual J L mu Delta Ry hL hmu hC2 hLip hsc hbelow start yin hgap hdual
  have hinitObsR : OriginalDualResidualQueryBound.observedRadius J L start start yin ≤ Obs := by
    have hh : 3 * (Real.sqrt (Delta / L) + D0) ≤ Obs := by
      change 3 * (Real.sqrt (Delta / L) + D0) ≤ 3 * (Real.sqrt (Delta / L) + R)
      linarith only [hR0]
    exact hinitObs.trans hh
  have hinitLog := (OriginalUniformMinimumWarmLog.actual_minimum_log_factor_uniform J mu L rho D0 tau R Obs
    hmu hL hrho htau hD0 hR0 hRtau hC2 hLip hHess hsc start start yin hinitObsR).2
  have hI0 : 0 ≤ initializationPolynomial mu L rho Delta Ry := by
    dsimp [initializationPolynomial]
    have hp : 0 ≤ rho * initialRadius mu L Delta Ry / mu := by change 0 ≤ rho * D0 / mu; positivity
    positivity
  have hinitCost : initialCost J mu L rho D0 tau start yin ≤ initializationPolynomial mu L rho Delta Ry * U :=
    mul_le_mul_of_nonneg_left hinitLog hI0
  have hDelta : 0 ≤ Delta := by
    have hi := csInf_le hbelow (Set.mem_range_self start)
    linarith only [hgap, hi]
  have ha : 0 ≤ OriginalGDRateNormalization.A1 Delta L eps := by unfold OriginalGDRateNormalization.A1; positivity
  have hr : 0 ≤ OriginalGDRateNormalization.ratio mu L rho eps ^ (2 / 7 : ℝ) := by
    unfold OriginalGDRateNormalization.ratio
    positivity
  have hmiddle := hfront.2.2.1
  change (run.2 : ℝ) ≤ initialCost J mu L rho D0 tau start yin +
    512 * maximumLog J mu L rho tau run.1.moves * OriginalGDRateNormalization.A1 Delta L eps *
      (1 + OriginalGDRateNormalization.ratio mu L rho eps ^ (2 / 7 : ℝ)) at hmiddle
  change (run.2 : ℝ) ≤ initialCost J mu L rho D0 tau start yin + costSum J mu L rho tau run.1.moves at hcost
  have hMscale := mul_le_mul_of_nonneg_right hM
    (show 0 ≤ 512 * OriginalGDRateNormalization.A1 Delta L eps * (1 + OriginalGDRateNormalization.ratio mu L rho eps ^ (2 / 7 : ℝ)) by positivity)
  have hmiddleBound : (run.2 : ℝ) ≤ U * (initializationPolynomial mu L rho Delta Ry +
      512 * OriginalGDRateNormalization.A1 Delta L eps * (1 + OriginalGDRateNormalization.ratio mu L rho eps ^ (2 / 7 : ℝ))) := by
    nlinarith only [hmiddle, hMscale, hinitCost]
  have hcap := actual_cost_sum_first_order_cap J mu L rho tau hmu hL hrho.le run.1.moves
    (fun m hm => (norm_nonneg _).trans (htrace m hm).1)
  have hsqrt : 1 ≤ Real.sqrt (L / mu) := by
    have hratio : 1 ≤ L / mu := (le_div_iff₀ hmu).mpr (by simpa using hLmu)
    nlinarith [Real.sq_sqrt (show 0 ≤ L / mu by positivity), Real.sqrt_nonneg (L / mu)]
  have hcountA : (run.1.moves.length : ℝ) ≤ 128 * OriginalGDRateNormalization.A1 Delta L eps := by
    convert! hcount using 1 <;> unfold OriginalGDRateNormalization.A1 <;> ring
  have hscalar : (run.1.moves.length : ℝ) * (1 + Real.sqrt (L / mu)) ≤
      256 * Real.sqrt (L / mu) * OriginalGDRateNormalization.A1 Delta L eps := by
    have hn := mul_le_mul_of_nonneg_right hcountA (show 0 ≤ 1 + Real.sqrt (L / mu) by positivity)
    have hp := mul_nonneg ha (sub_nonneg.mpr hsqrt)
    nlinarith only [hn, hp]
  have hcap2 : costSum J mu L rho tau run.1.moves ≤
      U * (256 * Real.sqrt (L / mu) * OriginalGDRateNormalization.A1 Delta L eps) := hcap.trans (by
    have hN0 : 0 ≤ (run.1.moves.length : ℝ) * (1 + Real.sqrt (L / mu)) := by positivity
    have hMa := mul_le_mul_of_nonneg_right hM hN0
    have hUb := mul_le_mul_of_nonneg_left hscalar hU0
    nlinarith only [hMa, hUb])
  refine ⟨hU, htrue, hstationary, hmiddleBound, ?_⟩
  nlinarith only [hcost, hinitCost, hcap2]

end
end OriginalStatefulEnvelopeGD




namespace OriginalZeroHessianReconstruction
open _root_.OriginalZeroHessianReconstruction

open OriginalSaddleImplicit OriginalSaddleTransfer OriginalSaddleStability
open OriginalBetaATSTrial OriginalDualOracleProgram

noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 5000

variable {Z : Type*} [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]
  [FiniteDimensional ℝ Z]

def jet (J : Z → ℝ) (z : Z) : OracleAnswer Z :=
  ⟨J z, gradient J z, fderiv ℝ (gradient J) z⟩

/-- This is the explicit quadratic built from one exact bundle at zero. -/
def quadratic (a : OracleAnswer Z) (z : Z) : ℝ :=
  a.value + OriginalOuterCubic.model a.grad a.hess 0 z

def polynomialOracle (a : OracleAnswer Z) (z : Z) : OracleAnswer Z :=
  ⟨quadratic a z, a.grad + CertifiedATS.sympart a.hess z, CertifiedATS.sympart a.hess⟩

theorem polynomial_oracle_is_exact (a : OracleAnswer Z) :
    jet (quadratic a) = polynomialOracle a := by
  have hg (z : Z) : HasGradientAt (quadratic a) (a.grad + CertifiedATS.sympart a.hess z) z := by
    have hh := (OriginalOuterCubic.model_hasGradientAt a.grad a.hess 0 z).hasFDerivAt.const_add a.value
    apply hasGradientAt_iff_hasFDerivAt.mpr
    convert! hh using 1 <;> simp [quadratic]
  have hgrad : gradient (quadratic a) = fun z => a.grad + CertifiedATS.sympart a.hess z :=
    funext (fun z => (hg z).gradient)
  funext z
  have hfd : fderiv ℝ (gradient (quadratic a)) z = CertifiedATS.sympart a.hess := by
    rw [hgrad]
    exact ((CertifiedATS.sympart a.hess).hasFDerivAt.const_add a.grad).fderiv
  change (⟨quadratic a z, gradient (quadratic a) z,
    fderiv ℝ (gradient (quadratic a)) z⟩ : OracleAnswer Z) = _
  rw [hfd]
  congr 1
  exact congrFun hgrad z

theorem exact_global_quadratic_reconstruction (J : Z → ℝ) (hC2 : ContDiff ℝ 2 J)
    (hzero : ∀ z w : Z, ‖fderiv ℝ (gradient J) z - fderiv ℝ (gradient J) w‖ ≤ 0 * ‖z - w‖) :
    quadratic (jet J 0) = J := by
  let H := fderiv ℝ (gradient J) 0
  have hJ : Differentiable ℝ J := hC2.differentiable (by norm_num)
  have hgrad : Differentiable ℝ (gradient J) :=
    (OriginalSaddleImplicit.contDiff_gradient_of_contDiff2 J hC2).differentiable (by norm_num)
  have hconstant (z : Z) : fderiv ℝ (gradient J) z = H := by
    have hh := hzero z 0
    rw [zero_mul] at hh
    exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hh (norm_nonneg _)))
  have haffine : gradient J = fun z => gradient J 0 + H z := by
    apply eq_of_fderiv_eq hgrad (fun z => (H.hasFDerivAt.const_add (gradient J 0)).differentiableAt)
      (fun z => (hconstant z).trans (H.hasFDerivAt.const_add (gradient J 0)).fderiv.symm) 0
    simp only [map_zero,add_zero]
  have hsym : CertifiedATS.sympart H = H := by
    have hself := OriginalSaddleTangent.gradient_derivative_selfadjoint J hC2 (0 : Z)
    change H.adjoint = H at hself
    ext z
    simp only [CertifiedATS.sympart,ContinuousLinearMap.smul_apply,ContinuousLinearMap.add_apply,hself]
    module
  let Q := quadratic (jet J 0)
  have hQ (z : Z) : HasGradientAt Q (gradient J 0 + H z) z := by
    have hh := (OriginalOuterCubic.model_hasGradientAt (gradient J 0) H 0 z).hasFDerivAt.const_add (J 0)
    rw [hsym] at hh
    apply hasGradientAt_iff_hasFDerivAt.mpr
    convert! hh using 1 <;> simp [Q,quadratic,jet,H]
  have heq : J = Q := by
    refine eq_of_fderiv_eq hJ (fun z => (hQ z).differentiableAt) ?_ 0 ?_
    · intro z
      rw [(hJ z).hasGradientAt.hasFDerivAt.fderiv,(hQ z).hasFDerivAt.fderiv,haffine]
      simp only [map_zero,add_zero]
    · simp [Q,quadratic,jet,OriginalOuterCubic.model]
  exact heq.symm

universe u
variable {E F : Type u}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

/-- Only the initial bundle is an original-oracle request. All later evaluations
are explicit evaluations of the reconstructed polynomial, hence free transcript
computation in the paper's model. The existing finite certified solver is reused
with this synthetic polynomial oracle. -/
def program (mu L Delta Ry eps : ℝ) (start : E) (yin : F) :
    GetterProgram (Joint E F) (OracleAnswer (Joint E F)) E :=
  .ask 0 (fun a => .pure
    ((OriginalBetaATSTrial.execute (polynomialOracle a)
      (OriginalStatefulEnvelopeGD.caller mu L 0 Delta Ry eps start yin)).1.saddle.fst))

theorem one_original_query_suffices_when_hessian_is_constant
    (J : Joint E F → ℝ) (mu L Delta Ry eps : ℝ)
    (hmu : 0 < mu) (hLmu : mu ≤ L) (heps : 0 < eps)
    (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (hzero : ∀ z w : Joint E F, ‖fderiv ℝ (gradient J) z - fderiv ℝ (gradient J) w‖ ≤ 0 * ‖z - w‖)
    (hsc : ∀ u : E, StrongConvexOn (Set.univ : Set F) mu (fun y => -JointSliceRegularity.curry J u y))
    (hbelow : BddBelow (Set.range (phi (JointSliceRegularity.curry J))))
    (start : E) (yin : F)
    (hgap : phi (JointSliceRegularity.curry J) start - sInf (Set.range (phi (JointSliceRegularity.curry J))) ≤ Delta)
    (hdual : ‖yin - yStar (JointSliceRegularity.curry J) start‖ ≤ Ry) :
    let run := OriginalBetaATSTrial.execute (actualOracle J) (program mu L Delta Ry eps start yin)
    run.2 = 1 ∧ ‖gradient (phi (JointSliceRegularity.curry J)) run.1‖ ≤ eps := by
  have hmodel := exact_global_quadratic_reconstruction J hC2 hzero
  have horacle : polynomialOracle (actualOracle J 0) = actualOracle J := by
    change polynomialOracle (jet J 0) = jet J
    rw [← polynomial_oracle_is_exact,hmodel]
  have hrun := OriginalStatefulEnvelopeGD.actual_gradient_caller_from_original_inputs J mu L 0 Delta Ry eps
    hmu hLmu (by norm_num) heps hC2 hLip hzero hsc hbelow start yin hgap hdual
  simp only [program,OriginalBetaATSTrial.execute,horacle]
  exact ⟨trivial,hrun.2.1⟩

end
end OriginalZeroHessianReconstruction





namespace OriginalBorelOuterCubic
open _root_.OriginalBorelOuterCubic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]

noncomputable section

def model (v : E) (H : E →L[ℝ] E) (M : ℝ) (s : E) : ℝ :=
  inner ℝ v s + (1 / 2 : ℝ) * inner ℝ (H s) s + M / 6 * ‖s‖ ^ 3

theorem model_hasGradientAt (v : E) (H : E →L[ℝ] E) (M : ℝ) (s : E) :
    HasGradientAt (model v H M) (v + CertifiedATS.sympart H s + (M / 2 * ‖s‖) • s) s := by
  have heq : CertifiedATS.model v H M 0 = model v H M := by
    funext d
    simp only [CertifiedATS.model, model, mul_zero, div_zero, zero_mul, add_zero]
  have hh := CertifiedATS.model_hasGradientAt v H M 0 s
  rw [heq] at hh
  simpa only [inv_zero, zero_smul, add_zero] using hh

theorem model_lower_bound (v : E) (H : E →L[ℝ] E) (M : ℝ) (s : E) :
    -‖v‖ * ‖s‖ - ‖H‖ / 2 * ‖s‖ ^ 2 + M / 6 * ‖s‖ ^ 3 ≤ model v H M s := by
  have hv := real_inner_le_norm (-v) s
  rw [inner_neg_left, norm_neg] at hv
  have hH := real_inner_le_norm (-(H s)) s
  rw [inner_neg_left, norm_neg] at hH
  have hn := mul_le_mul_of_nonneg_right (H.le_opNorm s) (norm_nonneg s)
  unfold model
  nlinarith only [hv, hH, hn]

def modelRadius (v : E) (H : E →L[ℝ] E) (M : ℝ) : ℝ :=
  1 + 12 * (‖v‖ + ‖H‖) / M

theorem model_nonnegative_outside (v : E) (H : E →L[ℝ] E) (M : ℝ) (hM : 0 < M)
    (s : E) (hout : modelRadius v H M ≤ ‖s‖) : 0 ≤ model v H M s := by
  have hR : 1 ≤ modelRadius v H M := by
    have hh : 0 ≤ 12 * (‖v‖ + ‖H‖) / M := by positivity
    unfold modelRadius
    linarith only [hh]
  have hr : 1 ≤ ‖s‖ := hR.trans hout
  have hMr : 12 * (‖v‖ + ‖H‖) ≤ M * ‖s‖ := by
    have hh := mul_le_mul_of_nonneg_left hout hM.le
    dsimp only [modelRadius] at hh
    have hid : M * (1 + 12 * (‖v‖ + ‖H‖) / M) = M + 12 * (‖v‖ + ‖H‖) := by
      field_simp <;> ring
    rw [hid] at hh
    linarith only [hh, hM]
  have hmul := mul_le_mul_of_nonneg_right hMr (sq_nonneg ‖s‖)
  have hvr : ‖v‖ * ‖s‖ ≤ ‖v‖ * ‖s‖ ^ 2 := by
    have hh : ‖s‖ ≤ ‖s‖ ^ 2 := by nlinarith only [hr]
    exact mul_le_mul_of_nonneg_left hh (norm_nonneg v)
  have hH0 := mul_nonneg (norm_nonneg H) (sq_nonneg ‖s‖)
  have hv0 := mul_nonneg (norm_nonneg v) (sq_nonneg ‖s‖)
  have hlower := model_lower_bound v H M s
  nlinarith only [hmul, hvr, hH0, hv0, hlower]

theorem exists_model_minimizer (v : E) (H : E →L[ℝ] E) (M : ℝ) (hM : 0 < M) :
    ∃ s : E, ∀ t : E, model v H M s ≤ model v H M t := by
  let R := modelRadius v H M
  have hR : 0 < R := by dsimp only [R, modelRadius]; positivity
  have hzero : (0 : E) ∈ Metric.closedBall 0 R := by
    simpa only [Metric.mem_closedBall, dist_self] using hR.le
  have hcont : Continuous (model v H M) :=
    (show Differentiable ℝ (model v H M) from fun s => (model_hasGradientAt v H M s).differentiableAt).continuous
  obtain ⟨s, hs, hmin⟩ := (isCompact_closedBall (0 : E) R).exists_isMinOn ⟨0, hzero⟩ hcont.continuousOn
  refine ⟨s, ?_⟩
  intro t
  by_cases ht : t ∈ Metric.closedBall 0 R
  · exact hmin ht
  · have hout : modelRadius v H M ≤ ‖t‖ := by
      have hh : R < ‖t‖ := by simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using ht
      exact hh.le
    have hs0 : model v H M s ≤ model v H M 0 := hmin hzero
    have h0 : model v H M 0 = 0 := by simp only [model, inner_zero_right, norm_zero]; ring
    rw [h0] at hs0
    exact hs0.trans (model_nonnegative_outside v H M hM t hout)

def minimizer (v : E) (H : E →L[ℝ] E) (M : ℝ) : E :=
  if hM : 0 < M then OriginalCubicBorelSelection.select v H M hM else 0

theorem minimizer_is_actual (v : E) (H : E →L[ℝ] E) (M : ℝ) (hM : 0 < M) :
    ∀ t : E, model v H M (minimizer v H M) ≤ model v H M t := by
  unfold minimizer
  rw [dif_pos hM]
  exact OriginalCubicBorelSelection.select_is_actual v H M hM

theorem minimizer_equation_and_decrease (v : E) (H : E →L[ℝ] E) (M : ℝ) (hM : 0 < M) :
    let s := minimizer v H M
    v + CertifiedATS.sympart H s + (M / 2 * ‖s‖) • s = 0 ∧
      model v H M s ≤ -(M / 12) * ‖s‖ ^ 3 := by
  dsimp only
  let s := minimizer v H M
  have hmin := minimizer_is_actual v H M hM
  have hloc : IsLocalMin (model v H M) s := Filter.Eventually.of_forall hmin
  have hg := hloc.hasFDerivAt_eq_zero (model_hasGradientAt v H M s).hasFDerivAt
  have heq : v + CertifiedATS.sympart H s + (M / 2 * ‖s‖) • s = 0 := by
    have hh := congrArg (fun D : E →L[ℝ] ℝ => D (v + CertifiedATS.sympart H s + (M / 2 * ‖s‖) • s)) hg
    simpa only [InnerProductSpace.toDual_apply_apply, ContinuousLinearMap.zero_apply,
      real_inner_self_eq_norm_sq, sq_eq_zero_iff, norm_eq_zero] using hh
  have hinner := congrArg (fun w : E => inner ℝ w s) heq
  simp only [inner_add_left, real_inner_smul_left, inner_zero_left,
    real_inner_self_eq_norm_sq] at hinner
  have hsym : inner ℝ (CertifiedATS.sympart H s) s = inner ℝ (H s) s := by
    simp only [CertifiedATS.sympart, smul_apply, add_apply, real_inner_smul_left,
      inner_add_left, ContinuousLinearMap.adjoint_inner_left, real_inner_comm s (H s)]
    ring
  rw [hsym] at hinner
  have hmirror := hmin (-s)
  have hneg : model v H M (-s) = -inner ℝ v s + (1 / 2 : ℝ) * inner ℝ (H s) s + M / 6 * ‖s‖ ^ 3 := by
    simp only [model, inner_neg_right, map_neg, inner_neg_left, neg_neg, norm_neg]
  rw [hneg] at hmirror
  dsimp only [model] at hmirror ⊢
  refine ⟨heq, ?_⟩
  nlinarith only [hinner, hmirror]

end
end OriginalBorelOuterCubic


namespace OriginalBorelOuterCubic
open _root_.OriginalBorelOuterCubic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]

theorem cubic_taylor_upper
    (f : E → ℝ) (hC2 : ContDiff ℝ 2 f) (M : ℝ) (hM : 0 < M)
    (hH : ∀ x y : E, ‖fderiv ℝ (gradient f) x - fderiv ℝ (gradient f) y‖ ≤ M * ‖x - y‖)
    (z s : E) :
    f (z + s) ≤ f z + inner ℝ (gradient f z) s +
      (1 / 2 : ℝ) * inner ℝ (fderiv ℝ (gradient f) z s) s + M / 6 * ‖s‖ ^ 3 := by
  let H := fderiv ℝ (gradient f) z
  let phi : ℝ → ℝ := fun t => f (z + t • s) - f z - t * inner ℝ (gradient f z) s -
    t ^ 2 / 2 * inner ℝ (H s) s - (M / 6 * ‖s‖ ^ 3) * t ^ 3
  let phi' : ℝ → ℝ := fun t => inner ℝ (gradient f (z + t • s)) s -
    inner ℝ (gradient f z) s - t * inner ℝ (H s) s - (M / 2 * ‖s‖ ^ 3) * t ^ 2
  have hdiff : Differentiable ℝ f := hC2.differentiable (by norm_num)
  have hderiv : ∀ t : ℝ, HasDerivAt phi (phi' t) t := by
    intro t
    have hcurve : HasDerivAt (fun t : ℝ => z + t • s) s t := by
      simpa only [one_smul, id_eq] using ((hasDerivAt_id t).smul_const s).const_add z
    have hgcurve : HasDerivAt (fun t : ℝ => f (z + t • s))
        (inner ℝ (gradient f (z + t • s)) s) t := by
      simpa only [Function.comp_def, inner_gradient_left] using
        ((hdiff (z + t • s)).hasFDerivAt.comp_hasDerivAt t hcurve)
    have hlin := (hasDerivAt_id t).mul_const (inner ℝ (gradient f z) s)
    have hquad := (((hasDerivAt_id t).pow 2).div_const 2).mul_const (inner ℝ (H s) s)
    have hcubic := ((hasDerivAt_id t).pow 3).const_mul (M / 6 * ‖s‖ ^ 3)
    simp only [id_eq, Pi.pow_apply] at hlin hquad hcubic
    have hh := (((hgcurve.sub_const (f z)).sub hlin).sub hquad).sub hcubic
    convert! hh using 1 <;> dsimp only [phi, phi'] <;> ring
  have hnonpos : phi' ≤ 0 := by
    intro t
    let R := gradient f (z + t • s) - gradient f z - H (t • s)
    have hR := RobustAHPE.gradient_taylor_remainder f hC2 M hM hH z (t • s)
    change ‖R‖ ≤ M / 2 * ‖t • s‖ ^ 2 at hR
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs] at hR
    have hinner := real_inner_le_norm R s
    have hm := mul_le_mul_of_nonneg_right hR (norm_nonneg s)
    have he : inner ℝ R s = inner ℝ (gradient f (z + t • s)) s -
        inner ℝ (gradient f z) s - t * inner ℝ (H s) s := by
      simp only [R, inner_sub_left, map_smul, real_inner_smul_left]
    rw [he] at hinner
    change inner ℝ (gradient f (z + t • s)) s - inner ℝ (gradient f z) s -
      t * inner ℝ (H s) s - (M / 2 * ‖s‖ ^ 3) * t ^ 2 ≤ 0
    nlinarith only [hinner, hm]
  have hanti := antitone_of_hasDerivAt_nonpos hderiv hnonpos
  have hh := hanti (by norm_num : (0 : ℝ) ≤ 1)
  dsimp only [phi] at hh
  simp only [zero_smul, add_zero, one_smul, zero_mul, one_mul, zero_pow (by norm_num : 2 ≠ 0),
    zero_pow (by norm_num : 3 ≠ 0), one_pow, sub_self, sub_zero, zero_div] at hh
  change f (z + s) ≤ _
  nlinarith only [hh]

end OriginalBorelOuterCubic


namespace OriginalBorelOuterCubic
open _root_.OriginalBorelOuterCubic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]

theorem inexact_step_bounds
    (f : E → ℝ) (hC2 : ContDiff ℝ 2 f) (M : ℝ) (hM : 0 < M)
    (hH : ∀ x y : E, ‖fderiv ℝ (gradient f) x - fderiv ℝ (gradient f) y‖ ≤ M * ‖x - y‖)
    (z v : E) (Ht : E →L[ℝ] E) (deltaG deltaH : ℝ)
    (hG : ‖v - gradient f z‖ ≤ deltaG)
    (hHt : ‖Ht - fderiv ℝ (gradient f) z‖ ≤ deltaH) :
    let s := minimizer v Ht (2 * M)
    f (z + s) - f z ≤ -(M / 3) * ‖s‖ ^ 3 + deltaG * ‖s‖ + deltaH / 2 * ‖s‖ ^ 2 ∧
      ‖gradient f (z + s)‖ ≤ (3 * M / 2) * ‖s‖ ^ 2 + deltaH * ‖s‖ + deltaG := by
  dsimp only
  let s := minimizer v Ht (2 * M)
  let H := fderiv ℝ (gradient f) z
  have hm := minimizer_equation_and_decrease v Ht (2 * M) (by positivity)
  change v + CertifiedATS.sympart Ht s + (2 * M / 2 * ‖s‖) • s = 0 ∧
    model v Ht (2 * M) s ≤ -(2 * M / 12) * ‖s‖ ^ 3 at hm
  have htaylor := cubic_taylor_upper f hC2 M hM hH z s
  have hg : ‖gradient f z - v‖ ≤ deltaG := by simpa only [norm_sub_rev] using hG
  have hgnorm := real_inner_le_norm (gradient f z - v) s
  have hgmul := mul_le_mul_of_nonneg_right hg (norm_nonneg s)
  simp only [inner_sub_left] at hgnorm
  have hdiff : ‖H - Ht‖ ≤ deltaH := by simpa only [norm_sub_rev] using hHt
  have hnorm := ((H - Ht).le_opNorm s).trans (mul_le_mul_of_nonneg_right hdiff (norm_nonneg s))
  have hinner := real_inner_le_norm ((H - Ht) s) s
  have hhmul := mul_le_mul_of_nonneg_right hnorm (norm_nonneg s)
  simp only [sub_apply, inner_sub_left] at hinner
  have hmodel := hm.2
  dsimp only [model] at hmodel
  simp only [sub_apply] at hhmul
  change f (z + s) ≤ f z + inner ℝ (gradient f z) s +
    (1 / 2 : ℝ) * inner ℝ (H s) s + M / 6 * ‖s‖ ^ 3 at htaylor
  refine ⟨?_, ?_⟩
  · change f (z + s) - f z ≤ -(M / 3) * ‖s‖ ^ 3 + deltaG * ‖s‖ + deltaH / 2 * ‖s‖ ^ 2
    nlinarith only [htaylor, hmodel, hgnorm, hgmul, hinner, hhmul]
  · change ‖gradient f (z + s)‖ ≤ (3 * M / 2) * ‖s‖ ^ 2 + deltaH * ‖s‖ + deltaG
    have hself := CertifiedATS.gradient_derivative_selfadjoint f hC2 z
    have hsym : ‖H - CertifiedATS.sympart Ht‖ ≤ deltaH := by
      rw [norm_sub_rev]
      exact (CertifiedATS.sympart_error_bound Ht H hself).trans hHt
    have hsymnorm := ((H - CertifiedATS.sympart Ht).le_opNorm s).trans
      (mul_le_mul_of_nonneg_right hsym (norm_nonneg s))
    let R := gradient f (z + s) - gradient f z - H s
    have hR := RobustAHPE.gradient_taylor_remainder f hC2 M hM hH z s
    change ‖R‖ ≤ M / 2 * ‖s‖ ^ 2 at hR
    have hzero : v + CertifiedATS.sympart Ht s + (M * ‖s‖) • s = 0 := by
      convert! hm.1 using 1 <;> ring
    have he : gradient f (z + s) = R + (gradient f z - v) + (H - CertifiedATS.sympart Ht) s - (M * ‖s‖) • s := by
      calc
        _ = gradient f (z + s) - (v + CertifiedATS.sympart Ht s + (M * ‖s‖) • s) := by rw [hzero, sub_zero]
        _ = _ := by simp only [R, sub_apply]; module
    have hn1 := norm_sub_le (R + (gradient f z - v) + (H - CertifiedATS.sympart Ht) s) ((M * ‖s‖) • s)
    have hn2 := norm_add_le (R + (gradient f z - v)) ((H - CertifiedATS.sympart Ht) s)
    have hn3 := norm_add_le R (gradient f z - v)
    have hsmul : ‖(M * ‖s‖) • s‖ = M * ‖s‖ ^ 2 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hM.le (norm_nonneg _))]
      ring
    rw [← he, hsmul] at hn1
    nlinarith only [hn1, hn2, hn3, hR, hg, hsymnorm]

theorem nonterminal_scalar_decrease (M eps r q Gnew Fchange : ℝ)
    (hM : 0 < M) (heps : 0 < eps) (hr : 0 ≤ r) (hq : 0 ≤ q) (hqsq : q ^ 2 = M * eps)
    (hnew : eps / 3 < Gnew)
    (hgrad : Gnew ≤ (3 * M / 2) * r ^ 2 + (q / 1024) * r + eps / 1024)
    (hchange : Fchange ≤ -(M / 3) * r ^ 3 + (eps / 1024) * r + (q / 1024) / 2 * r ^ 2) :
    eps / 16 ≤ M * r ^ 2 ∧ Fchange ≤ -(M / 4) * r ^ 3 := by
  have hyoung : 2 * r * q ≤ M * r ^ 2 + eps := by
    apply (mul_le_mul_iff_right₀ hM).mp
    nlinarith only [sq_nonneg (M * r - q), hqsq]
  have hradius : eps / 16 ≤ M * r ^ 2 := by
    nlinarith only [hgrad, hyoung, hnew, heps]
  have hMmul := mul_le_mul_of_nonneg_left hradius hM.le
  have hqr : q ≤ 4 * M * r := by
    nlinarith only [hMmul, hqsq, hq, mul_nonneg hM.le hr]
  have hepsr := mul_le_mul_of_nonneg_right hradius hr
  have hqrr := mul_le_mul_of_nonneg_right hqr (sq_nonneg r)
  refine ⟨hradius, ?_⟩
  nlinarith only [hchange, hepsr, hqrr, mul_nonneg hM.le (pow_nonneg hr 3)]

end OriginalBorelOuterCubic


open OriginalBorelOuterCubic



namespace OriginalBorelOuterCubicSeparateErrors
open _root_.OriginalBorelOuterCubicSeparateErrors

open OriginalBetaATSTrial (Answer GetterProgram execute)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]

noncomputable section

def tolerance (M eps : ℝ) : ℝ := min (eps / 1024) (Real.sqrt (M * eps) / 1024)
def stepRadius (M eps : ℝ) : ℝ := Real.sqrt (eps / (16 * M))
def stepCharge (M eps : ℝ) : ℝ := M / 4 * stepRadius M eps ^ 3

structure CubicOutput (E : Type*) where
  point : E
  success : Bool
  moves : ℕ
  charged : ℕ
  cubicSteps : ℝ

def appendCharged (s : E) (out : CubicOutput E) : CubicOutput E :=
  ⟨out.point, out.success, out.moves + 1, out.charged + 1, ‖s‖ ^ 3 + out.cubicSteps⟩

def loop (M eps : ℝ) : ℕ → E → Answer E → GetterProgram (E × ℝ) (Answer E) (CubicOutput E)
  | 0, x, _ => .pure ⟨x, false, 0, 0, 0⟩
  | n + 1, x, a =>
      if ‖a.grad‖ ≤ eps / 2 then .pure ⟨x, true, 0, 0, 0⟩
      else
        let s := OriginalBorelOuterCubic.minimizer a.grad a.hess (2 * M)
        let y := x + s
        .ask (y, tolerance M eps) (fun ay =>
          if ‖ay.grad‖ ≤ eps / 2 then .pure ⟨y, true, 1, 0, ‖s‖ ^ 3⟩
          else FangqingGetterComposition.map (appendCharged s) (loop M eps n y ay))

def program (M eps : ℝ) (n : ℕ) (start : E) : GetterProgram (E × ℝ) (Answer E) (CubicOutput E) :=
  .ask (start, tolerance M eps) (fun a => loop M eps n start a)

theorem radius_properties (M eps : ℝ) (hM : 0 < M) (heps : 0 < eps) :
    0 < tolerance M eps ∧ 0 < stepRadius M eps ∧
      M * stepRadius M eps ^ 2 = eps / 16 ∧ 0 < stepCharge M eps := by
  have ht : 0 < tolerance M eps := by unfold tolerance; positivity
  have hr : 0 < stepRadius M eps := by unfold stepRadius; positivity
  have hs := Real.sq_sqrt (by positivity : 0 ≤ eps / (16 * M))
  have hid : M * stepRadius M eps ^ 2 = eps / 16 := by
    unfold stepRadius
    rw [hs]
    field_simp
  exact ⟨ht, hr, hid, by unfold stepCharge; positivity⟩

def Accurate (f : E → ℝ) (M eps : ℝ) (x : E) (a : Answer E) : Prop :=
  ‖a.grad - gradient f x‖ ≤ eps / 1024 ∧
    ‖a.hess - fderiv ℝ (gradient f) x‖ ≤ Real.sqrt (M * eps) / 1024

theorem accurate_stop (f : E → ℝ) (M eps : ℝ) (heps : 0 < eps) (x : E) (a : Answer E)
    (ha : Accurate f M eps x a) (hstop : ‖a.grad‖ ≤ eps / 2) : ‖gradient f x‖ ≤ eps := by
  have he : ‖a.grad - gradient f x‖ ≤ eps / 1024 := ha.1
  have ht := norm_sub_le a.grad (a.grad - gradient f x)
  have hid : a.grad - (a.grad - gradient f x) = gradient f x := by abel
  rw [hid] at ht
  linarith only [ht, he, hstop, heps]

theorem accurate_nonterminal (f : E → ℝ) (M eps : ℝ) (heps : 0 < eps) (x : E) (a : Answer E)
    (ha : Accurate f M eps x a) (hstop : ¬ ‖a.grad‖ ≤ eps / 2) : eps / 3 < ‖gradient f x‖ := by
  have he : ‖a.grad - gradient f x‖ ≤ eps / 1024 := ha.1
  have ht := norm_add_le (a.grad - gradient f x) (gradient f x)
  have hid : (a.grad - gradient f x) + gradient f x = a.grad := by abel
  rw [hid] at ht
  linarith only [ht, he, lt_of_not_ge hstop, heps]

theorem large_radius_scalar_decrease (M eps r q Fchange : ℝ)
    (hM : 0 < M) (hr : 0 ≤ r) (hqsq : q ^ 2 = M * eps)
    (hradius : eps / 16 ≤ M * r ^ 2)
    (hchange : Fchange ≤ -(M / 3) * r ^ 3 + (eps / 1024) * r + (q / 1024) / 2 * r ^ 2) :
    Fchange ≤ -(M / 4) * r ^ 3 := by
  have hMmul := mul_le_mul_of_nonneg_left hradius hM.le
  have hqr : q ≤ 4 * M * r := by
    nlinarith only [hMmul, hqsq, mul_nonneg hM.le hr]
  have hepsr := mul_le_mul_of_nonneg_right hradius hr
  have hqrr := mul_le_mul_of_nonneg_right hqr (sq_nonneg r)
  nlinarith only [hchange, hepsr, hqrr, mul_nonneg hM.le (pow_nonneg hr 3)]

theorem actual_step_radius_and_descent
    (f : E → ℝ) (hC2 : ContDiff ℝ 2 f) (M eps : ℝ) (hM : 0 < M) (heps : 0 < eps)
    (hH : ∀ x y : E, ‖fderiv ℝ (gradient f) x - fderiv ℝ (gradient f) y‖ ≤ M * ‖x - y‖)
    (x : E) (a : Answer E) (ha : Accurate f M eps x a) :
    let s := OriginalBorelOuterCubic.minimizer a.grad a.hess (2 * M)
    (stepRadius M eps ≤ ‖s‖ → M / 4 * ‖s‖ ^ 3 ≤ f x - f (x + s)) ∧
    (∀ ay : Answer E, Accurate f M eps (x + s) ay → ¬ ‖ay.grad‖ ≤ eps / 2 →
      stepRadius M eps ≤ ‖s‖ ∧ M / 4 * ‖s‖ ^ 3 ≤ f x - f (x + s)) := by
  dsimp only
  let s := OriginalBorelOuterCubic.minimizer a.grad a.hess (2 * M)
  have hp := radius_properties M eps hM heps
  have hs := OriginalBorelOuterCubic.inexact_step_bounds f hC2 M hM hH x a.grad a.hess (eps / 1024) (Real.sqrt (M * eps) / 1024)
    (ha.1) ha.2
  have hqsq := Real.sq_sqrt (by positivity : 0 ≤ M * eps)
  have hq : 0 ≤ Real.sqrt (M * eps) := Real.sqrt_nonneg _
  refine ⟨?_, ?_⟩
  · intro hr
    have hsq := (sq_le_sq₀ hp.2.1.le (norm_nonneg s)).mpr hr
    have hm := mul_le_mul_of_nonneg_left hsq hM.le
    have hradius : eps / 16 ≤ M * ‖s‖ ^ 2 := by linarith only [hm, hp.2.2.1]
    have hd := large_radius_scalar_decrease M eps ‖s‖ (Real.sqrt (M * eps)) (f (x + s) - f x)
      hM (norm_nonneg _) hqsq hradius hs.1
    linarith only [hd]
  · intro ay hay haway
    have hlarge := accurate_nonterminal f M eps heps (x + s) ay hay haway
    have hscalar := OriginalBorelOuterCubic.nonterminal_scalar_decrease M eps ‖s‖ (Real.sqrt (M * eps))
      ‖gradient f (x + s)‖ (f (x + s) - f x) hM heps (norm_nonneg _) hq hqsq hlarge hs.2 hs.1
    have hsq : stepRadius M eps ^ 2 ≤ ‖s‖ ^ 2 := by
      apply (mul_le_mul_iff_right₀ hM).mp
      linarith only [hp.2.2.1, hscalar.1]
    exact ⟨(sq_le_sq₀ hp.2.1.le (norm_nonneg s)).mp hsq, by linarith only [hscalar.2]⟩

end
end OriginalBorelOuterCubicSeparateErrors




namespace OriginalBorelOuterCubicSeparateErrors
open _root_.OriginalBorelOuterCubicSeparateErrors

open OriginalBetaATSTrial (Answer GetterProgram execute)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]

def LoopSpec (f : E → ℝ) (M eps lower : ℝ) (n : ℕ) (x : E) (run : CubicOutput E × ℕ) : Prop :=
  stepCharge M eps * (run.1.charged : ℝ) ≤ f x - lower ∧
  M / 4 * run.1.cubicSteps ≤ f x - lower + stepCharge M eps ∧
  run.1.moves ≤ run.1.charged + 1 ∧
  (run.1.success = true → ‖gradient f run.1.point‖ ≤ eps) ∧
  (run.1.success = false → run.1.charged = n) ∧ run.2 = run.1.moves

theorem actual_cubic_loop_spec
    (f : E → ℝ) (hC2 : ContDiff ℝ 2 f) (M eps lower : ℝ) (hM : 0 < M) (heps : 0 < eps)
    (hH : ∀ x y : E, ‖fderiv ℝ (gradient f) x - fderiv ℝ (gradient f) y‖ ≤ M * ‖x - y‖)
    (hbelow : ∀ x : E, lower ≤ f x)
    (getter : E × ℝ → Answer E)
    (hvalid : ∀ x, Accurate f M eps x (getter (x, tolerance M eps)))
    (n : ℕ) (x : E) (a : Answer E) (ha : Accurate f M eps x a) :
    LoopSpec f M eps lower n x (execute getter (loop M eps n x a)) := by
  have hp := radius_properties M eps hM heps
  have hradius0 := hp.2.1.le
  induction n generalizing x a with
  | zero =>
      simp only [loop, execute, LoopSpec]
      refine ⟨by simpa only [Nat.cast_zero, mul_zero] using sub_nonneg.mpr (hbelow x),
        by simpa only [mul_zero] using add_nonneg (sub_nonneg.mpr (hbelow x)) hp.2.2.2.le,
        by omega, ?_, fun _ => by trivial, by trivial⟩
      intro hf
      cases hf
  | succ n ih =>
      by_cases hstop : ‖a.grad‖ ≤ eps / 2
      · rw [loop, if_pos hstop]
        simp only [execute, LoopSpec]
        refine ⟨by simpa only [Nat.cast_zero, mul_zero] using sub_nonneg.mpr (hbelow x),
          by simpa only [mul_zero] using add_nonneg (sub_nonneg.mpr (hbelow x)) hp.2.2.2.le,
          by omega, fun _ => accurate_stop f M eps heps x a ha hstop, ?_, by trivial⟩
        intro hf
        cases hf
      · let s := OriginalBorelOuterCubic.minimizer a.grad a.hess (2 * M)
        let y := x + s
        let ay := getter (y, tolerance M eps)
        have hay : Accurate f M eps y ay := hvalid y
        have hstep := actual_step_radius_and_descent f hC2 M eps hM heps hH x a ha
        change (stepRadius M eps ≤ ‖s‖ → M / 4 * ‖s‖ ^ 3 ≤ f x - f y) ∧
          (∀ ay : Answer E, Accurate f M eps y ay → ¬ ‖ay.grad‖ ≤ eps / 2 →
            stepRadius M eps ≤ ‖s‖ ∧ M / 4 * ‖s‖ ^ 3 ≤ f x - f y) at hstep
        rw [loop, if_neg hstop]
        change LoopSpec f M eps lower (n + 1) x
          (execute getter (.ask (y, tolerance M eps) (fun ay =>
            if ‖ay.grad‖ ≤ eps / 2 then .pure ⟨y, true, 1, 0, ‖s‖ ^ 3⟩
            else FangqingGetterComposition.map (appendCharged s) (loop M eps n y ay))))
        simp only [execute]
        change LoopSpec f M eps lower (n + 1) x
          ((execute getter (if ‖ay.grad‖ ≤ eps / 2 then .pure ⟨y, true, 1, 0, ‖s‖ ^ 3⟩
            else FangqingGetterComposition.map (appendCharged s) (loop M eps n y ay))).1,
           (execute getter (if ‖ay.grad‖ ≤ eps / 2 then .pure ⟨y, true, 1, 0, ‖s‖ ^ 3⟩
            else FangqingGetterComposition.map (appendCharged s) (loop M eps n y ay))).2 + 1)
        by_cases hnextstop : ‖ay.grad‖ ≤ eps / 2
        · have hbudget : M / 4 * ‖s‖ ^ 3 ≤ f x - lower + stepCharge M eps := by
            by_cases hr : stepRadius M eps ≤ ‖s‖
            · have hd := hstep.1 hr
              linarith only [hd, hbelow y, hp.2.2.2]
            · have hrle : ‖s‖ ≤ stepRadius M eps := (lt_of_not_ge hr).le
              have hcube : ‖s‖ ^ 3 ≤ stepRadius M eps ^ 3 := by gcongr
              have hh := mul_le_mul_of_nonneg_left hcube (by positivity : 0 ≤ M / 4)
              change M / 4 * ‖s‖ ^ 3 ≤ f x - lower + M / 4 * stepRadius M eps ^ 3
              linarith only [hh, hbelow x]
          simp only [if_pos hnextstop, execute, LoopSpec]
          refine ⟨by simpa only [Nat.cast_zero, mul_zero] using sub_nonneg.mpr (hbelow x),
            hbudget, by omega, fun _ => accurate_stop f M eps heps y ay hay hnextstop, ?_, by trivial⟩
          intro hf
          cases hf
        · have hd := hstep.2 ay hay hnextstop
          have hradius := hd.1
          have hcube : stepRadius M eps ^ 3 ≤ ‖s‖ ^ 3 := by gcongr
          have hcharge : stepCharge M eps ≤ M / 4 * ‖s‖ ^ 3 :=
            mul_le_mul_of_nonneg_left hcube (by positivity)
          have hi := ih y ay hay
          simp only [LoopSpec] at hi
          simp only [if_neg hnextstop, FangqingGetterComposition.execute_map,
            LoopSpec, appendCharged, Nat.cast_add, Nat.cast_one]
          refine ⟨by nlinarith only [hi.1, hd.2, hcharge],
            by nlinarith only [hi.2.1, hd.2], ?_, hi.2.2.2.1, ?_, ?_⟩
          · have hh := hi.2.2.1
            omega
          · intro hf
            have hh := hi.2.2.2.2.1 hf
            omega
          · have hh := hi.2.2.2.2.2
            omega

noncomputable def fuel (Delta M eps : ℝ) : ℕ := Nat.ceil (Delta / stepCharge M eps) + 1

theorem actual_finite_cubic_termination
    (f : E → ℝ) (hC2 : ContDiff ℝ 2 f) (M eps lower Delta : ℝ) (hM : 0 < M) (heps : 0 < eps)
    (hH : ∀ x y : E, ‖fderiv ℝ (gradient f) x - fderiv ℝ (gradient f) y‖ ≤ M * ‖x - y‖)
    (hbelow : ∀ x : E, lower ≤ f x)
    (getter : E × ℝ → Answer E)
    (hvalid : ∀ x, Accurate f M eps x (getter (x, tolerance M eps)))
    (start : E) (hgap : f start - lower ≤ Delta) :
    let run := execute getter (program M eps (fuel Delta M eps) start)
    run.1.success = true ∧ ‖gradient f run.1.point‖ ≤ eps ∧
      (run.1.moves : ℝ) ≤ 1 + Delta / stepCharge M eps ∧
      run.1.cubicSteps ≤ 4 * Delta / M + stepRadius M eps ^ 3 ∧
      (run.2 : ℝ) ≤ 2 + Delta / stepCharge M eps := by
  dsimp only
  let a := getter (start, tolerance M eps)
  let rest := execute getter (loop M eps (fuel Delta M eps) start a)
  have hp := radius_properties M eps hM heps
  have hs := actual_cubic_loop_spec f hC2 M eps lower hM heps hH hbelow getter hvalid
    (fuel Delta M eps) start a (hvalid start)
  change LoopSpec f M eps lower (fuel Delta M eps) start rest at hs
  dsimp only [LoopSpec] at hs
  have hc : (rest.1.charged : ℝ) ≤ Delta / stepCharge M eps :=
    (le_div_iff₀ hp.2.2.2).mpr (by nlinarith only [hs.1, hgap])
  have hsuccess : rest.1.success = true := by
    cases hb : rest.1.success with
    | true => rfl
    | false =>
        have hn := hs.2.2.2.2.1 hb
        rw [hn] at hc
        have hceil : Delta / stepCharge M eps ≤ (Nat.ceil (Delta / stepCharge M eps) : ℝ) := Nat.le_ceil _
        unfold fuel at hc
        push_cast at hc
        linarith only [hc, hceil]
  have hmoves : (rest.1.moves : ℝ) ≤ 1 + Delta / stepCharge M eps := by
    have hh : (rest.1.moves : ℝ) ≤ (rest.1.charged : ℝ) + 1 := by exact_mod_cast hs.2.2.1
    linarith only [hh, hc]
  have hcubic : rest.1.cubicSteps ≤ 4 * Delta / M + stepRadius M eps ^ 3 := by
    apply (mul_le_mul_iff_right₀ (by positivity : 0 < M / 4)).mp
    have hid : M / 4 * (4 * Delta / M + stepRadius M eps ^ 3) = Delta + stepCharge M eps := by
      unfold stepCharge
      field_simp <;> ring
    rw [hid]
    nlinarith only [hs.2.1, hgap]
  change rest.1.success = true ∧ ‖gradient f rest.1.point‖ ≤ eps ∧
    (rest.1.moves : ℝ) ≤ 1 + Delta / stepCharge M eps ∧
    rest.1.cubicSteps ≤ 4 * Delta / M + stepRadius M eps ^ 3 ∧ ((rest.2 + 1 : ℕ) : ℝ) ≤ _
  refine ⟨hsuccess, hs.2.2.2.1 hsuccess, hmoves, hcubic, ?_⟩
  rw [hs.2.2.2.2.2]
  push_cast
  linarith only [hmoves]

end OriginalBorelOuterCubicSeparateErrors




namespace OriginalBorelOuterCubicSeparateErrors
open _root_.OriginalBorelOuterCubicSeparateErrors

theorem radius_and_charge_identities (M eps : ℝ) (hM : 0 < M) (heps : 0 < eps) :
    stepRadius M eps ^ 3 = eps ^ (3 / 2 : ℝ) / (64 * M * Real.sqrt M) ∧
      stepCharge M eps = eps ^ (3 / 2 : ℝ) / (256 * Real.sqrt M) := by
  have hr : stepRadius M eps = Real.sqrt eps / (4 * Real.sqrt M) := by
    unfold stepRadius
    rw [Real.sqrt_div heps.le, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 16)]
    norm_num
  have he3 : Real.sqrt eps ^ 3 = eps * Real.sqrt eps := by rw [pow_succ, Real.sq_sqrt heps.le]
  have hM3 : Real.sqrt M ^ 3 = M * Real.sqrt M := by rw [pow_succ, Real.sq_sqrt hM.le]
  have hepow : eps ^ (3 / 2 : ℝ) = eps * Real.sqrt eps := by
    calc
      _ = eps ^ (1 + 1 / 2 : ℝ) := by congr 1 <;> ring
      _ = _ := by rw [Real.rpow_add heps, Real.rpow_one, ← Real.sqrt_eq_rpow]
  have hcube : stepRadius M eps ^ 3 = eps ^ (3 / 2 : ℝ) / (64 * M * Real.sqrt M) := by
    rw [hr, div_pow, mul_pow, he3, hM3, hepow]
    norm_num
    ring
  refine ⟨hcube, ?_⟩
  unfold stepCharge
  rw [hcube]
  field_simp [ne_of_gt hM, ne_of_gt (Real.sqrt_pos.mpr hM)]
  <;> ring

theorem reciprocal_charge_identity (Delta M eps : ℝ) (hM : 0 < M) (heps : 0 < eps) :
    Delta / stepCharge M eps = 256 * Delta * Real.sqrt M / eps ^ (3 / 2 : ℝ) := by
  rw [(radius_and_charge_identities M eps hM heps).2, div_div_eq_mul_div]
  ring

noncomputable def epsilonThreshold (Delta M : ℝ) : ℝ := (Delta * Real.sqrt M) ^ (2 / 3 : ℝ)

theorem epsilon_threshold_properties (Delta M eps : ℝ) (hDelta : 0 < Delta) (hM : 0 < M)
    (heps : 0 < eps) (hsmall : eps ≤ epsilonThreshold Delta M) :
    0 < epsilonThreshold Delta M ∧ eps ^ (3 / 2 : ℝ) ≤ Delta * Real.sqrt M := by
  have hx : 0 < Delta * Real.sqrt M := by positivity
  have hpos : 0 < epsilonThreshold Delta M := by unfold epsilonThreshold; positivity
  have hp := Real.rpow_le_rpow heps.le hsmall (by norm_num : (0 : ℝ) ≤ 3 / 2)
  change eps ^ (3 / 2 : ℝ) ≤ ((Delta * Real.sqrt M) ^ (2 / 3 : ℝ)) ^ (3 / 2 : ℝ) at hp
  rw [← Real.rpow_mul hx.le] at hp
  norm_num only [show (2 / 3 : ℝ) * (3 / 2) = 1 by norm_num, Real.rpow_one] at hp
  exact ⟨hpos, hp⟩

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]

open OriginalBetaATSTrial (Answer execute)

theorem cubic_asymptotic_rate_and_full_step_budget
    (f : E → ℝ) (hC2 : ContDiff ℝ 2 f) (M eps lower Delta : ℝ) (hM : 0 < M) (heps : 0 < eps)
    (hH : ∀ x y : E, ‖fderiv ℝ (gradient f) x - fderiv ℝ (gradient f) y‖ ≤ M * ‖x - y‖)
    (hbelow : ∀ x : E, lower ≤ f x)
    (getter : E × ℝ → Answer E)
    (hvalid : ∀ x, Accurate f M eps x (getter (x, tolerance M eps)))
    (start : E) (hgap : f start - lower ≤ Delta)
    (hsmall : eps ^ (3 / 2 : ℝ) ≤ Delta * Real.sqrt M) :
    let run := execute getter (program M eps (fuel Delta M eps) start)
    ‖gradient f run.1.point‖ ≤ eps ∧
      (run.1.moves : ℝ) ≤ 512 * Delta * Real.sqrt M / eps ^ (3 / 2 : ℝ) ∧
      run.1.cubicSteps ≤ 5 * Delta / M ∧
      (run.2 : ℝ) ≤ 512 * Delta * Real.sqrt M / eps ^ (3 / 2 : ℝ) := by
  dsimp only
  have hDelta : 0 ≤ Delta := by linarith only [hgap, hbelow start]
  have hpow : 0 < eps ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos heps _
  have hs := actual_finite_cubic_termination f hC2 M eps lower Delta hM heps hH hbelow getter hvalid start hgap
  have hrate : 1 ≤ Delta * Real.sqrt M / eps ^ (3 / 2 : ℝ) :=
    (le_div_iff₀ hpow).mpr (by simpa only [one_mul] using hsmall)
  let t := Delta * Real.sqrt M / eps ^ (3 / 2 : ℝ)
  change 1 ≤ t at hrate
  rw [reciprocal_charge_identity Delta M eps hM heps] at hs
  have hcube : stepRadius M eps ^ 3 ≤ Delta / (64 * M) := by
    rw [(radius_and_charge_identities M eps hM heps).1]
    calc
      _ ≤ (Delta * Real.sqrt M) / (64 * M * Real.sqrt M) :=
        div_le_div_of_nonneg_right hsmall (by positivity)
      _ = _ := by field_simp [ne_of_gt (Real.sqrt_pos.mpr hM)]
  refine ⟨hs.2.1, ?_, ?_, ?_⟩
  · have hh := hs.2.2.1
    rw [show 256 * Delta * Real.sqrt M / eps ^ (3 / 2 : ℝ) = 256 * t by dsimp [t]; ring] at hh
    rw [show 512 * Delta * Real.sqrt M / eps ^ (3 / 2 : ℝ) = 512 * t by dsimp [t]; ring]
    nlinarith only [hh, hrate]
  · have hh := hs.2.2.2.1
    have hn : 0 ≤ Delta / M := by positivity
    rw [show 4 * Delta / M = 4 * (Delta / M) by ring] at hh
    rw [show Delta / (64 * M) = (Delta / M) / 64 by ring] at hcube
    rw [show 5 * Delta / M = 5 * (Delta / M) by ring]
    nlinarith only [hh, hcube, hn]
  · have hh := hs.2.2.2.2
    rw [show 256 * Delta * Real.sqrt M / eps ^ (3 / 2 : ℝ) = 256 * t by dsimp [t]; ring] at hh
    rw [show 512 * Delta * Real.sqrt M / eps ^ (3 / 2 : ℝ) = 512 * t by dsimp [t]; ring]
    nlinarith only [hh, hrate]

end OriginalBorelOuterCubicSeparateErrors


namespace OriginalBorelStatefulEnvelopeCubic
open _root_.OriginalBorelStatefulEnvelopeCubic

open OriginalBorelOuterCubic OriginalBorelOuterCubicSeparateErrors

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]

noncomputable section
set_option maxHeartbeats 3000000

/-- Every actual cubic step increases the value by at most one explicit terminal
charge. Large steps decrease it. This controls the genuine terminal query's envelope
gap without invoking the refuted unconditional all-step cube budget. -/
theorem actual_step_value_upper
    (f : E → ℝ) (hC2 : ContDiff ℝ 2 f) (M eps : ℝ) (hM : 0 < M) (heps : 0 < eps)
    (hH : ∀ x y : E, ‖fderiv ℝ (gradient f) x - fderiv ℝ (gradient f) y‖ ≤ M * ‖x - y‖)
    (x : E) (a : OriginalBetaATSTrial.Answer E) (ha : Accurate f M eps x a) :
    let s := OriginalBorelOuterCubic.minimizer a.grad a.hess (2 * M)
    f (x + s) ≤ f x + stepCharge M eps := by
  let s := OriginalBorelOuterCubic.minimizer a.grad a.hess (2 * M)
  let R := stepRadius M eps
  have hp := radius_properties M eps hM heps
  have hcharge : 0 ≤ stepCharge M eps := hp.2.2.2.le
  by_cases hlarge : R ≤ ‖s‖
  · have hd := (actual_step_radius_and_descent f hC2 M eps hM heps hH x a ha).1 hlarge
    have hnon : 0 ≤ M / 4 * ‖s‖ ^ 3 := by positivity
    change f (x + s) ≤ f x + _
    linarith only [hd, hnon, hcharge]
  · have hr : ‖s‖ ≤ R := (lt_of_not_ge hlarge).le
    have hR : 0 < R := hp.2.1
    have hRsq : M * R ^ 2 = eps / 16 := hp.2.2.1
    have hq0 := Real.sqrt_nonneg (M * eps)
    have hqsq := Real.sq_sqrt (show 0 ≤ M * eps by positivity)
    have hQ : Real.sqrt (M * eps) = 4 * M * R := by
      have hh := congrArg (fun t : ℝ => 16 * M * t) hRsq
      have hh' : (4 * M * R) ^ 2 = M * eps := by nlinarith only [hh]
      have hMR : 0 < 4 * M * R := by positivity
      nlinarith only [hh', hqsq, hq0, hMR]
    have hEps : eps = 16 * M * R ^ 2 := by linarith only [hRsq]
    have herr : eps / 1024 * R + (Real.sqrt (M * eps) / 1024) / 2 * R ^ 2 ≤ stepCharge M eps := by
      have heq : eps / 1024 * R + (Real.sqrt (M * eps) / 1024) / 2 * R ^ 2 =
          (9 / 512 : ℝ) * M * R ^ 3 := by rw [hQ, hEps]; ring
      rw [heq]
      change (9 / 512 : ℝ) * M * R ^ 3 ≤ M / 4 * R ^ 3
      have hn : 0 ≤ M * R ^ 3 := by positivity
      nlinarith only [hn]
    have hs := (OriginalBorelOuterCubic.inexact_step_bounds f hC2 M hM hH x a.grad a.hess (eps / 1024)
      (Real.sqrt (M * eps) / 1024) ha.1 ha.2).1
    have hlin := mul_le_mul_of_nonneg_left hr (show 0 ≤ eps / 1024 by positivity)
    have hsq := pow_le_pow_left₀ (norm_nonneg s) hr 2
    have hquad := mul_le_mul_of_nonneg_left hsq
      (show 0 ≤ (Real.sqrt (M * eps) / 1024) / 2 by positivity)
    have hcube : 0 ≤ M * ‖s‖ ^ 3 := by positivity
    change f (x + s) ≤ f x + _
    change f (x + s) - f x ≤ -(M / 3) * ‖s‖ ^ 3 + eps / 1024 * ‖s‖ +
      (Real.sqrt (M * eps) / 1024) / 2 * ‖s‖ ^ 2 at hs
    nlinarith only [hs, hlin, hquad, herr, hcube]

end
end OriginalBorelStatefulEnvelopeCubic


namespace OriginalBorelStatefulEnvelopeCubic
open _root_.OriginalBorelStatefulEnvelopeCubic

open OriginalSaddleImplicit OriginalSaddleTransfer OriginalSaddleStability
open OriginalBetaATSTrial FangqingGetterComposition
open OriginalEnvelopeOracleProgram
open OriginalBorelOuterCubic OriginalBorelOuterCubicSeparateErrors

noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 5000

universe u
variable {E F : Type u}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

def estimateProgram (mu L rho D tau : ℝ) (x : E) (yin : F) :
    GetterProgram (Joint E F) (OriginalDualOracleProgram.OracleAnswer (Joint E F)) (Estimate E F) :=
  OriginalEnvelopeOracleProgram.program L x (OriginalMinimumWarmSolver.program mu L rho D tau x x yin)

def asAnswer (a : Estimate E F) : Answer E := ⟨a.grad, a.hess⟩

theorem actual_estimate
    (J : Joint E F → ℝ) (mu L rho D tau : ℝ)
    (hmu : 0 < mu) (hLmu : mu ≤ L) (hrho : 0 ≤ rho) (htau : 0 < tau)
    (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (hHess : ∀ z w : Joint E F, ‖fderiv ℝ (gradient J) z - fderiv ℝ (gradient J) w‖ ≤ rho * ‖z - w‖)
    (hsc : ∀ u : E, StrongConvexOn (Set.univ : Set F) mu (fun y => -JointSliceRegularity.curry J u y))
    (x : E) (yin : F) (hwarm : ‖yin - vStar (JointSliceRegularity.curry J) L x‖ ≤ D) :
    let run := execute (OriginalDualOracleProgram.actualOracle J) (estimateProgram mu L rho D tau x yin)
    ‖run.1.saddle - zStar (JointSliceRegularity.curry J) L x‖ ≤ tau ∧
    ‖run.1.grad - gradient (saddleEnvelope (JointSliceRegularity.curry J) L) x‖ ≤ 2 * L * tau ∧
    ‖run.1.hess - fderiv ℝ (gradient (saddleEnvelope (JointSliceRegularity.curry J) L)) x‖ ≤
      4 * rho * (1 + L / mu) ^ 2 * tau ∧
    (run.2 : ℝ) ≤ (1 + min (Real.sqrt (L / mu)) ((rho * D / mu) ^ (2 / 7 : ℝ))) *
      OriginalMinimumWarmSolver.logFactor J mu L rho D tau x x yin + 1 := by
  let p := OriginalMinimumWarmSolver.program mu L rho D tau x x yin
  let w := (execute (OriginalDualOracleProgram.actualOracle J) p).1
  have hw := OriginalMinimumWarmSolver.actual_minimum_warm_solver J mu L rho D tau
    hmu hLmu hrho htau hC2 hLip hHess hsc x x yin hwarm
  have he := OriginalEnvelopeOracle.envelope_oracle_from_joint_negative_slice J L mu rho
    (hmu.trans_le hLmu) hmu hrho hC2 hsc hLip hHess x w tau hw.1
  unfold estimateProgram
  rw [OriginalEnvelopeOracleProgram.actual_execution]
  refine ⟨hw.1, he.1, he.2, ?_⟩
  simp only [Nat.cast_add, Nat.cast_one]
  exact add_le_add hw.2 (le_refl (1 : ℝ))

structure Result (E F : Type*) where
  point : E
  saddle : Joint E F
  success : Bool
  charged : ℕ
  moves : List (OriginalStatefulEnvelopeGD.Move E F)

def cubedMovement (moves : List (OriginalStatefulEnvelopeGD.Move E F)) : ℝ :=
  (moves.map (fun m => ‖m.next - m.previous‖ ^ 3)).sum

def appendCharged (m : OriginalStatefulEnvelopeGD.Move E F) (out : Result E F) : Result E F :=
  { out with charged := out.charged + 1, moves := m :: out.moves }

/-- Actual cubic execution with a previous returned saddle kept as inner warm state. -/
def loop (mu L rho tau M eps : ℝ) : ℕ → E → Estimate E F →
    GetterProgram (Joint E F) (OriginalDualOracleProgram.OracleAnswer (Joint E F)) (Result E F)
  | 0, x, a => .pure ⟨x, a.saddle, false, 0, []⟩
  | n + 1, x, a =>
      if ‖a.grad‖ ≤ eps / 2 then .pure ⟨x, a.saddle, true, 0, []⟩
      else
        let s := OriginalBorelOuterCubic.minimizer a.grad a.hess (2 * M)
        let y := x + s
        let D := tau + 2 * Real.sqrt (L / mu) * ‖s‖
        let m : OriginalStatefulEnvelopeGD.Move E F := ⟨x, y, a.saddle.snd, D⟩
        bind (estimateProgram mu L rho D tau y a.saddle.snd) (fun ay =>
          if ‖ay.grad‖ ≤ eps / 2 then .pure ⟨y, ay.saddle, true, 0, [m]⟩
          else map (appendCharged m) (loop mu L rho tau M eps n y ay))

end
end OriginalBorelStatefulEnvelopeCubic


namespace OriginalBorelStatefulEnvelopeCubic
open _root_.OriginalBorelStatefulEnvelopeCubic

open OriginalSaddleImplicit OriginalSaddleTransfer OriginalSaddleStability
open OriginalBetaATSTrial FangqingGetterComposition
open OriginalEnvelopeOracleProgram
open OriginalBorelOuterCubic OriginalBorelOuterCubicSeparateErrors

noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 6000

universe u
variable {E F : Type u}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

structure LoopSpec (J : Joint E F → ℝ) (mu L rho tau M eps lower : ℝ)
    (n : ℕ) (x : E) (run : Result E F × ℕ) : Prop where
  close : ‖run.1.saddle - zStar (JointSliceRegularity.curry J) L run.1.point‖ ≤ tau
  charged_budget : stepCharge M eps * (run.1.charged : ℝ) ≤ saddleEnvelope (JointSliceRegularity.curry J) L x - lower
  cube_budget : M / 4 * cubedMovement run.1.moves ≤ saddleEnvelope (JointSliceRegularity.curry J) L x - lower + stepCharge M eps
  length_bound : run.1.moves.length ≤ run.1.charged + 1
  terminal : run.1.success = true → ‖gradient (saddleEnvelope (JointSliceRegularity.curry J) L) run.1.point‖ ≤ eps
  exhausted : run.1.success = false → run.1.charged = n
  original_cost : (run.2 : ℝ) ≤ OriginalStatefulEnvelopeGD.costSum J mu L rho tau run.1.moves + (run.1.moves.length : ℝ)
  value_upper : saddleEnvelope (JointSliceRegularity.curry J) L run.1.point ≤ saddleEnvelope (JointSliceRegularity.curry J) L x + stepCharge M eps
  legal_moves : ∀ m ∈ run.1.moves,
    ‖m.warm - vStar (JointSliceRegularity.curry J) L m.next‖ ≤ m.radius ∧
    m.radius = tau + 2 * Real.sqrt (L / mu) * ‖m.next - m.previous‖ ∧
    saddleEnvelope (JointSliceRegularity.curry J) L m.previous ≤ saddleEnvelope (JointSliceRegularity.curry J) L x ∧
    saddleEnvelope (JointSliceRegularity.curry J) L m.next ≤ saddleEnvelope (JointSliceRegularity.curry J) L x + stepCharge M eps

theorem actual_loop_spec
    (J : Joint E F → ℝ) (mu L rho tau M eps lower : ℝ)
    (hmu : 0 < mu) (hLmu : mu ≤ L) (hrho : 0 ≤ rho) (htau : 0 < tau) (hM : 0 < M) (heps : 0 < eps)
    (htolG : 2 * L * tau ≤ eps / 1024)
    (htolH : 4 * rho * (1 + L / mu) ^ 2 * tau ≤ Real.sqrt (M * eps) / 1024)
    (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (hHess : ∀ z w : Joint E F, ‖fderiv ℝ (gradient J) z - fderiv ℝ (gradient J) w‖ ≤ rho * ‖z - w‖)
    (hsc : ∀ u : E, StrongConvexOn (Set.univ : Set F) mu (fun y => -JointSliceRegularity.curry J u y))
    (hEHess : ∀ x y : E,
      ‖fderiv ℝ (gradient (saddleEnvelope (JointSliceRegularity.curry J) L)) x -
        fderiv ℝ (gradient (saddleEnvelope (JointSliceRegularity.curry J) L)) y‖ ≤ M * ‖x - y‖)
    (hbelow : ∀ x : E, lower ≤ saddleEnvelope (JointSliceRegularity.curry J) L x)
    (n : ℕ) (x : E) (a : Estimate E F)
    (hclose : ‖a.saddle - zStar (JointSliceRegularity.curry J) L x‖ ≤ tau)
    (ha : Accurate (saddleEnvelope (JointSliceRegularity.curry J) L) M eps x (asAnswer a)) :
    LoopSpec J mu L rho tau M eps lower n x
      (execute (OriginalDualOracleProgram.actualOracle J) (loop mu L rho tau M eps n x a)) := by
  let Ef := saddleEnvelope (JointSliceRegularity.curry J) L
  have hL : 0 < L := hmu.trans_le hLmu
  have hJ := JointSliceRegularity.differentiable_joint_of_contDiff2 J hC2
  have hEC2 : ContDiff ℝ 2 Ef := OriginalEnvelopeRegularity.actual_envelope_contDiff2 J L mu hL hmu hC2 hsc hLip
  have hp := radius_properties M eps hM heps
  have hcharge : 0 < stepCharge M eps := hp.2.2.2
  induction n generalizing x a with
  | zero =>
      rw [loop]
      simp only [execute]
      refine ⟨hclose, ?_, ?_, by norm_num, ?_, fun _ => rfl, ?_, ?_, ?_⟩
      · simp only [Nat.cast_zero, mul_zero]
        change 0 ≤ Ef x - lower
        linarith only [hbelow x]
      · change M / 4 * (0 : ℝ) ≤ Ef x - lower + stepCharge M eps
        linarith only [hbelow x, hcharge]
      · intro hh
        cases hh
      · simp [OriginalStatefulEnvelopeGD.costSum]
      · change Ef x ≤ Ef x + stepCharge M eps
        linarith only [hcharge]
      · intro m hm
        cases hm
  | succ n ih =>
      by_cases hstop : ‖a.grad‖ ≤ eps / 2
      · rw [loop, if_pos hstop]
        simp only [execute]
        refine ⟨hclose, ?_, ?_, by norm_num, ?_, ?_, ?_, ?_, ?_⟩
        · simp only [Nat.cast_zero, mul_zero]
          change 0 ≤ Ef x - lower
          linarith only [hbelow x]
        · change M / 4 * (0 : ℝ) ≤ Ef x - lower + stepCharge M eps
          linarith only [hbelow x, hcharge]
        · intro _
          exact accurate_stop Ef M eps heps x (asAnswer a) ha hstop
        · intro hh
          cases hh
        · simp [OriginalStatefulEnvelopeGD.costSum]
        · change Ef x ≤ Ef x + stepCharge M eps
          linarith only [hcharge]
        · intro m hm
          cases hm
      · let s := OriginalBorelOuterCubic.minimizer a.grad a.hess (2 * M)
        let y := x + s
        let D := tau + 2 * Real.sqrt (L / mu) * ‖s‖
        let m : OriginalStatefulEnvelopeGD.Move E F := ⟨x, y, a.saddle.snd, D⟩
        let first := execute (OriginalDualOracleProgram.actualOracle J) (estimateProgram mu L rho D tau y a.saddle.snd)
        let ay := first.1
        have hs : y - x = s := by dsimp only [y]; abel
        have hprevious : ‖a.saddle.snd - vStar (JointSliceRegularity.curry J) L x‖ ≤ tau :=
          (WithLp.norm_snd_le E (a.saddle - zStar (JointSliceRegularity.curry J) L x)).trans hclose
        have hwarm : ‖a.saddle.snd - vStar (JointSliceRegularity.curry J) L y‖ ≤ D := by
          have hh := OriginalWarmAmortization.actual_warm_dual_distance J L mu hL hmu hJ hLip hsc x y a.saddle.snd tau hprevious
          simpa only [hs] using hh
        have hfirst := actual_estimate J mu L rho D tau hmu hLmu hrho htau hC2 hLip hHess hsc y a.saddle.snd hwarm
        have hayClose : ‖ay.saddle - zStar (JointSliceRegularity.curry J) L y‖ ≤ tau := hfirst.1
        have hay : Accurate Ef M eps y (asAnswer ay) :=
          ⟨hfirst.2.1.trans htolG, hfirst.2.2.1.trans htolH⟩
        have hfirstCost : (first.2 : ℝ) ≤ OriginalStatefulEnvelopeGD.moveCost J mu L rho tau m + 1 := hfirst.2.2.2
        have hstep := actual_step_radius_and_descent Ef hEC2 M eps hM heps hEHess x (asAnswer a) ha
        change (stepRadius M eps ≤ ‖s‖ → M / 4 * ‖s‖ ^ 3 ≤ Ef x - Ef y) ∧
          (∀ ay' : Answer E, Accurate Ef M eps y ay' → ¬ ‖ay'.grad‖ ≤ eps / 2 →
            stepRadius M eps ≤ ‖s‖ ∧ M / 4 * ‖s‖ ^ 3 ≤ Ef x - Ef y) at hstep
        have hvalue : Ef y ≤ Ef x + stepCharge M eps := actual_step_value_upper Ef hEC2 M eps hM heps hEHess x (asAnswer a) ha
        by_cases hnext : ‖ay.grad‖ ≤ eps / 2
        · have hexec : execute (OriginalDualOracleProgram.actualOracle J) (loop mu L rho tau M eps (n + 1) x a) =
              (⟨y, ay.saddle, true, 0, [m]⟩, first.2) := by
            simp only [loop, if_neg hstop, execute_bind]
            change ((execute (OriginalDualOracleProgram.actualOracle J)
              (if ‖ay.grad‖ ≤ eps / 2 then .pure ⟨y, ay.saddle, true, 0, [m]⟩
               else map (appendCharged m) (loop mu L rho tau M eps n y ay))).1,
              first.2 + (execute (OriginalDualOracleProgram.actualOracle J)
              (if ‖ay.grad‖ ≤ eps / 2 then .pure ⟨y, ay.saddle, true, 0, [m]⟩
               else map (appendCharged m) (loop mu L rho tau M eps n y ay))).2) = _
            rw [if_pos hnext]
            rfl

          have hbudget : M / 4 * ‖s‖ ^ 3 ≤ Ef x - lower + stepCharge M eps := by
            by_cases hlarge : stepRadius M eps ≤ ‖s‖
            · have hd := hstep.1 hlarge
              linarith only [hd, hbelow y, hcharge]
            · have hr : ‖s‖ ≤ stepRadius M eps := (lt_of_not_ge hlarge).le
              have hc : ‖s‖ ^ 3 ≤ stepRadius M eps ^ 3 := by gcongr
              have hh := mul_le_mul_of_nonneg_left hc (show 0 ≤ M / 4 by positivity)
              unfold stepCharge
              linarith only [hh, hbelow x]
          rw [hexec]
          refine ⟨hayClose, ?_, ?_, by norm_num, ?_, ?_, ?_, hvalue, ?_⟩
          · simp only [Nat.cast_zero, mul_zero]
            change 0 ≤ Ef x - lower
            linarith only [hbelow x]
          · change M / 4 * (‖y - x‖ ^ 3 + 0) ≤ Ef x - lower + stepCharge M eps
            simpa only [hs, add_zero] using hbudget
          · intro _
            exact accurate_stop Ef M eps heps y (asAnswer ay) hay hnext
          · intro hh
            cases hh
          · simpa only [OriginalStatefulEnvelopeGD.costSum, List.map_cons, List.map_nil,
              List.sum_cons, List.sum_nil, add_zero, List.length_singleton, Nat.cast_one] using hfirstCost
          · intro move hmem
            have he : move = m := List.mem_singleton.mp hmem
            subst move
            refine ⟨hwarm, ?_, le_refl _, hvalue⟩
            change D = tau + 2 * Real.sqrt (L / mu) * ‖y - x‖
            rw [hs]
        · let rest := execute (OriginalDualOracleProgram.actualOracle J) (loop mu L rho tau M eps n y ay)
          have hrec := ih y ay hayClose hay
          change LoopSpec J mu L rho tau M eps lower n y rest at hrec
          have hd := hstep.2 (asAnswer ay) hay hnext
          have hc : stepRadius M eps ^ 3 ≤ ‖s‖ ^ 3 := by exact pow_le_pow_left₀ hp.2.1.le hd.1 3
          have hpaid : stepCharge M eps ≤ M / 4 * ‖s‖ ^ 3 :=
            mul_le_mul_of_nonneg_left hc (show 0 ≤ M / 4 by positivity)
          have hdescent : Ef y ≤ Ef x := by
            have hn : 0 ≤ M / 4 * ‖s‖ ^ 3 := by positivity
            linarith only [hd.2, hn]
          have hexec : execute (OriginalDualOracleProgram.actualOracle J) (loop mu L rho tau M eps (n + 1) x a) =
              (appendCharged m rest.1, first.2 + rest.2) := by
            simp only [loop, if_neg hstop, execute_bind]
            change ((execute (OriginalDualOracleProgram.actualOracle J)
              (if ‖ay.grad‖ ≤ eps / 2 then .pure ⟨y, ay.saddle, true, 0, [m]⟩
               else map (appendCharged m) (loop mu L rho tau M eps n y ay))).1,
              first.2 + (execute (OriginalDualOracleProgram.actualOracle J)
              (if ‖ay.grad‖ ≤ eps / 2 then .pure ⟨y, ay.saddle, true, 0, [m]⟩
               else map (appendCharged m) (loop mu L rho tau M eps n y ay))).2) = _
            rw [if_neg hnext, execute_map]
          rw [hexec]
          have hcube : cubedMovement (m :: rest.1.moves) = ‖s‖ ^ 3 + cubedMovement rest.1.moves := by
            simp only [cubedMovement, List.map_cons, List.sum_cons]
            change ‖y - x‖ ^ 3 + _ = _
            rw [hs]
          refine ⟨hrec.close, ?_, ?_, ?_, hrec.terminal, ?_, ?_, ?_, ?_⟩
          · change stepCharge M eps * ((rest.1.charged + 1 : ℕ) : ℝ) ≤ Ef x - lower
            push_cast
            have hh := hrec.charged_budget
            nlinarith only [hh, hd.2, hpaid]
          · change M / 4 * cubedMovement (m :: rest.1.moves) ≤ Ef x - lower + stepCharge M eps
            rw [hcube]
            have hh := hrec.cube_budget
            nlinarith only [hh, hd.2]
          · have hh := hrec.length_bound
            change (m :: rest.1.moves).length ≤ rest.1.charged + 1 + 1
            simp only [List.length_cons]
            omega
          · intro hh
            exact congrArg Nat.succ (hrec.exhausted hh)
          · change ((first.2 + rest.2 : ℕ) : ℝ) ≤ OriginalStatefulEnvelopeGD.costSum J mu L rho tau (m :: rest.1.moves) + ((m :: rest.1.moves).length : ℝ)
            simp only [Nat.cast_add, OriginalStatefulEnvelopeGD.costSum, List.map_cons, List.sum_cons,
              List.length_cons, Nat.cast_one]
            have hh := hrec.original_cost
            dsimp only [OriginalStatefulEnvelopeGD.costSum] at hh
            linarith only [hh, hfirstCost]
          · have hh := hrec.value_upper
            exact hh.trans (add_le_add hdescent le_rfl)
          · intro move hmem
            rcases List.mem_cons.mp hmem with he | he
            · subst move
              refine ⟨hwarm, ?_, le_refl _, ?_⟩
              · change D = tau + 2 * Real.sqrt (L / mu) * ‖y - x‖
                rw [hs]
              · exact hdescent.trans (le_add_of_nonneg_right hcharge.le)
            · obtain ⟨hlegal, hradius, hprev, hnext⟩ := hrec.legal_moves move he
              exact ⟨hlegal, hradius, hprev.trans hdescent, hnext.trans (add_le_add hdescent le_rfl)⟩

end
end OriginalBorelStatefulEnvelopeCubic


namespace OriginalBorelStatefulEnvelopeCubic
open _root_.OriginalBorelStatefulEnvelopeCubic

open OriginalSaddleImplicit OriginalSaddleTransfer OriginalSaddleStability
open OriginalBetaATSTrial FangqingGetterComposition
open OriginalEnvelopeOracleProgram
open OriginalBorelOuterCubic OriginalBorelOuterCubicSeparateErrors

noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 6000

universe u
variable {E F : Type u}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

def program (mu L rho D0 tau M eps Delta : ℝ) (start : E) (yin : F) :
    GetterProgram (Joint E F) (OriginalDualOracleProgram.OracleAnswer (Joint E F)) (Result E F) :=
  bind (estimateProgram mu L rho D0 tau start yin) (fun a =>
    loop mu L rho tau M eps (OriginalBorelOuterCubicSeparateErrors.fuel Delta M eps) start a)

/-- The complete stateful cubic execution halts. The extra terminal cube and its
slightly larger level set are retained explicitly, including when the gap is zero. -/
theorem actual_finite_termination_with_warm_trace
    (J : Joint E F → ℝ) (mu L rho D0 tau M eps Delta lower : ℝ)
    (hmu : 0 < mu) (hLmu : mu ≤ L) (hrho : 0 ≤ rho) (htau : 0 < tau)
    (hM : 0 < M) (heps : 0 < eps)
    (htolG : 2 * L * tau ≤ eps / 1024)
    (htolH : 4 * rho * (1 + L / mu) ^ 2 * tau ≤ Real.sqrt (M * eps) / 1024)
    (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (hHess : ∀ z w : Joint E F, ‖fderiv ℝ (gradient J) z - fderiv ℝ (gradient J) w‖ ≤ rho * ‖z - w‖)
    (hsc : ∀ u : E, StrongConvexOn (Set.univ : Set F) mu (fun y => -JointSliceRegularity.curry J u y))
    (hEHess : ∀ x y : E,
      ‖fderiv ℝ (gradient (saddleEnvelope (JointSliceRegularity.curry J) L)) x -
        fderiv ℝ (gradient (saddleEnvelope (JointSliceRegularity.curry J) L)) y‖ ≤ M * ‖x - y‖)
    (hbelow : ∀ x : E, lower ≤ saddleEnvelope (JointSliceRegularity.curry J) L x)
    (start : E) (yin : F)
    (hgap : saddleEnvelope (JointSliceRegularity.curry J) L start - lower ≤ Delta)
    (hwarm : ‖yin - vStar (JointSliceRegularity.curry J) L start‖ ≤ D0) :
    let run := execute (OriginalDualOracleProgram.actualOracle J)
      (program mu L rho D0 tau M eps Delta start yin)
    run.1.success = true ∧
    ‖gradient (saddleEnvelope (JointSliceRegularity.curry J) L) run.1.point‖ ≤ eps ∧
    ‖run.1.saddle - zStar (JointSliceRegularity.curry J) L run.1.point‖ ≤ tau ∧
    (run.1.moves.length : ℝ) ≤ 1 + Delta / stepCharge M eps ∧
    cubedMovement run.1.moves ≤ 4 * Delta / M + stepRadius M eps ^ 3 ∧
    (run.2 : ℝ) ≤ OriginalStatefulEnvelopeGD.initialCost J mu L rho D0 tau start yin +
      1 + OriginalStatefulEnvelopeGD.costSum J mu L rho tau run.1.moves + (run.1.moves.length : ℝ) ∧
    (∀ m ∈ run.1.moves,
      ‖m.warm - vStar (JointSliceRegularity.curry J) L m.next‖ ≤ m.radius ∧
      m.radius = tau + 2 * Real.sqrt (L / mu) * ‖m.next - m.previous‖ ∧
      saddleEnvelope (JointSliceRegularity.curry J) L m.previous - lower ≤ Delta ∧
      saddleEnvelope (JointSliceRegularity.curry J) L m.next - lower ≤ Delta + stepCharge M eps) := by
  let first := execute (OriginalDualOracleProgram.actualOracle J)
    (estimateProgram mu L rho D0 tau start yin)
  let n := OriginalBorelOuterCubicSeparateErrors.fuel Delta M eps
  let rest := execute (OriginalDualOracleProgram.actualOracle J)
    (loop mu L rho tau M eps n start first.1)
  have hp := radius_properties M eps hM heps
  have hcharge : 0 < stepCharge M eps := hp.2.2.2
  have hfirst := actual_estimate J mu L rho D0 tau hmu hLmu hrho htau hC2 hLip hHess hsc start yin hwarm
  have hclose : ‖first.1.saddle - zStar (JointSliceRegularity.curry J) L start‖ ≤ tau := hfirst.1
  have ha : Accurate (saddleEnvelope (JointSliceRegularity.curry J) L) M eps start (asAnswer first.1) :=
    ⟨hfirst.2.1.trans htolG, hfirst.2.2.1.trans htolH⟩
  have hcost0 : (first.2 : ℝ) ≤ OriginalStatefulEnvelopeGD.initialCost J mu L rho D0 tau start yin + 1 := hfirst.2.2.2
  have hs := actual_loop_spec J mu L rho tau M eps lower hmu hLmu hrho htau hM heps htolG htolH
    hC2 hLip hHess hsc hEHess hbelow n start first.1 hclose ha
  change LoopSpec J mu L rho tau M eps lower n start rest at hs
  have hc : (rest.1.charged : ℝ) ≤ Delta / stepCharge M eps := by
    apply (le_div_iff₀ hcharge).mpr
    have hh := hs.charged_budget
    nlinarith only [hh, hgap]
  have hsuccess : rest.1.success = true := by
    cases hb : rest.1.success with
    | true => rfl
    | false =>
        have hcount := hs.exhausted hb
        rw [hcount] at hc
        dsimp [n, OriginalBorelOuterCubicSeparateErrors.fuel] at hc
        push_cast at hc
        have hceil := Nat.le_ceil (Delta / stepCharge M eps)
        linarith only [hc, hceil]
  have hlength : (rest.1.moves.length : ℝ) ≤ 1 + Delta / stepCharge M eps := by
    have hh : (rest.1.moves.length : ℝ) ≤ (rest.1.charged : ℝ) + 1 := by exact_mod_cast hs.length_bound
    linarith only [hc, hh]
  have hcubes : cubedMovement rest.1.moves ≤ 4 * Delta / M + stepRadius M eps ^ 3 := by
    have hh := hs.cube_budget
    have hm : M * (4 * Delta / M + stepRadius M eps ^ 3) = 4 * Delta + 4 * stepCharge M eps := by
      unfold stepCharge
      field_simp
      <;> ring
    have hmul : M * cubedMovement rest.1.moves ≤ M * (4 * Delta / M + stepRadius M eps ^ 3) := by
      nlinarith only [hh, hgap, hm]
    exact (mul_le_mul_iff_right₀ hM).mp hmul
  have hexec : execute (OriginalDualOracleProgram.actualOracle J)
      (program mu L rho D0 tau M eps Delta start yin) = (rest.1, first.2 + rest.2) := by
    simp only [program, execute_bind]
    rfl
  rw [hexec]
  refine ⟨hsuccess, hs.terminal hsuccess, hs.close, hlength, hcubes, ?_, ?_⟩
  · simp only [Nat.cast_add]
    have hh := hs.original_cost
    linarith only [hh, hcost0]
  · intro m hm
    obtain ⟨hw, hr, hp, hn⟩ := hs.legal_moves m hm
    exact ⟨hw, hr, by linarith only [hp, hgap], by linarith only [hn, hgap]⟩

end
end OriginalBorelStatefulEnvelopeCubic


namespace OriginalBorelStatefulEnvelopeCubic
open _root_.OriginalBorelStatefulEnvelopeCubic

open OriginalSaddleImplicit OriginalSaddleTransfer OriginalSaddleStability
open OriginalBetaATSTrial FangqingGetterComposition
open OriginalBorelOuterCubicSeparateErrors

universe u
variable {E F : Type u}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 5000

def curvature (mu L rho : ℝ) := 8 * rho * (1 + L / mu) ^ (3 / 2 : ℝ)

def callerTolerance (mu L rho eps : ℝ) :=
  min (eps / (4096 * L))
    (min (Real.sqrt (curvature mu L rho * (eps / 2)) / (4096 * rho * (1 + L / mu) ^ 2))
      (min (mu / rho) (OriginalStatefulEnvelopeGD.callerTolerance mu L eps)))

def caller (mu L rho Delta Ry eps : ℝ) (start : E) (yin : F) :
    GetterProgram (Joint E F) (OriginalDualOracleProgram.OracleAnswer (Joint E F)) (Result E F) :=
  program mu L rho (Ry + (L / mu) * Real.sqrt (Delta / L)) (callerTolerance mu L rho eps)
    (curvature mu L rho) (eps / 2) Delta start yin

theorem actual_cubic_caller_from_original_inputs
    (J : Joint E F → ℝ) (mu L rho Delta Ry eps : ℝ)
    (hmu : 0 < mu) (hLmu : mu ≤ L) (hrho : 0 < rho) (heps : 0 < eps)
    (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (hHess : ∀ z w : Joint E F, ‖fderiv ℝ (gradient J) z - fderiv ℝ (gradient J) w‖ ≤ rho * ‖z - w‖)
    (hsc : ∀ u : E, StrongConvexOn (Set.univ : Set F) mu
      (fun y => -JointSliceRegularity.curry J u y))
    (hbelow : BddBelow (Set.range (phi (JointSliceRegularity.curry J))))
    (start : E) (yin : F)
    (hgap : phi (JointSliceRegularity.curry J) start - sInf (Set.range (phi (JointSliceRegularity.curry J))) ≤ Delta)
    (hdual : ‖yin - yStar (JointSliceRegularity.curry J) start‖ ≤ Ry) :
    let M := curvature mu L rho
    let tau := callerTolerance mu L rho eps
    let D0 := Ry + (L / mu) * Real.sqrt (Delta / L)
    let run := execute (OriginalDualOracleProgram.actualOracle J) (caller mu L rho Delta Ry eps start yin)
    run.1.success = true ∧
    ‖gradient (phi (JointSliceRegularity.curry J)) run.1.saddle.fst‖ ≤ eps ∧
    (run.1.moves.length : ℝ) ≤ 1 + Delta / stepCharge M (eps / 2) ∧
    cubedMovement run.1.moves ≤ 4 * Delta / M + stepRadius M (eps / 2) ^ 3 ∧
    (run.2 : ℝ) ≤ OriginalStatefulEnvelopeGD.initialCost J mu L rho D0 tau start yin + 1 +
      OriginalStatefulEnvelopeGD.costSum J mu L rho tau run.1.moves + (run.1.moves.length : ℝ) ∧
    (∀ m ∈ run.1.moves,
      ‖m.warm - vStar (JointSliceRegularity.curry J) L m.next‖ ≤ m.radius ∧
      m.radius = tau + 2 * Real.sqrt (L / mu) * ‖m.next - m.previous‖ ∧
      OriginalDualResidualQueryBound.observedRadius J L m.next m.next m.warm ≤
        3 * (Real.sqrt ((Delta + stepCharge M (eps / 2)) / L) + m.radius)) := by
  let f := JointSliceRegularity.curry J
  let lower := sInf (Set.range (phi f))
  let tau := callerTolerance mu L rho eps
  let D0 := Ry + (L / mu) * Real.sqrt (Delta / L)
  let run := execute (OriginalDualOracleProgram.actualOracle J) (caller mu L rho Delta Ry eps start yin)
  have hL : 0 < L := hmu.trans_le hLmu
  let M := curvature mu L rho
  have hM : 0 < M := by dsimp [M, curvature]; positivity
  have hratio : 0 < L / mu := by positivity
  have htau : 0 < tau := by
    have hsq : 0 < Real.sqrt (M * (eps / 2)) := Real.sqrt_pos.mpr (by positivity)
    have hgd : 0 < OriginalStatefulEnvelopeGD.callerTolerance mu L eps := by
      unfold OriginalStatefulEnvelopeGD.callerTolerance
      positivity
    change 0 < min (eps / (4096 * L))
      (min (Real.sqrt (M * (eps / 2)) / (4096 * rho * (1 + L / mu) ^ 2))
        (min (mu / rho) (OriginalStatefulEnvelopeGD.callerTolerance mu L eps)))
    positivity
  have htolG : 2 * L * tau ≤ (eps / 2) / 1024 := by
    have ht : tau ≤ eps / (4096 * L) := min_le_left _ _
    have hh := mul_le_mul_of_nonneg_left ht (show 0 ≤ 2 * L by positivity)
    have he : 2 * L * (eps / (4096 * L)) = (eps / 2) / 1024 := by field_simp; ring
    exact hh.trans_eq he
  have htolH : 4 * rho * (1 + L / mu) ^ 2 * tau ≤ Real.sqrt (M * (eps / 2)) / 1024 := by
    have ht : tau ≤ Real.sqrt (M * (eps / 2)) / (4096 * rho * (1 + L / mu) ^ 2) :=
      (min_le_right _ _).trans (min_le_left _ _)
    have hh := mul_le_mul_of_nonneg_left ht (show 0 ≤ 4 * rho * (1 + L / mu) ^ 2 by positivity)
    have he : 4 * rho * (1 + L / mu) ^ 2 *
        (Real.sqrt (M * (eps / 2)) / (4096 * rho * (1 + L / mu) ^ 2)) = Real.sqrt (M * (eps / 2)) / 1024 := by
      field_simp
      <;> ring
    exact hh.trans_eq he
  have htoutput : tau ≤ OriginalStatefulEnvelopeGD.callerTolerance mu L eps :=
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))

  have hJ := JointSliceRegularity.differentiable_joint_of_contDiff2 J hC2
  have hdx := JointSliceRegularity.differentiable_x_slice J hJ
  have hdy := JointSliceRegularity.differentiable_y_slice J hJ
  have hxx := fun y u v => JointSliceRegularity.gradient_x_lipschitz_in_x J hJ L hLip u v y
  have hxy := fun u y v => JointSliceRegularity.gradient_x_lipschitz_in_y J hJ L hLip u y v
  obtain ⟨hPhi, hweak⟩ := phi_regular_from_slices f L mu hL hmu hdx hdy hsc hxx hxy
  have hE := saddleEnvelope_eq_moreau f L mu hmu hsc hdy
  have hElower : ∀ x, lower ≤ saddleEnvelope f L x := by
    intro x
    rw [hE, MoreauTransfer.envelope_eq_prox_objective (phi f) L hL hPhi hweak]
    have hp := csInf_le hbelow (Set.mem_range_self (MoreauTransfer.prox (phi f) L x))
    unfold MoreauTransfer.objective
    have hn : 0 ≤ L * ‖MoreauTransfer.prox (phi f) L x - x‖ ^ 2 := by positivity
    change lower ≤ phi f (MoreauTransfer.prox (phi f) L x) + _
    linarith only [hp, hn]
  have hEgap : saddleEnvelope f L start - lower ≤ Delta := by
    have hh := MoreauTransfer.envelope_le_original (phi f) L hL hPhi hweak start
    rw [← hE] at hh
    linarith only [hh, hgap]
  have hinit := OriginalInitialSaddleRadius.actual_initial_dual_radius J L mu Delta Ry
    hL hmu hC2 hLip hsc hbelow start yin hgap hdual
  have hEHess := (OriginalEnvelopeRegularity.envelope_regularity_from_joint_negative_slice
    J L mu rho hL hmu hrho.le hC2 hsc hLip hHess).2.2
  have hh := actual_finite_termination_with_warm_trace J mu L rho D0 tau M (eps / 2) Delta lower
    hmu hLmu hrho.le htau hM (by positivity) htolG htolH hC2 hLip hHess hsc hEHess hElower start yin hEgap hinit
  change run.1.success = true ∧ _ at hh
  rcases hh with ⟨htrue, hgradE, hclose, hcount, hcubes, hcost, htrace⟩
  change ‖gradient (saddleEnvelope f L) run.1.point‖ ≤ eps / 2 at hgradE
  have htransfer := exact_transfer_from_slices f L mu hL hmu hdx hdy hsc hxx hxy hbelow start Delta hgap
  have hPhiLip := OriginalStatefulEnvelopeGD.actual_phi_gradient_lipschitz J mu L hmu hL hC2 hLip hsc
  have hfirst : ‖run.1.saddle.fst - uStar f L run.1.point‖ ≤ tau := by
    exact (WithLp.norm_fst_le E (run.1.saddle - zStar f L run.1.point)).trans hclose
  have houtput : ‖gradient (phi f) run.1.saddle.fst‖ ≤ eps := by
    have hd := hPhiLip run.1.saddle.fst (uStar f L run.1.point)
    have hm := mul_le_mul_of_nonneg_left hfirst (show 0 ≤ L * (1 + L / mu) by positivity)
    have hn := norm_le_norm_sub_add (gradient (phi f) run.1.saddle.fst)
      (gradient (phi f) (uStar f L run.1.point))
    change ‖gradient (phi f) run.1.saddle.fst - gradient (phi f) (uStar f L run.1.point)‖ ≤ _ at hd
    rw [← (htransfer.1 run.1.point).2] at hn hd
    have hmul := mul_le_mul_of_nonneg_left htoutput (show 0 ≤ L * (1 + L / mu) by positivity)
    have he : L * (1 + L / mu) * OriginalStatefulEnvelopeGD.callerTolerance mu L eps = eps / 128 := by
      unfold OriginalStatefulEnvelopeGD.callerTolerance
      field_simp
      <;> ring
    rw [he] at hmul
    linarith only [hd, hm, hn, hgradE, hmul, heps]
  refine ⟨htrue, houtput, hcount, hcubes, hcost, ?_⟩
  · intro m hm
    obtain ⟨hlegal, hradius, hprev, hnext⟩ := htrace m hm
    have hb := (OriginalOuterPrimalInitialization.standing_primal_residual_bound J L mu lower (Delta + stepCharge M (eps / 2)) m.radius
      hL hmu hC2 hLip hsc (fun u => csInf_le hbelow ⟨u, rfl⟩) m.next m.warm hnext hlegal).2.2
    exact ⟨hlegal, hradius, hb⟩


end
end OriginalBorelStatefulEnvelopeCubic


open scoped BigOperators
namespace OriginalBorelStatefulEnvelopeCubic
open _root_.OriginalBorelStatefulEnvelopeCubic
open OriginalStatefulEnvelopeGD
open OriginalSaddleImplicit OriginalSaddleTransfer OriginalSaddleStability
noncomputable section
set_option maxHeartbeats 4000000
universe u
variable {E F : Type u}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

def cubicPolynomialBound (mu L rho tau : ℝ) (moves : List (Move E F)) : ℝ :=
  (moves.length : ℝ) * (1 + (rho * tau / mu) ^ (2 / 7 : ℝ)) +
    (rho / mu * (2 * Real.sqrt (L / mu))) ^ (2 / 7 : ℝ) *
      (moves.length : ℝ) ^ (19 / 21 : ℝ) * cubedMovement moves ^ (2 / 21 : ℝ)

/-- Actual per-move costs are amortized over the actual physical step trace.
The finite maximum of log-factors is retained explicitly, rather than assumed to be
uniformly polylogarithmic. -/
theorem actual_cubic_cost_sum_holder_bound
    (J : Joint E F → ℝ) (mu L rho tau : ℝ) (hmu : 0 < mu) (hL : 0 < L)
    (hrho : 0 ≤ rho) (htau : 0 ≤ tau) (moves : List (Move E F))
    (hradii : ∀ m ∈ moves, m.radius = tau + 2 * Real.sqrt (L / mu) * ‖m.next - m.previous‖) :
    costSum J mu L rho tau moves ≤
      maximumLog J mu L rho tau moves * cubicPolynomialBound mu L rho tau moves := by
  let N := moves.length
  let step : Fin N → ℝ := fun i => ‖(moves.get i).next - (moves.get i).previous‖
  let radius : Fin N → ℝ := fun i => rho * (moves.get i).radius / mu
  have hradius : ∀ i : Fin N, 0 ≤ (moves.get i).radius := by
    intro i
    rw [hradii (moves.get i) (List.get_mem _ _)]
    positivity
  have hM : 0 ≤ maximumLog J mu L rho tau moves :=
    (by norm_num : (0 : ℝ) ≤ 1).trans (maximum_log_positive J mu L rho tau moves)
  have hpoint : ∀ i : Fin N,
      moveCost J mu L rho tau (moves.get i) ≤
        maximumLog J mu L rho tau moves * (1 + radius i ^ (2 / 7 : ℝ)) := by
    intro i
    have hlog : moveLog J mu L rho tau (moves.get i) ≤ maximumLog J mu L rho tau moves := by
      exact List.le_max_of_le' 1 (List.mem_map.mpr ⟨moves.get i, List.get_mem _ _, rfl⟩) le_rfl
    have hscale : 0 ≤ 1 + min (Real.sqrt (L / mu)) (radius i ^ (2 / 7 : ℝ)) := by
      have hp : 0 ≤ radius i := div_nonneg (mul_nonneg hrho (hradius i)) hmu.le
      exact add_nonneg zero_le_one (le_min (Real.sqrt_nonneg _) (Real.rpow_nonneg hp _))
    have ha := mul_le_mul_of_nonneg_left hlog hscale
    have hb := mul_le_mul_of_nonneg_left
      (add_le_add_left (min_le_right (Real.sqrt (L / mu)) (radius i ^ (2 / 7 : ℝ))) 1) hM
    change (1 + min (Real.sqrt (L / mu)) (radius i ^ (2 / 7 : ℝ))) *
      moveLog J mu L rho tau (moves.get i) ≤ _
    exact ha.trans (by nlinarith only [hb])
  have hholder := OriginalWarmAmortization.warm_cost_sum_from_cubed_steps
    (Finset.univ : Finset (Fin N)) step radius (rho * tau / mu)
    (rho / mu * (2 * Real.sqrt (L / mu))) (by positivity) (by positivity)
    (fun _ _ => norm_nonneg _) (fun i _ => div_nonneg (mul_nonneg hrho (hradius i)) hmu.le) (by
      intro i _
      have hi := hradii (moves.get i) (List.get_mem _ _)
      change rho * (moves.get i).radius / mu ≤ rho * tau / mu +
        rho / mu * (2 * Real.sqrt (L / mu)) * ‖(moves.get i).next - (moves.get i).previous‖
      rw [hi]
      ring_nf
      exact le_rfl)
  have hcubes : ∑ i : Fin N, step i ^ 3 = cubedMovement moves :=
    (list_sum_as_fin moves (fun m => ‖m.next - m.previous‖ ^ 3)).symm
  have hpoly : ∑ i : Fin N, (1 + radius i ^ (2 / 7 : ℝ)) ≤ cubicPolynomialBound mu L rho tau moves := by
    simpa only [Finset.card_univ, Fintype.card_fin, hcubes, N, cubicPolynomialBound] using hholder
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hpoint i)
  rw [← Finset.mul_sum] at hsum
  rw [costSum, list_sum_as_fin]
  exact hsum.trans (mul_le_mul_of_nonneg_left hpoly hM)


theorem cubed_movement_nonnegative (moves : List (Move E F)) : 0 ≤ cubedMovement moves := by
  exact List.sum_nonneg (fun x hx => by
    obtain ⟨m, _, rfl⟩ := List.mem_map.mp hx
    positivity)

theorem one_step_cubed_le_total (moves : List (Move E F)) (m : Move E F) (hm : m ∈ moves) :
    ‖m.next - m.previous‖ ^ 3 ≤ cubedMovement moves := by
  induction moves with
  | nil => cases hm
  | cons head tail ih =>
      simp only [cubedMovement, List.map_cons, List.sum_cons]
      rcases List.mem_cons.mp hm with h | h
      · subst m
        exact le_add_of_nonneg_right (cubed_movement_nonnegative tail)
      · exact (ih h).trans (le_add_of_nonneg_left (by positivity))

theorem norm_le_one_add_cube (v : E) : ‖v‖ ≤ 1 + ‖v‖ ^ 3 := by
  by_cases h : ‖v‖ ≤ 1
  · have hc : 0 ≤ ‖v‖ ^ 3 := by positivity
    linarith only [h, hc]
  · have h1 : 1 ≤ ‖v‖ := (lt_of_not_ge h).le
    have hh := mul_nonneg (sub_nonneg.mpr h1) (show 0 ≤ ‖v‖ ^ 2 + ‖v‖ by positivity)
    nlinarith only [hh]

theorem cubic_warm_radii_uniform_bound (L mu tau B : ℝ)
    (moves : List (Move E F)) (hcubes : cubedMovement moves ≤ B)
    (hradii : ∀ m ∈ moves, m.radius = tau + 2 * Real.sqrt (L / mu) * ‖m.next - m.previous‖) :
    ∀ m ∈ moves, m.radius ≤ tau + 2 * Real.sqrt (L / mu) * (1 + B) := by
  intro m hm
  have hstep := (one_step_cubed_le_total moves m hm).trans hcubes
  have hn := norm_le_one_add_cube (m.next - m.previous)
  have hh := mul_le_mul_of_nonneg_left (show ‖m.next - m.previous‖ ≤ 1 + B by linarith only [hn,hstep])
    (show 0 ≤ 2 * Real.sqrt (L / mu) by positivity)
  rw [hradii m hm]
  linarith only [hh]

end
end OriginalBorelStatefulEnvelopeCubic


namespace OriginalBorelCubicHolderNormalization
open _root_.OriginalBorelCubicHolderNormalization

set_option maxHeartbeats 3000000

/-- The terminal cube is charged to the same `1 + gap / charge` factor as the
actual number of moves. No small-epsilon premise or unconditional cube-sum bound
is used. -/
theorem holder_with_terminal_budget
    (N C B R a b : ℝ) (hN : 0 ≤ N) (hC : 0 ≤ C) (hB : 0 < B) (hR : 0 < R)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hNB : N ≤ B) (hCB : C ≤ B * R ^ 3)
    (ha1 : a ≤ 1) (hbR : b * R ≤ 1) :
    N * (1 + a ^ (2 / 7 : ℝ)) +
      b ^ (2 / 7 : ℝ) * N ^ (19 / 21 : ℝ) * C ^ (2 / 21 : ℝ) ≤ 3 * B := by
  have haPow : a ^ (2 / 7 : ℝ) ≤ 1 := by
    simpa using Real.rpow_le_rpow ha ha1 (by norm_num : (0 : ℝ) ≤ 2 / 7)
  have hNPow := Real.rpow_le_rpow hN hNB (by norm_num : (0 : ℝ) ≤ 19 / 21)
  have hCPow := Real.rpow_le_rpow hC hCB (by norm_num : (0 : ℝ) ≤ 2 / 21)
  have hRPow : (R ^ 3) ^ (2 / 21 : ℝ) = R ^ (2 / 7 : ℝ) := by
    rw [← Real.rpow_natCast R 3, ← Real.rpow_mul hR.le]
    norm_num
  have hBPow : B ^ (19 / 21 : ℝ) * B ^ (2 / 21 : ℝ) = B := by
    rw [← Real.rpow_add hB]
    norm_num
  have hprod : b ^ (2 / 7 : ℝ) * N ^ (19 / 21 : ℝ) * C ^ (2 / 21 : ℝ) ≤ B := by
    have h1 := mul_le_mul_of_nonneg_left hNPow (Real.rpow_nonneg hb (2 / 7 : ℝ))
    have h2 := mul_le_mul h1 hCPow (Real.rpow_nonneg hC (2 / 21 : ℝ))
      (mul_nonneg (Real.rpow_nonneg hb _) (Real.rpow_nonneg hB.le _))
    have hid : b ^ (2 / 7 : ℝ) * B ^ (19 / 21 : ℝ) * (B * R ^ 3) ^ (2 / 21 : ℝ) =
        B * (b * R) ^ (2 / 7 : ℝ) := by
      rw [Real.mul_rpow hB.le (pow_nonneg hR.le 3), hRPow, Real.mul_rpow hb hR.le]
      calc
        _ = (B ^ (19 / 21 : ℝ) * B ^ (2 / 21 : ℝ)) *
            (b ^ (2 / 7 : ℝ) * R ^ (2 / 7 : ℝ)) := by ring
        _ = _ := by rw [hBPow]
    rw [hid] at h2
    have h3 : (b * R) ^ (2 / 7 : ℝ) ≤ 1 := by
      simpa using Real.rpow_le_rpow (mul_nonneg hb hR.le) hbR (by norm_num : (0 : ℝ) ≤ 2 / 7)
    exact h2.trans (by nlinarith only [mul_le_mul_of_nonneg_left h3 hB.le])
  have hfirst := mul_le_mul hNB (show 1 + a ^ (2 / 7 : ℝ) ≤ 2 by linarith only [haPow])
    (show 0 ≤ 1 + a ^ (2 / 7 : ℝ) by positivity) hB.le
  nlinarith only [hfirst, hprod]

end OriginalBorelCubicHolderNormalization


namespace OriginalBorelCubicSelectedRegime
open _root_.OriginalBorelCubicSelectedRegime
noncomputable section
set_option maxHeartbeats 3000000

theorem warm_coefficient_times_step_radius_le_one
    (mu L rho eps : ℝ) (hmu : 0 < mu) (hLmu : mu ≤ L) (hrho : 0 < rho) (heps : 0 < eps)
    (hr : OriginalGDRateNormalization.ratio mu L rho eps ≤ 1) :
    (rho / mu * (2 * Real.sqrt (L / mu))) *
      OriginalBorelOuterCubicSeparateErrors.stepRadius (OriginalBorelStatefulEnvelopeCubic.curvature mu L rho) (eps / 2) ≤ 1 := by
  let s := Real.sqrt (L / mu)
  let M := OriginalBorelStatefulEnvelopeCubic.curvature mu L rho
  let R := OriginalBorelOuterCubicSeparateErrors.stepRadius M (eps / 2)
  let b := rho / mu * (2 * s)
  have hL : 0 < L := hmu.trans_le hLmu
  have hs : 0 < s := Real.sqrt_pos.mpr (by positivity)
  have hs2 : s ^ 2 = L / mu := Real.sq_sqrt (by positivity)
  have hLeq : L = mu * s ^ 2 := by rw [hs2]; field_simp
  have hM : 0 < M := by dsimp [M, OriginalBorelStatefulEnvelopeCubic.curvature]; positivity
  have hp := OriginalBorelOuterCubicSeparateErrors.radius_properties M (eps / 2) hM (by positivity)
  have hR : 0 < R := hp.2.1
  have hMR0 := hp.2.2.1
  have hMR : M * R ^ 2 = eps / 32 := by change M * R ^ 2 = eps / 2 / 16 at hMR0; linarith only [hMR0]
  have hpower : (L / mu) ^ (3 / 2 : ℝ) = s ^ 3 := by
    dsimp only [s]
    symm
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul (show 0 ≤ L / mu by positivity)]
    norm_num
  have hMLower : 8 * rho * s ^ 3 ≤ M := by
    have hpow := Real.rpow_le_rpow (show 0 ≤ L / mu by positivity)
      (show L / mu ≤ 1 + L / mu by linarith) (by norm_num : (0 : ℝ) ≤ 3 / 2)
    rw [hpower] at hpow
    exact mul_le_mul_of_nonneg_left hpow (by positivity)
  have hRbound : R ^ 2 ≤ eps / (256 * rho * s ^ 3) := by
    apply (le_div_iff₀ (show 0 < 256 * rho * s ^ 3 by positivity)).mpr
    have hh := mul_le_mul_of_nonneg_right hMLower (sq_nonneg R)
    nlinarith only [hh, hMR]
  have hb2 := mul_le_mul_of_nonneg_left hRbound (sq_nonneg b)
  have hid : b ^ 2 * (eps / (256 * rho * s ^ 3)) =
      OriginalGDRateNormalization.ratio mu L rho eps / 64 := by
    dsimp only [b, OriginalGDRateNormalization.ratio]
    change (rho / mu * (2 * s)) ^ 2 * (eps / (256 * rho * s ^ 3)) =
      (rho * s ^ 3 * eps / L ^ 2) / 64
    rw [hLeq]
    field_simp
    <;> ring
  rw [hid] at hb2
  have hb : 0 ≤ b * R := by dsimp [b]; positivity
  change b * R ≤ 1
  nlinarith only [hb2, hr, hb]

theorem terminal_cube_budget_factorization (Delta M eps : ℝ) (hM : 0 < M) (heps : 0 < eps) :
    4 * Delta / M + OriginalBorelOuterCubicSeparateErrors.stepRadius M eps ^ 3 =
      (1 + Delta / OriginalBorelOuterCubicSeparateErrors.stepCharge M eps) *
        OriginalBorelOuterCubicSeparateErrors.stepRadius M eps ^ 3 := by
  have hp := OriginalBorelOuterCubicSeparateErrors.radius_properties M eps hM heps
  have hR : OriginalBorelOuterCubicSeparateErrors.stepRadius M eps ≠ 0 := ne_of_gt hp.2.1
  unfold OriginalBorelOuterCubicSeparateErrors.stepCharge
  field_simp
  <;> ring

end
end OriginalBorelCubicSelectedRegime


namespace OriginalBorelStatefulEnvelopeCubic
open _root_.OriginalBorelStatefulEnvelopeCubic

open OriginalSaddleImplicit OriginalSaddleTransfer OriginalSaddleStability
open OriginalBetaATSTrial OriginalBorelOuterCubicSeparateErrors
open OriginalStatefulEnvelopeGD

universe u
variable {E F : Type u}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 6000

def cubicBudget (mu L rho Delta eps : ℝ) :=
  1 + Delta / stepCharge (curvature mu L rho) (eps / 2)

def cubeBound (mu L rho Delta eps : ℝ) :=
  4 * Delta / curvature mu L rho + stepRadius (curvature mu L rho) (eps / 2) ^ 3

def queryGap (mu L rho Delta eps : ℝ) := Delta + stepCharge (curvature mu L rho) (eps / 2)

def globalWarmRadius (mu L rho Delta Ry eps : ℝ) :=
  max (OriginalStatefulEnvelopeGD.initialRadius mu L Delta Ry)
    (callerTolerance mu L rho eps + 2 * Real.sqrt (L / mu) * (1 + cubeBound mu L rho Delta eps))

def globalObservedRadius (mu L rho Delta Ry eps : ℝ) :=
  3 * (Real.sqrt (queryGap mu L rho Delta eps / L) + globalWarmRadius mu L rho Delta Ry eps)

def globalLogFactor (mu L rho Delta Ry eps : ℝ) :=
  OriginalUniformMinimumWarmLog.uniformFactor mu L rho (globalWarmRadius mu L rho Delta Ry eps)
    (callerTolerance mu L rho eps) (globalObservedRadius mu L rho Delta Ry eps)

/-- The genuine cubic caller has a parameter-only logarithmic factor and a full
original-oracle budget in the selected `r ≤ 1` regime. Both the terminal move and
its extra envelope query are included. -/
theorem actual_uniform_cubic_selected_branch
    (J : Joint E F → ℝ) (mu L rho Delta Ry eps : ℝ)
    (hmu : 0 < mu) (hLmu : mu ≤ L) (hrho : 0 < rho) (heps : 0 < eps)
    (hr : OriginalGDRateNormalization.ratio mu L rho eps ≤ 1)
    (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (hHess : ∀ z w : Joint E F, ‖fderiv ℝ (gradient J) z - fderiv ℝ (gradient J) w‖ ≤ rho * ‖z - w‖)
    (hsc : ∀ u : E, StrongConvexOn (Set.univ : Set F) mu (fun y => -JointSliceRegularity.curry J u y))
    (hbelow : BddBelow (Set.range (phi (JointSliceRegularity.curry J))))
    (start : E) (yin : F)
    (hgap : phi (JointSliceRegularity.curry J) start - sInf (Set.range (phi (JointSliceRegularity.curry J))) ≤ Delta)
    (hdual : ‖yin - yStar (JointSliceRegularity.curry J) start‖ ≤ Ry) :
    let run := execute (OriginalDualOracleProgram.actualOracle J) (caller mu L rho Delta Ry eps start yin)
    let U := globalLogFactor mu L rho Delta Ry eps
    1 ≤ U ∧ run.1.success = true ∧
    ‖gradient (phi (JointSliceRegularity.curry J)) run.1.saddle.fst‖ ≤ eps ∧
    (run.2 : ℝ) ≤ U * (OriginalStatefulEnvelopeGD.initializationPolynomial mu L rho Delta Ry +
      1 + 4 * cubicBudget mu L rho Delta eps) := by
  let tau := callerTolerance mu L rho eps
  let M := curvature mu L rho
  let D0 := OriginalStatefulEnvelopeGD.initialRadius mu L Delta Ry
  let B := cubicBudget mu L rho Delta eps
  let R := globalWarmRadius mu L rho Delta Ry eps
  let Obs := globalObservedRadius mu L rho Delta Ry eps
  let U := globalLogFactor mu L rho Delta Ry eps
  let run := execute (OriginalDualOracleProgram.actualOracle J) (caller mu L rho Delta Ry eps start yin)
  have hL : 0 < L := hmu.trans_le hLmu
  have hM : 0 < M := by dsimp [M, curvature]; positivity
  have hp := radius_properties M (eps / 2) hM (by positivity)
  have hcharge : 0 < stepCharge M (eps / 2) := hp.2.2.2
  have hDelta : 0 ≤ Delta := by
    have hi := csInf_le hbelow (Set.mem_range_self start)
    linarith only [hgap, hi]
  have hB : 0 < B := by dsimp [B,cubicBudget]; positivity
  have hCB : 0 ≤ cubeBound mu L rho Delta eps := by
    change 0 ≤ 4 * Delta / M + stepRadius M (eps / 2) ^ 3
    exact add_nonneg (by positivity) (pow_nonneg hp.2.1.le 3)
  have htau : 0 < tau := by
    have hsq : 0 < Real.sqrt (M * (eps / 2)) := Real.sqrt_pos.mpr (by positivity)
    have hgd : 0 < OriginalStatefulEnvelopeGD.callerTolerance mu L eps := by
      unfold OriginalStatefulEnvelopeGD.callerTolerance
      positivity
    change 0 < min (eps / (4096 * L))
      (min (Real.sqrt (M * (eps / 2)) / (4096 * rho * (1 + L / mu) ^ 2))
        (min (mu / rho) (OriginalStatefulEnvelopeGD.callerTolerance mu L eps)))
    positivity
  have hRtau : tau ≤ R := by
    apply le_trans ?_ (le_max_right _ _)
    exact le_add_of_nonneg_right (by positivity)
  have hR0 : D0 ≤ R := le_max_left _ _
  have hR : 0 < R := htau.trans_le hRtau
  have hObs : 0 ≤ Obs := by dsimp [Obs, globalObservedRadius]; positivity
  have hU : 1 ≤ U := OriginalStatefulEnvelopeGD.uniform_minimum_factor_ge_one
    mu L rho R tau Obs hmu hL hrho.le htau hR.le hObs
  have hU0 : 0 ≤ U := zero_le_one.trans hU
  have hbase := actual_cubic_caller_from_original_inputs J mu L rho Delta Ry eps hmu hLmu hrho heps
    hC2 hLip hHess hsc hbelow start yin hgap hdual
  change run.1.success = true ∧ _ at hbase
  rcases hbase with ⟨htrue, hstationary, hcount, hcubes, hcost, htrace⟩
  have hrad : ∀ m ∈ run.1.moves, m.radius ≤ R := by
    intro m hm
    have hh := cubic_warm_radii_uniform_bound L mu tau (cubeBound mu L rho Delta eps) run.1.moves
      hcubes (fun m hm => (htrace m hm).2.1) m hm
    exact hh.trans (le_max_right _ _)
  have hlogs : ∀ m ∈ run.1.moves, OriginalStatefulEnvelopeGD.moveLog J mu L rho tau m ≤ U := by
    intro m hm
    obtain ⟨hlegal, _, hobs⟩ := htrace m hm
    have hD : 0 ≤ m.radius := (norm_nonneg _).trans hlegal
    have hobsR : OriginalDualResidualQueryBound.observedRadius J L m.next m.next m.warm ≤ Obs :=
      hobs.trans (by
        change 3 * (Real.sqrt (queryGap mu L rho Delta eps / L) + m.radius) ≤
          3 * (Real.sqrt (queryGap mu L rho Delta eps / L) + R)
        exact mul_le_mul_of_nonneg_left (add_le_add le_rfl (hrad m hm)) (by norm_num))
    exact (OriginalUniformMinimumWarmLog.actual_minimum_log_factor_uniform J mu L rho m.radius tau R Obs
      hmu hL hrho htau hD (hrad m hm) hRtau hC2 hLip hHess hsc m.next m.next m.warm hobsR).2
  have hMax := OriginalStatefulEnvelopeGD.maximum_log_le_of_all J mu L rho tau U hU run.1.moves hlogs
  have hinit := OriginalInitialSaddleRadius.actual_initial_dual_radius J L mu Delta Ry hL hmu hC2 hLip hsc hbelow start yin hgap hdual
  have hD0 : 0 ≤ D0 := (norm_nonneg _).trans hinit
  have hinitObs := OriginalInitialSaddleRadius.actual_initial_primal_residual J L mu Delta Ry hL hmu hC2 hLip hsc hbelow start yin hgap hdual
  have hSQ : Real.sqrt (Delta / L) ≤ Real.sqrt (queryGap mu L rho Delta eps / L) := by
    apply Real.sqrt_le_sqrt
    apply (div_le_div_iff_of_pos_right hL).mpr
    change Delta ≤ Delta + stepCharge M (eps / 2)
    linarith only [hcharge]
  have hinitObsR : OriginalDualResidualQueryBound.observedRadius J L start start yin ≤ Obs :=
    hinitObs.trans (by
      change 3 * (Real.sqrt (Delta / L) + D0) ≤
        3 * (Real.sqrt (queryGap mu L rho Delta eps / L) + R)
      exact mul_le_mul_of_nonneg_left (add_le_add hSQ hR0) (by norm_num))
  have hinitLog := (OriginalUniformMinimumWarmLog.actual_minimum_log_factor_uniform J mu L rho D0 tau R Obs
    hmu hL hrho htau hD0 hR0 hRtau hC2 hLip hHess hsc start start yin hinitObsR).2
  have hI0 : 0 ≤ OriginalStatefulEnvelopeGD.initializationPolynomial mu L rho Delta Ry := by
    dsimp [OriginalStatefulEnvelopeGD.initializationPolynomial]
    have hp : 0 ≤ rho * OriginalStatefulEnvelopeGD.initialRadius mu L Delta Ry / mu := by
      change 0 ≤ rho * D0 / mu
      positivity
    positivity
  have hinitCost : OriginalStatefulEnvelopeGD.initialCost J mu L rho D0 tau start yin ≤
      OriginalStatefulEnvelopeGD.initializationPolynomial mu L rho Delta Ry * U :=
    mul_le_mul_of_nonneg_left hinitLog hI0
  have htauSmall : rho * tau / mu ≤ 1 := by
    have ht : tau ≤ mu / rho :=
      (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
    have hh := mul_le_mul_of_nonneg_left ht (show 0 ≤ rho / mu by positivity)
    have he : (rho / mu) * (mu / rho) = 1 := by field_simp
    rw [he] at hh
    calc
      rho * tau / mu = (rho / mu) * tau := by ring
      _ ≤ 1 := hh
  have hfactor := OriginalBorelCubicSelectedRegime.terminal_cube_budget_factorization Delta M (eps / 2) hM (by positivity)
  have hcubesB : cubedMovement run.1.moves ≤ B * stepRadius M (eps / 2) ^ 3 := hcubes.trans_eq hfactor
  have hpoly := OriginalBorelCubicHolderNormalization.holder_with_terminal_budget
    (run.1.moves.length : ℝ) (cubedMovement run.1.moves) B (stepRadius M (eps / 2))
    (rho * tau / mu) (rho / mu * (2 * Real.sqrt (L / mu)))
    (by positivity) (cubed_movement_nonnegative _) hB hp.2.1 (by positivity) (by positivity)
    hcount hcubesB htauSmall
    (OriginalBorelCubicSelectedRegime.warm_coefficient_times_step_radius_le_one mu L rho eps hmu hLmu hrho heps hr)
  have hholder := actual_cubic_cost_sum_holder_bound J mu L rho tau hmu hL hrho.le htau.le run.1.moves
    (fun m hm => (htrace m hm).2.1)
  have hcostMoves : OriginalStatefulEnvelopeGD.costSum J mu L rho tau run.1.moves ≤ U * (3 * B) := by
    have hP0 : 0 ≤ cubicPolynomialBound mu L rho tau run.1.moves := by
      have hC0 := cubed_movement_nonnegative run.1.moves
      unfold cubicPolynomialBound
      positivity
    have h1 := mul_le_mul_of_nonneg_right hMax hP0
    have h2 := mul_le_mul_of_nonneg_left hpoly hU0
    exact hholder.trans (h1.trans h2)
  change (run.2 : ℝ) ≤ OriginalStatefulEnvelopeGD.initialCost J mu L rho D0 tau start yin +
    1 + OriginalStatefulEnvelopeGD.costSum J mu L rho tau run.1.moves + (run.1.moves.length : ℝ) at hcost
  refine ⟨hU,htrue,hstationary,?_⟩
  change (run.2 : ℝ) ≤ U * (OriginalStatefulEnvelopeGD.initializationPolynomial mu L rho Delta Ry + 1 + 4 * B)
  have hlen : (run.1.moves.length : ℝ) ≤ B := hcount
  have h1 := mul_nonneg (sub_nonneg.mpr hU) (show 0 ≤ 1 + B by positivity)
  nlinarith only [hcost,hinitCost,hcostMoves,hlen,h1]

end
end OriginalBorelStatefulEnvelopeCubic


namespace OriginalBorelCubicPaperRate
open _root_.OriginalBorelCubicPaperRate
noncomputable section
set_option maxHeartbeats 3000000

def A2 (mu L rho Delta eps : ℝ) :=
  Delta * Real.sqrt rho * (L / mu) ^ (3 / 4 : ℝ) / eps ^ (3 / 2 : ℝ)

theorem sqrt_curvature_upper (mu L rho : ℝ)
    (hmu : 0 < mu) (hLmu : mu ≤ L) (hrho : 0 < rho) :
    Real.sqrt (OriginalBorelStatefulEnvelopeCubic.curvature mu L rho) ≤
      8 * Real.sqrt rho * (L / mu) ^ (3 / 4 : ℝ) := by
  have hL : 0 < L := hmu.trans_le hLmu
  have hk : 1 ≤ L / mu := (le_div_iff₀ hmu).mpr (by simpa using hLmu)
  have hk0 : 0 ≤ L / mu := by positivity
  have ht : Real.sqrt ((1 + L / mu) ^ (3 / 2 : ℝ)) = (1 + L / mu) ^ (3 / 4 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (show 0 ≤ 1 + L / mu by positivity)]
    norm_num
  have hroot : Real.sqrt (OriginalBorelStatefulEnvelopeCubic.curvature mu L rho) =
      Real.sqrt 8 * Real.sqrt rho * (1 + L / mu) ^ (3 / 4 : ℝ) := by
    unfold OriginalBorelStatefulEnvelopeCubic.curvature
    rw [Real.sqrt_mul (show 0 ≤ 8 * rho by positivity),Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 8),ht]
  have hp := Real.rpow_le_rpow (show 0 ≤ 1 + L / mu by positivity)
    (show 1 + L / mu ≤ 2 * (L / mu) by linarith only [hk]) (by norm_num : (0 : ℝ) ≤ 3 / 4)
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hk0] at hp
  have h2 : (2 : ℝ) ^ (3 / 4 : ℝ) ≤ 2 := Real.rpow_le_self_of_one_le (by norm_num) (by norm_num)
  have h8 : Real.sqrt (8 : ℝ) ≤ 4 := by
    nlinarith only [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 8),Real.sqrt_nonneg (8 : ℝ)]
  rw [hroot]
  have h3 := mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg hk0 (3 / 4 : ℝ))
  have h4 := mul_le_mul h8 (hp.trans h3) (Real.rpow_nonneg (show 0 ≤ 1 + L / mu by positivity) _)
    (by norm_num : (0 : ℝ) ≤ 4)
  have h5 := mul_le_mul_of_nonneg_right h4 (Real.sqrt_nonneg rho)
  nlinarith only [h5]

theorem cubic_budget_le_paper_rate (mu L rho Delta eps : ℝ)
    (hmu : 0 < mu) (hLmu : mu ≤ L) (hrho : 0 < rho) (hDelta : 0 ≤ Delta) (heps : 0 < eps) :
    OriginalBorelStatefulEnvelopeCubic.cubicBudget mu L rho Delta eps ≤ 1 + 8192 * A2 mu L rho Delta eps := by
  have hL : 0 < L := hmu.trans_le hLmu
  let M := OriginalBorelStatefulEnvelopeCubic.curvature mu L rho
  have hM : 0 < M := by dsimp [M,OriginalBorelStatefulEnvelopeCubic.curvature]; positivity
  have hcharge := OriginalBorelOuterCubicSeparateErrors.reciprocal_charge_identity Delta M (eps / 2) hM (by positivity)
  have hsqrt := sqrt_curvature_upper mu L rho hmu hLmu hrho
  have hscale : eps ^ (3 / 2 : ℝ) ≤ 4 * (eps / 2) ^ (3 / 2 : ℝ) := by
    have hid : eps = 2 * (eps / 2) := by ring
    have hh : (2 : ℝ) ^ (3 / 2 : ℝ) ≤ 4 := by
      have ht := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
        (by norm_num : (3 / 2 : ℝ) ≤ 2)
      norm_num at ht
      exact ht
    calc
      _ = (2 : ℝ) ^ (3 / 2 : ℝ) * (eps / 2) ^ (3 / 2 : ℝ) := by
        rw [← Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (by positivity : 0 ≤ eps / 2)]
        congr 1
      _ ≤ _ := mul_le_mul_of_nonneg_right hh (by positivity)
  have hpow : 0 < eps ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos heps _
  have hhalf : 0 < (eps / 2) ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos (by positivity) _
  have hnum := mul_le_mul_of_nonneg_left hsqrt (show 0 ≤ 256 * Delta by positivity)
  have h1 := div_le_div_of_nonneg_right hnum hhalf.le
  have h2 : (2048 * Delta * Real.sqrt rho * (L / mu) ^ (3 / 4 : ℝ)) / (eps / 2) ^ (3 / 2 : ℝ) ≤
      8192 * A2 mu L rho Delta eps := by
    unfold A2
    rw [show 8192 * (Delta * Real.sqrt rho * (L / mu) ^ (3 / 4 : ℝ) / eps ^ (3 / 2 : ℝ)) =
      (8192 * Delta * Real.sqrt rho * (L / mu) ^ (3 / 4 : ℝ)) / eps ^ (3 / 2 : ℝ) by ring]
    apply (div_le_div_iff₀ hhalf hpow).mpr
    have hmul := mul_le_mul_of_nonneg_left hscale
      (show 0 ≤ 2048 * Delta * Real.sqrt rho * (L / mu) ^ (3 / 4 : ℝ) by positivity)
    nlinarith only [hmul]
  change 1 + Delta / OriginalBorelOuterCubicSeparateErrors.stepCharge M (eps / 2) ≤ _
  rw [hcharge]
  have h3 : 256 * Delta * Real.sqrt M / (eps / 2) ^ (3 / 2 : ℝ) ≤
      8192 * A2 mu L rho Delta eps := h1.trans (by convert! h2 using 1 <;> ring)
  linarith only [h3]

end
end OriginalBorelCubicPaperRate


namespace OriginalBorelMainUpperRates
open _root_.OriginalBorelMainUpperRates
noncomputable section
set_option maxHeartbeats 3000000

def cubic (mu L rho Delta eps : ℝ) :=
  OriginalBorelCubicPaperRate.A2 mu L rho Delta eps *
    (1 + OriginalGDRateNormalization.ratio mu L rho eps ^ (1 / 7 : ℝ))

def middle (mu L rho Delta eps : ℝ) :=
  OriginalGDRateNormalization.A1 Delta L eps *
    (1 + OriginalGDRateNormalization.ratio mu L rho eps ^ (2 / 7 : ℝ))

def first (mu L Delta eps : ℝ) :=
  Real.sqrt (L / mu) * OriginalGDRateNormalization.A1 Delta L eps

def frontier (mu L rho Delta eps : ℝ) :=
  min (cubic mu L rho Delta eps) (min (middle mu L rho Delta eps) (first mu L Delta eps))

theorem A2_eq_A1_sqrt_ratio (mu L rho Delta eps : ℝ)
    (hmu : 0 < mu) (hL : 0 < L) (hrho : 0 ≤ rho) (heps : 0 < eps) :
    OriginalBorelCubicPaperRate.A2 mu L rho Delta eps =
      OriginalGDRateNormalization.A1 Delta L eps * Real.sqrt (OriginalGDRateNormalization.ratio mu L rho eps) := by
  have hk : 0 ≤ L / mu := by positivity
  have hr : 0 ≤ OriginalGDRateNormalization.ratio mu L rho eps := by
    unfold OriginalGDRateNormalization.ratio
    positivity
  have hp : ((L / mu) ^ (3 / 4 : ℝ)) ^ 2 = (L / mu) ^ (3 / 2 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hk]
    norm_num
  let c := Real.sqrt rho * (L / mu) ^ (3 / 4 : ℝ) * Real.sqrt eps / L
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hcsq : c ^ 2 = OriginalGDRateNormalization.ratio mu L rho eps := by
    dsimp only [c]
    rw [div_pow,mul_pow,mul_pow,Real.sq_sqrt hrho,Real.sq_sqrt heps.le,hp,
      OriginalGDRateNormalization.ratio_eq_paper mu L rho eps hmu hL]
  have hroot : Real.sqrt (OriginalGDRateNormalization.ratio mu L rho eps) = c := by
    nlinarith only [Real.sq_sqrt hr,Real.sqrt_nonneg (OriginalGDRateNormalization.ratio mu L rho eps),hcsq,hc]
  have hepow : eps ^ (3 / 2 : ℝ) = eps * Real.sqrt eps := by
    calc
      _ = eps ^ (1 + 1 / 2 : ℝ) := by congr 1 <;> ring
      _ = _ := by rw [Real.rpow_add heps,Real.rpow_one,← Real.sqrt_eq_rpow]
  rw [hroot]
  unfold OriginalBorelCubicPaperRate.A2 OriginalGDRateNormalization.A1 c
  rw [hepow]
  field_simp
  <;> rw [Real.sq_sqrt heps.le]
  <;> ring

theorem A2_le_all_rates_in_small_regime (mu L rho Delta eps : ℝ)
    (hmu : 0 < mu) (hLmu : mu ≤ L) (hrho : 0 ≤ rho) (hDelta : 0 ≤ Delta) (heps : 0 < eps)
    (hr : OriginalGDRateNormalization.ratio mu L rho eps ≤ 1) :
    OriginalBorelCubicPaperRate.A2 mu L rho Delta eps ≤ frontier mu L rho Delta eps := by
  have hL : 0 < L := hmu.trans_le hLmu
  have ha1 : 0 ≤ OriginalGDRateNormalization.A1 Delta L eps := by unfold OriginalGDRateNormalization.A1; positivity
  have ha2 : 0 ≤ OriginalBorelCubicPaperRate.A2 mu L rho Delta eps := by unfold OriginalBorelCubicPaperRate.A2; positivity
  have hr0 : 0 ≤ OriginalGDRateNormalization.ratio mu L rho eps := by unfold OriginalGDRateNormalization.ratio; positivity
  have hsqrt : Real.sqrt (OriginalGDRateNormalization.ratio mu L rho eps) ≤ 1 := by
    have hh := Real.sqrt_le_sqrt hr
    simpa using hh
  have hk : 1 ≤ Real.sqrt (L / mu) := by
    have hh := Real.sqrt_le_sqrt ((le_div_iff₀ hmu).mpr (by simpa using hLmu) : 1 ≤ L / mu)
    simpa using hh
  have hA2 : OriginalBorelCubicPaperRate.A2 mu L rho Delta eps ≤ OriginalGDRateNormalization.A1 Delta L eps := by
    rw [A2_eq_A1_sqrt_ratio mu L rho Delta eps hmu hL hrho heps]
    nlinarith only [mul_le_mul_of_nonneg_left hsqrt ha1]
  unfold frontier
  refine le_min ?_ (le_min ?_ ?_)
  · unfold cubic
    have hh := mul_nonneg ha2 (Real.rpow_nonneg hr0 (1 / 7 : ℝ))
    nlinarith only [hh]
  · unfold middle
    have hh := mul_nonneg ha1 (Real.rpow_nonneg hr0 (2 / 7 : ℝ))
    nlinarith only [hh,hA2]
  · unfold first
    have hh := mul_nonneg ha1 (sub_nonneg.mpr hk)
    nlinarith only [hh,hA2]

theorem middle_le_twice_cubic_in_large_regime (mu L rho Delta eps : ℝ)
    (hmu : 0 < mu) (hL : 0 < L) (hrho : 0 ≤ rho) (hDelta : 0 ≤ Delta) (heps : 0 < eps)
    (hr : 1 ≤ OriginalGDRateNormalization.ratio mu L rho eps) :
    middle mu L rho Delta eps ≤ 2 * cubic mu L rho Delta eps := by
  let r := OriginalGDRateNormalization.ratio mu L rho eps
  have ha1 : 0 ≤ OriginalGDRateNormalization.A1 Delta L eps := by unfold OriginalGDRateNormalization.A1; positivity
  have ha2 : 0 ≤ OriginalBorelCubicPaperRate.A2 mu L rho Delta eps := by unfold OriginalBorelCubicPaperRate.A2; positivity
  have hr0 : 0 ≤ r := zero_le_one.trans hr
  have hpow : r ^ (2 / 7 : ℝ) ≤ Real.sqrt r := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hr (by norm_num)
  have hsqrt : 1 ≤ Real.sqrt r := by
    have hh := Real.sqrt_le_sqrt hr
    simpa using hh
  have hA2 := A2_eq_A1_sqrt_ratio mu L rho Delta eps hmu hL hrho heps
  change OriginalBorelCubicPaperRate.A2 mu L rho Delta eps = OriginalGDRateNormalization.A1 Delta L eps * Real.sqrt r at hA2
  have h1 := mul_le_mul_of_nonneg_left (show 1 + r ^ (2 / 7 : ℝ) ≤ 2 * Real.sqrt r by linarith only [hpow,hsqrt]) ha1
  have h2 := mul_nonneg ha2 (Real.rpow_nonneg hr0 (1 / 7 : ℝ))
  unfold middle cubic
  change OriginalGDRateNormalization.A1 Delta L eps * (1 + r ^ (2 / 7 : ℝ)) ≤
    2 * (OriginalBorelCubicPaperRate.A2 mu L rho Delta eps * (1 + r ^ (1 / 7 : ℝ)))
  nlinarith only [h1,h2,hA2]

end
end OriginalBorelMainUpperRates


namespace OriginalBorelActualMainUpper
open _root_.OriginalBorelActualMainUpper

open OriginalSaddleImplicit OriginalSaddleTransfer OriginalSaddleStability
open OriginalBetaATSTrial FangqingGetterComposition

noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 6000

universe u
variable {E F : Type u}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

def positiveProgram (mu L rho Delta Ry eps : ℝ) (start : E) (yin : F) :
    GetterProgram (Joint E F) (OriginalDualOracleProgram.OracleAnswer (Joint E F)) E :=
  if OriginalGDRateNormalization.ratio mu L rho eps ≤ 1 then
    map (fun out : OriginalBorelStatefulEnvelopeCubic.Result E F => out.saddle.fst)
      (OriginalBorelStatefulEnvelopeCubic.caller mu L rho Delta Ry eps start yin)
  else
    map (fun out : OriginalStatefulEnvelopeGD.Result E F => out.saddle.fst)
      (OriginalStatefulEnvelopeGD.caller mu L rho Delta Ry eps start yin)

def positiveLogFactor (mu L rho Delta Ry eps : ℝ) :=
  max (OriginalStatefulEnvelopeGD.globalLogFactor mu L rho Delta Ry eps)
    (OriginalBorelStatefulEnvelopeCubic.globalLogFactor mu L rho Delta Ry eps)

def program (mu L rho Delta Ry eps : ℝ) (start : E) (yin : F) :
    GetterProgram (Joint E F) (OriginalDualOracleProgram.OracleAnswer (Joint E F)) E :=
  if rho = 0 then OriginalZeroHessianReconstruction.program mu L Delta Ry eps start yin
  else positiveProgram mu L rho Delta Ry eps start yin

def logarithmicFactor (mu L rho Delta Ry eps : ℝ) :=
  if rho = 0 then 1 else positiveLogFactor mu L rho Delta Ry eps

theorem scalar_cost_domination (T u U I R c : ℝ)
    (hT : T ≤ u * (I + c * R)) (hu : u ≤ U) (hU : 0 ≤ U)
    (hI : 0 ≤ I) (hR : 0 ≤ R) (hc : 0 ≤ c) (hcmax : c ≤ 32768) :
    T ≤ 32768 * U * (I + R) := by
  have h1 := mul_le_mul_of_nonneg_right hu (show 0 ≤ I + c * R by positivity)
  have h2 := mul_nonneg hU (show 0 ≤ (32768 - c) * R by positivity)
  have h3 := mul_nonneg hU hI
  nlinarith only [hT,h1,h2,h3]

theorem cost_le_frontier_of_three_bounds (T K I mu L rho Delta eps : ℝ)
    (hc : T ≤ K * (I + OriginalBorelMainUpperRates.cubic mu L rho Delta eps))
    (hm : T ≤ K * (I + OriginalBorelMainUpperRates.middle mu L rho Delta eps))
    (hf : T ≤ K * (I + OriginalBorelMainUpperRates.first mu L Delta eps)) :
    T ≤ K * (I + OriginalBorelMainUpperRates.frontier mu L rho Delta eps) := by
  unfold OriginalBorelMainUpperRates.frontier
  by_cases h : OriginalBorelMainUpperRates.cubic mu L rho Delta eps ≤
      min (OriginalBorelMainUpperRates.middle mu L rho Delta eps) (OriginalBorelMainUpperRates.first mu L Delta eps)
  · rw [min_eq_left h]
    exact hc
  · rw [min_eq_right (le_of_not_ge h)]
    by_cases hm' : OriginalBorelMainUpperRates.middle mu L rho Delta eps ≤ OriginalBorelMainUpperRates.first mu L Delta eps
    · rw [min_eq_left hm']
      exact hm
    · rw [min_eq_right (le_of_not_ge hm')]
      exact hf

theorem positive_main_upper
    (J : Joint E F → ℝ) (mu L rho Delta Ry eps : ℝ)
    (hmu : 0 < mu) (hLmu : mu ≤ L) (hrho : 0 < rho) (heps : 0 < eps)
    (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (hHess : ∀ z w : Joint E F, ‖fderiv ℝ (gradient J) z - fderiv ℝ (gradient J) w‖ ≤ rho * ‖z - w‖)
    (hsc : ∀ u : E, StrongConvexOn (Set.univ : Set F) mu (fun y => -JointSliceRegularity.curry J u y))
    (hbelow : BddBelow (Set.range (phi (JointSliceRegularity.curry J))))
    (start : E) (yin : F)
    (hgap : phi (JointSliceRegularity.curry J) start - sInf (Set.range (phi (JointSliceRegularity.curry J))) ≤ Delta)
    (hdual : ‖yin - yStar (JointSliceRegularity.curry J) start‖ ≤ Ry) :
    let run := execute (OriginalDualOracleProgram.actualOracle J) (positiveProgram mu L rho Delta Ry eps start yin)
    let U := positiveLogFactor mu L rho Delta Ry eps
    1 ≤ U ∧ ‖gradient (phi (JointSliceRegularity.curry J)) run.1‖ ≤ eps ∧
    (run.2 : ℝ) ≤ 32768 * U *
      (OriginalStatefulEnvelopeGD.initializationPolynomial mu L rho Delta Ry +
        OriginalBorelMainUpperRates.frontier mu L rho Delta eps) := by
  let U := positiveLogFactor mu L rho Delta Ry eps
  let Ug := OriginalStatefulEnvelopeGD.globalLogFactor mu L rho Delta Ry eps
  let Uc := OriginalBorelStatefulEnvelopeCubic.globalLogFactor mu L rho Delta Ry eps
  let I := OriginalStatefulEnvelopeGD.initializationPolynomial mu L rho Delta Ry
  have hL : 0 < L := hmu.trans_le hLmu
  have hDelta : 0 ≤ Delta := by
    have hi := csInf_le hbelow (Set.mem_range_self start)
    linarith only [hgap,hi]
  have hD0 : 0 ≤ OriginalStatefulEnvelopeGD.initialRadius mu L Delta Ry := by
    have hh := OriginalInitialSaddleRadius.actual_initial_dual_radius J L mu Delta Ry hL hmu hC2 hLip hsc hbelow start yin hgap hdual
    exact (norm_nonneg _).trans hh
  have hI : 1 ≤ I := by
    change 1 ≤ 1 + min (Real.sqrt (L / mu))
      ((rho * OriginalStatefulEnvelopeGD.initialRadius mu L Delta Ry / mu) ^ (2 / 7 : ℝ))
    exact le_add_of_nonneg_right (le_min (Real.sqrt_nonneg _) (Real.rpow_nonneg (by positivity) _))
  have hUgU : Ug ≤ U := le_max_left _ _
  have hUcU : Uc ≤ U := le_max_right _ _
  have hgd := OriginalStatefulEnvelopeGD.actual_uniform_gradient_main_branches J mu L rho Delta Ry eps
    hmu hLmu hrho heps hC2 hLip hHess hsc hbelow start yin hgap hdual
  have hUg : 1 ≤ Ug := hgd.1
  have hU : 1 ≤ U := hUg.trans hUgU
  have hU0 : 0 ≤ U := zero_le_one.trans hU
  by_cases hr : OriginalGDRateNormalization.ratio mu L rho eps ≤ 1
  · have hc := OriginalBorelStatefulEnvelopeCubic.actual_uniform_cubic_selected_branch J mu L rho Delta Ry eps
      hmu hLmu hrho heps hr hC2 hLip hHess hsc hbelow start yin hgap hdual
    simp only [positiveProgram,if_pos hr,execute_map]
    refine ⟨hU,hc.2.2.1,?_⟩
    change ((execute (OriginalDualOracleProgram.actualOracle J)
      (OriginalBorelStatefulEnvelopeCubic.caller mu L rho Delta Ry eps start yin)).2 : ℝ) ≤
      32768 * U * (I + OriginalBorelMainUpperRates.frontier mu L rho Delta eps)
    have hB := OriginalBorelCubicPaperRate.cubic_budget_le_paper_rate mu L rho Delta eps hmu hLmu hrho hDelta heps
    have hA2 := OriginalBorelMainUpperRates.A2_le_all_rates_in_small_regime mu L rho Delta eps hmu hLmu hrho.le hDelta heps hr
    have hraw : 0 ≤ I + 1 + 4 * OriginalBorelStatefulEnvelopeCubic.cubicBudget mu L rho Delta eps := by
      have hM : 0 < OriginalBorelStatefulEnvelopeCubic.curvature mu L rho := by
        unfold OriginalBorelStatefulEnvelopeCubic.curvature
        positivity
      have hcharge := (OriginalBorelOuterCubicSeparateErrors.radius_properties
        (OriginalBorelStatefulEnvelopeCubic.curvature mu L rho) (eps / 2) hM (by positivity)).2.2.2
      unfold OriginalBorelStatefulEnvelopeCubic.cubicBudget
      positivity
    have h1 := mul_le_mul_of_nonneg_right hUcU hraw
    have h2 := mul_le_mul_of_nonneg_left
      (show I + 1 + 4 * OriginalBorelStatefulEnvelopeCubic.cubicBudget mu L rho Delta eps ≤
        32768 * (I + OriginalBorelMainUpperRates.frontier mu L rho Delta eps) by nlinarith only [hB,hA2,hI]) hU0
    have hcCost := hc.2.2.2
    change ((execute (OriginalDualOracleProgram.actualOracle J)
      (OriginalBorelStatefulEnvelopeCubic.caller mu L rho Delta Ry eps start yin)).2 : ℝ) ≤
      Uc * (I + 1 + 4 * OriginalBorelStatefulEnvelopeCubic.cubicBudget mu L rho Delta eps) at hcCost
    nlinarith only [hcCost,h1,h2]
  · simp only [positiveProgram,if_neg hr,execute_map]
    refine ⟨hU,hgd.2.2.1,?_⟩
    let T := ((execute (OriginalDualOracleProgram.actualOracle J)
      (OriginalStatefulEnvelopeGD.caller mu L rho Delta Ry eps start yin)).2 : ℝ)
    have hmiddle : T ≤ Ug * (I + 512 * OriginalBorelMainUpperRates.middle mu L rho Delta eps) := by
      convert! hgd.2.2.2.1 using 1 <;> unfold OriginalBorelMainUpperRates.middle <;> ring
    have hfirst : T ≤ Ug * (I + 256 * OriginalBorelMainUpperRates.first mu L Delta eps) := by
      convert! hgd.2.2.2.2 using 1 <;> unfold OriginalBorelMainUpperRates.first <;> ring
    have hmid0 : 0 ≤ OriginalBorelMainUpperRates.middle mu L rho Delta eps := by
      unfold OriginalBorelMainUpperRates.middle OriginalGDRateNormalization.A1 OriginalGDRateNormalization.ratio
      positivity
    have hfirst0 : 0 ≤ OriginalBorelMainUpperRates.first mu L Delta eps := by
      unfold OriginalBorelMainUpperRates.first OriginalGDRateNormalization.A1
      positivity
    have hcub0 : 0 ≤ OriginalBorelMainUpperRates.cubic mu L rho Delta eps := by
      unfold OriginalBorelMainUpperRates.cubic OriginalBorelCubicPaperRate.A2 OriginalGDRateNormalization.ratio
      positivity
    have hcomp := OriginalBorelMainUpperRates.middle_le_twice_cubic_in_large_regime mu L rho Delta eps hmu hL hrho.le hDelta heps (le_of_not_ge hr)
    have h1 : T ≤ Ug * (I + 1024 * OriginalBorelMainUpperRates.cubic mu L rho Delta eps) := by
      have hh := mul_le_mul_of_nonneg_left hcomp (show 0 ≤ 512 * Ug by positivity)
      nlinarith only [hmiddle,hh]
    have hc := scalar_cost_domination T Ug U I (OriginalBorelMainUpperRates.cubic mu L rho Delta eps) 1024
      h1 hUgU hU0 (zero_le_one.trans hI) hcub0 (by norm_num) (by norm_num)
    have hm := scalar_cost_domination T Ug U I (OriginalBorelMainUpperRates.middle mu L rho Delta eps) 512
      hmiddle hUgU hU0 (zero_le_one.trans hI) hmid0 (by norm_num) (by norm_num)
    have hf := scalar_cost_domination T Ug U I (OriginalBorelMainUpperRates.first mu L Delta eps) 256
      hfirst hUgU hU0 (zero_le_one.trans hI) hfirst0 (by norm_num) (by norm_num)
    exact cost_le_frontier_of_three_bounds T (32768 * U) I mu L rho Delta eps hc hm hf

/-- Full actual original-oracle upper program: rho=0 reconstructs the whole
quadratic from one bundle; rho>0 selects cubic/GD using only known parameters.
The original theorem's randomized lower bound is a separate obligation. -/
theorem main_upper_from_original_standing_inputs
    (J : Joint E F → ℝ) (mu L rho Delta Ry eps : ℝ)
    (hmu : 0 < mu) (hLmu : mu ≤ L) (hrho : 0 ≤ rho) (heps : 0 < eps)
    (hC2 : ContDiff ℝ 2 J)
    (hLip : ∀ z w : Joint E F, ‖gradient J z - gradient J w‖ ≤ L * ‖z - w‖)
    (hHess : ∀ z w : Joint E F, ‖fderiv ℝ (gradient J) z - fderiv ℝ (gradient J) w‖ ≤ rho * ‖z - w‖)
    (hsc : ∀ u : E, StrongConvexOn (Set.univ : Set F) mu (fun y => -JointSliceRegularity.curry J u y))
    (hbelow : BddBelow (Set.range (phi (JointSliceRegularity.curry J))))
    (start : E) (yin : F)
    (hgap : phi (JointSliceRegularity.curry J) start - sInf (Set.range (phi (JointSliceRegularity.curry J))) ≤ Delta)
    (hdual : ‖yin - yStar (JointSliceRegularity.curry J) start‖ ≤ Ry) :
    let run := execute (OriginalDualOracleProgram.actualOracle J) (program mu L rho Delta Ry eps start yin)
    let U := logarithmicFactor mu L rho Delta Ry eps
    1 ≤ U ∧ ‖gradient (phi (JointSliceRegularity.curry J)) run.1‖ ≤ eps ∧
    (run.2 : ℝ) ≤ 32768 * U *
      (OriginalStatefulEnvelopeGD.initializationPolynomial mu L rho Delta Ry +
        OriginalBorelMainUpperRates.frontier mu L rho Delta eps) := by
  by_cases hzero : rho = 0
  · subst rho
    have hh := OriginalZeroHessianReconstruction.one_original_query_suffices_when_hessian_is_constant
      J mu L Delta Ry eps hmu hLmu heps hC2 hLip hHess hsc hbelow start yin hgap hdual
    simp only [program,logarithmicFactor,if_pos rfl,ite_true]
    refine ⟨le_refl _,hh.2,?_⟩
    rw [hh.1]
    have hDelta : 0 ≤ Delta := by
      have hi := csInf_le hbelow (Set.mem_range_self start)
      linarith only [hgap,hi]
    have hL : 0 < L := hmu.trans_le hLmu
    have hF : 0 ≤ OriginalBorelMainUpperRates.frontier mu L 0 Delta eps := by
      unfold OriginalBorelMainUpperRates.frontier OriginalBorelMainUpperRates.cubic OriginalBorelMainUpperRates.middle
        OriginalBorelMainUpperRates.first OriginalBorelCubicPaperRate.A2 OriginalGDRateNormalization.A1 OriginalGDRateNormalization.ratio
      positivity
    have hI : 1 ≤ OriginalStatefulEnvelopeGD.initializationPolynomial mu L 0 Delta Ry := by
      unfold OriginalStatefulEnvelopeGD.initializationPolynomial
      simp only [zero_mul,zero_div,Real.zero_rpow (by norm_num : (2 / 7 : ℝ) ≠ 0)]
      exact le_add_of_nonneg_right (le_min (Real.sqrt_nonneg _) le_rfl)
    norm_num only [Nat.cast_one,mul_one]
    nlinarith only [hF,hI]
  · have hpos : 0 < rho := lt_of_le_of_ne hrho (Ne.symm hzero)
    simp only [program,logarithmicFactor,if_neg hzero]
    exact positive_main_upper J mu L rho Delta Ry eps hmu hLmu hpos heps hC2 hLip hHess hsc hbelow start yin hgap hdual

end
end OriginalBorelActualMainUpper


end OriginalAdmissibleMainReplay
end
