import Bilevel.OracleMachineRun

/-! Pathwise, exact-call compilation of sequential composition, including
the case where either component returns without an original oracle call. -/
noncomputable section
namespace Bilevel.OracleCode.Machine
open BorelAdaptive
variable {Q O A B C : Space}

theorem bind_correct (p : Machine Q O A B) (q : Machine Q O (prod A B) C)
    (cp : Code Q O A B) (cq : Code Q O (prod A B) C)
    (hp : Correct p cp) (hq : Correct q cq) : Correct (bind p q) (.bind cp cq) := by
  intro Seed response s a
  let u := eval response cp (a,s)
  let v := eval response cq ((a,u.1.1),u.2)
  have hP := hp Seed response s a
  have hQ := hq Seed response u.2 (a,u.1.1)
  change p.program.halt (execute p response s a u.1.2.2)=true ∧
    (∀ n<u.1.2.2,p.program.halt (execute p response s a n)=false) ∧
    p.program.output (execute p response s a u.1.2.2)=u.1.1 at hP
  change q.program.halt (execute q response u.2 (a,u.1.1) v.1.2.2)=true ∧
    (∀ n<v.1.2.2,q.program.halt (execute q response u.2 (a,u.1.1) n)=false) ∧
    q.program.output (execute q response u.2 (a,u.1.1) v.1.2.2)=v.1.1 at hQ
  have hswitch : execute (bind p q) response s a u.1.2.2=Sum.inr (q.start (a,u.1.1)) := by
    rw [bind_run_first p q response s a u.1.2.2 hP.2.1 _ le_rfl]
    simp only [enter,hP.1,if_true,hP.2.2]
  have hafter (k : ℕ) : execute (bind p q) response s a (u.1.2.2+k)=
      Sum.inr (execute q response u.2 (a,u.1.1) k) := by
    change run (bind p q).program _ () s ((bind p q).start a) (u.1.2.2+k)=_
    rw [run_add]
    change run (bind p q).program _ () (fun j => s (u.1.2.2+j))
      (execute (bind p q) response s a u.1.2.2) k=_
    rw [hswitch,bind_run_inr]
    congr 1
    change _=run q.program _ () (eval response cp (a,s)).2 (q.start (a,u.1.1)) k
    rw [eval_suffix]
  change (bind p q).program.halt (execute (bind p q) response s a (u.1.2.2+v.1.2.2))=true ∧
    (∀ n<u.1.2.2+v.1.2.2,(bind p q).program.halt (execute (bind p q) response s a n)=false) ∧
    (bind p q).program.output (execute (bind p q) response s a (u.1.2.2+v.1.2.2))=v.1.1
  refine ⟨?_,?_,?_⟩
  · rw [hafter]
    exact hQ.1
  · intro n hn
    by_cases hp' : n<u.1.2.2
    · rw [bind_run_first p q response s a u.1.2.2 hP.2.1 n hp'.le]
      simp only [enter,hP.2.1 n hp',Bool.false_eq_true,if_false,bind,Sum.elim_inl]
    · have hle : u.1.2.2≤n := Nat.le_of_not_gt hp'
      have he : u.1.2.2+(n-u.1.2.2)=n := Nat.add_sub_of_le hle
      rw [← he,hafter]
      exact hQ.2.1 _ (by omega)
  · rw [hafter]
    exact hQ.2.2

end Bilevel.OracleCode.Machine
