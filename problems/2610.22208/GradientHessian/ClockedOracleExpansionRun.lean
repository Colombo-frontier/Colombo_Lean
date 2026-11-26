import GradientHessian.ClockedOracleExpansion

/-! Exact simulation of every rich instruction by its actual ordinary
reply batch. No oracle-agreement premise is assumed. -/

noncomputable section
namespace GradientHessian.ClockedOracle
open MeasureTheory

variable {Seed W X Y Z : Type*} [MeasurableSpace Seed] [MeasurableSpace W]
  [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z] {r : ℕ}
variable (p : Program Seed W X Y Z) (b : Batch X Y Z r) (ordinary : X → Y) (unusedRich : X → Z)

theorem Program.expanded_query_step (i j : ℕ) (hk : p.kind i=2) (hj : j<r)
    (w : W) (c : Fin r → Y) :
    (p.expand b).advance ordinary unusedRich (i*(r+1)+j) (w,c)=
      (w,Function.update c ⟨j,hj⟩ (ordinary (b.query ⟨j,hj⟩ (p.point i w)))) := by
  have hjs : j<r+1 := by omega
  simp [advance,expand,expandedKind,expandedPoint,expandedOrdinary,
    batchIndex_clock r i j hjs,batchSlot_clock r i j hjs,hk,hj]

theorem Program.expanded_deliver_step (i : ℕ) (hk : p.kind i=2) (w : W) (c : Fin r → Y) :
    (p.expand b).advance ordinary unusedRich (i*(r+1)+r) (w,c)=
      (p.richNext i (w,b.decode (p.point i w,c)),c) := by
  simp [advance,expand,expandedKind,expandedThink,
    batchIndex_clock r i r (by omega),batchSlot_clock r i r (by omega),hk]

theorem Program.expanded_first_step (i : ℕ) (hk : p.kind i≠2) (w : W) (c : Fin r → Y) :
    (p.expand b).advance ordinary unusedRich (i*(r+1)) (w,c)=
      (p.advance ordinary (b.oracle ordinary) i w,c) := by
  have hi := batchIndex_clock r i 0 (by omega)
  have hs := batchSlot_clock r i 0 (by omega)
  simp only [Nat.add_zero] at hi hs
  generalize he : p.kind i=k at *
  fin_cases k <;> simp_all [advance,expand,expandedKind,expandedThink,expandedPoint,expandedOrdinary]

theorem Program.expanded_idle_step (i j : ℕ) (hk : p.kind i≠2) (hj : 0<j) (hjs : j<r+1)
    (w : W) (c : Fin r → Y) :
    (p.expand b).advance ordinary unusedRich (i*(r+1)+j) (w,c)=(w,c) := by
  simp [advance,expand,expandedKind,expandedThink,
    batchIndex_clock r i j hjs,batchSlot_clock r i j hjs,hk,Nat.ne_of_gt hj]

theorem Program.expanded_nonrich_segment (i j : ℕ) (hk : p.kind i≠2) (hj : 0<j) (hjs : j≤r+1)
    (w : W) (c : Fin r → Y) :
    (p.expand b).segment ordinary unusedRich (i*(r+1)) j (w,c)=
      (p.advance ordinary (b.oracle ordinary) i w,c) := by
  induction j with
  | zero => omega
  | succ j ih =>
    by_cases hz : j=0
    · subst j
      change (p.expand b).advance ordinary unusedRich (i*(r+1)+0) (w,c)=_
      rw [Nat.add_zero]
      exact p.expanded_first_step b ordinary unusedRich i hk w c
    · change (p.expand b).advance ordinary unusedRich (i*(r+1)+j)
        ((p.expand b).segment ordinary unusedRich (i*(r+1)) j (w,c))=_
      rw [ih (by omega) (by omega)]
      exact p.expanded_idle_step b ordinary unusedRich i j hk (by omega) (by omega) _ c

theorem Program.expanded_rich_prefix (i j : ℕ) (hk : p.kind i=2) (hjs : j≤r)
    (w : W) (c : Fin r → Y) :
    (p.expand b).segment ordinary unusedRich (i*(r+1)) j (w,c)=
      (w,fun a => if a.val<j then ordinary (b.query a (p.point i w)) else c a) := by
  induction j with
  | zero => simp [segment]
  | succ j ih =>
    change (p.expand b).advance ordinary unusedRich (i*(r+1)+j)
      ((p.expand b).segment ordinary unusedRich (i*(r+1)) j (w,c))=_
    rw [ih (by omega),p.expanded_query_step b ordinary unusedRich i j hk (by omega)]
    apply Prod.ext
    · rfl
    funext a
    dsimp only [Prod.snd]
    by_cases ha : a=⟨j,by omega⟩
    · subst a
      simp
    · have hval : a.val≠j := by intro hv; exact ha (Fin.ext hv)
      rw [Function.update_of_ne ha]
      have he : a.val<j+1 ↔ a.val<j := by omega
      simp only [he]

theorem Program.expanded_rich_segment (i : ℕ) (hk : p.kind i=2) (w : W) (c : Fin r → Y) :
    (p.expand b).segment ordinary unusedRich (i*(r+1)) (r+1) (w,c)=
      (p.advance ordinary (b.oracle ordinary) i w,fun a => ordinary (b.query a (p.point i w))) := by
  change (p.expand b).advance ordinary unusedRich (i*(r+1)+r)
    ((p.expand b).segment ordinary unusedRich (i*(r+1)) r (w,c))=_
  rw [p.expanded_rich_prefix b ordinary unusedRich i r hk le_rfl]
  have he : (fun a : Fin r => if a.val<r then ordinary (b.query a (p.point i w)) else c a)=
      (fun a => ordinary (b.query a (p.point i w))) := by funext a; simp only [a.isLt,if_true]
  rw [he,p.expanded_deliver_step b ordinary unusedRich i hk]
  simp [advance,hk,Batch.oracle]

theorem Program.expanded_segment_projection (i : ℕ) (s : W × (Fin r → Y)) :
    ((p.expand b).segment ordinary unusedRich (i*(r+1)) (r+1) s).1=
      p.advance ordinary (b.oracle ordinary) i s.1 := by
  rcases s with ⟨w,c⟩
  by_cases hk : p.kind i=2
  · rw [p.expanded_rich_segment b ordinary unusedRich i hk]
  · rw [p.expanded_nonrich_segment b ordinary unusedRich i (r+1) hk (by omega) le_rfl]

theorem Program.expanded_evaluate_projection (i : ℕ) (seed : Seed) :
    ((p.expand b).evaluate ordinary unusedRich (i*(r+1)) seed).1=
      p.evaluate ordinary (b.oracle ordinary) i seed := by
  induction i with
  | zero => rw [Nat.zero_mul]; rfl
  | succ i ih =>
    rw [Nat.succ_mul,(p.expand b).evaluate_add]
    rw [p.expanded_segment_projection b ordinary unusedRich]
    rw [ih]
    rfl

theorem Program.expanded_output (seed : Seed) :
    (p.expand b).policy.output
      ((p.expand b).policy.run ordinary unusedRich (p.length*(r+1)) seed)=
        p.policy.output (p.policy.run ordinary (b.oracle ordinary) p.length seed) := by
  change (p.expand b).policy.output ((p.expand b).policy.run ordinary unusedRich (p.expand b).length seed)=_
  rw [(p.expand b).output_final ordinary unusedRich seed,p.output_final ordinary (b.oracle ordinary) seed]
  change p.output (((p.expand b).evaluate ordinary unusedRich (p.length*(r+1)) seed).1)=_
  rw [p.expanded_evaluate_projection b ordinary unusedRich]

end GradientHessian.ClockedOracle
