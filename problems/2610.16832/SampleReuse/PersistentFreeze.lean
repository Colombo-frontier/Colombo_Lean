import SampleReuse.OracleFreeze
import SampleReuse.PersistentHandleNormalization

open SecondOrder
open scoped Classical
namespace SampleReuse
noncomputable section
variable {Q H Y O S Z : Type}

theorem freezeOracle_lazy_before (P : OracleAlgorithm (Q × H) Y O S)
    (stop : ℕ → S → Bool) (idle : Q × H) (reply : Q → Z → Y) (tape : ℕ → Z) : ∀ n,
    (∀ k < n, stop k (lazyPersistentRun P.toQueryPolicy reply tape k).1 = false) →
    lazyPersistentRun (freezeOracle P stop idle).toQueryPolicy reply tape n =
      (((lazyPersistentRun P.toQueryPolicy reply tape n).1,
        stop n (lazyPersistentRun P.toQueryPolicy reply tape n).1,
        P.output n (lazyPersistentRun P.toQueryPolicy reply tape n).1),
        (lazyPersistentRun P.toQueryPolicy reply tape n).2) := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
    intro hs
    have hh := ih (fun k hk => hs k (by omega))
    simp only [lazyPersistentRun]
    rw [hh]
    simp only [freezeOracle,hs n (by omega),Bool.false_eq_true,if_false]

theorem freezeOracle_lazy_stable (P : OracleAlgorithm (Q × H) Y O S)
    (stop : ℕ → S → Bool) (idle : Q × H) (reply : Q → Z → Y) (tape : ℕ → Z) {k : ℕ}
    (hk : (lazyPersistentRun (freezeOracle P stop idle).toQueryPolicy reply tape k).1.2.1 = true) :
    ∀ n, k ≤ n → (lazyPersistentRun (freezeOracle P stop idle).toQueryPolicy reply tape n).1 =
      (lazyPersistentRun (freezeOracle P stop idle).toQueryPolicy reply tape k).1 := by
  intro n hn
  obtain ⟨r,rfl⟩ := Nat.exists_eq_add_of_le hn
  clear hn
  induction r with
  | zero => rfl
  | succ r ih =>
    change (freezeOracle P stop idle).update (k+r)
      (lazyPersistentRun (freezeOracle P stop idle).toQueryPolicy reply tape (k+r)).1
      (reply ((freezeOracle P stop idle).query (k+r)
          (lazyPersistentRun (freezeOracle P stop idle).toQueryPolicy reply tape (k+r)).1).1
        (tape ((lazyPersistentRun (freezeOracle P stop idle).toQueryPolicy reply tape (k+r)).2.idxOf
          ((freezeOracle P stop idle).query (k+r)
            (lazyPersistentRun (freezeOracle P stop idle).toQueryPolicy reply tape (k+r)).1).2))) = _
    rw [ih]
    exact if_pos hk

theorem freezeOracle_lazy_first_stop (P : OracleAlgorithm (Q × H) Y O S)
    (stop : ℕ → S → Bool) (idle : Q × H) (reply : Q → Z → Y) (tape : ℕ → Z) {k n : ℕ}
    (hkn : k ≤ n) (hk : stop k (lazyPersistentRun P.toQueryPolicy reply tape k).1 = true)
    (hbefore : ∀ j < k, stop j (lazyPersistentRun P.toQueryPolicy reply tape j).1 = false) :
    (lazyPersistentRun (freezeOracle P stop idle).toQueryPolicy reply tape n).1 =
      ((lazyPersistentRun P.toQueryPolicy reply tape k).1,true,
        P.output k (lazyPersistentRun P.toQueryPolicy reply tape k).1) := by
  have he := freezeOracle_lazy_before P stop idle reply tape k hbefore
  have hh : (lazyPersistentRun (freezeOracle P stop idle).toQueryPolicy reply tape k).1.2.1 = true := by
    rw [he]
    exact hk
  rw [freezeOracle_lazy_stable P stop idle reply tape hh n hkn,he,hk]

end
end SampleReuse
