import RobustGlobal254

noncomputable section
open scoped BigOperators
namespace Paper254

theorem uniform_local_error_budget (T : ℕ) (hT : 0<T) (lam δ : ℝ) (hlam : 0<lam)
    (ε ζ : ℕ → ℝ)
    (hε : ∀ t<T, ε t ≤ lam*δ/(2*T)) (hζ : ∀ t<T, ζ t ≤ lam*δ/(2*T)) :
    intervalCharge (totalLocalError ε ζ) 0 T/lam ≤ δ := by
  have hTr : (0 : ℝ)<T := by exact_mod_cast hT
  have hs := Finset.sum_le_sum (s := Finset.range T)
    (f := fun t=>ε t+ζ t) (g := fun _=>2*(lam*δ/(2*T)))
    (fun t ht=>by have he:=hε t (Finset.mem_range.mp ht); have hz:=hζ t (Finset.mem_range.mp ht); linarith)
  simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul] at hs
  have he : (T : ℝ)*(2*(lam*δ/(2*T)))=lam*δ := by field_simp
  rw [he] at hs
  apply (div_le_iff₀ hlam).mpr
  simpa only [intervalCharge,totalLocalError,Nat.zero_add,mul_comm] using hs

theorem InexactHistorySystem.fixed_scale_with_delta {T : ℕ} {r delta ε ζ : ℕ → ℝ} {lam a B q : ℝ}
    (S : InexactHistorySystem T r delta ε ζ lam a B q)
    (hT : 0<T) (hlam : 0<lam) (ha : 0≤a) (hB : 0<B) (hq : 0<q) (hd : ∀ t,0≤delta t)
    (L : ℕ) (hL : 1≤L) (hpow : T<2^L) (δ : ℝ)
    (hε : ∀ t<T,ε t≤lam*δ/(2*T)) (hζ : ∀ t<T,ζ t≤lam*δ/(2*T)) :
    intervalCharge r 0 T ≤ (restartThreshold L a B lam/64)*
      (1+intervalCharge delta 0 (T-1)/variationThreshold L a B lam q)+δ := by
  have hg := S.fixed_scale hlam ha hB hq hd L hL hpow
  have he := uniform_local_error_budget T hT lam δ hlam ε ζ hε hζ
  linarith

end Paper254
#print axioms Paper254.InexactHistorySystem.fixed_scale_with_delta
