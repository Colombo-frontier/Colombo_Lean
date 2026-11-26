import SecondOrder.LocalSampleEnumeration

namespace SecondOrder
noncomputable section

variable {Ω : Type}

theorem drawsVector_append_left (n m : ℕ) (u : Draws Ω n) (v : Draws Ω m) (i : Fin n) :
    drawsVector id (n+m) (drawsAppend n m u v) (i.castAdd m)=drawsVector id n u i := by
  induction m with
  | zero => rfl
  | succ m ih =>
    have he : i.castAdd (m+1)=(i.castAdd m).castSucc := by ext; rfl
    rw [he]
    simpa only [drawsAppend,drawsVector,Fin.snoc_castSucc] using ih v.1

theorem drawsVector_append_right (n m : ℕ) (u : Draws Ω n) (v : Draws Ω m) (i : Fin m) :
    drawsVector id (n+m) (drawsAppend n m u v) (i.natAdd n)=drawsVector id m v i := by
  induction m with
  | zero => exact Fin.elim0 i
  | succ m ih =>
    refine Fin.lastCases ?_ (fun j => ?_) i
    · have he : (Fin.last m).natAdd n=Fin.last (n+m) := by ext; rfl
      rw [he]
      simp only [drawsAppend,drawsVector,Fin.snoc_last,id_eq]
      exact Fin.snoc_last _ _
    · have he : j.castSucc.natAdd n=(j.natAdd n).castSucc := by ext; rfl
      rw [he]
      simpa only [drawsAppend,drawsVector,Fin.snoc_castSucc] using ih v.1 j

theorem drawsTape_append_left (a₀ : Ω) (n m : ℕ) (u : Draws Ω n) (v : Draws Ω m) (i : Fin n) :
    drawsTape a₀ (n+m) (drawsAppend n m u v) i=drawsVector id n u i := by
  exact (drawsTape_apply a₀ (n+m) (drawsAppend n m u v) (i.castAdd m)).trans
    (drawsVector_append_left n m u v i)

theorem drawsTape_append_right (a₀ : Ω) (n m : ℕ) (u : Draws Ω n) (v : Draws Ω m) (i : Fin m) :
    drawsTape a₀ (n+m) (drawsAppend n m u v) (n+i)=drawsVector id m v i := by
  exact (drawsTape_apply a₀ (n+m) (drawsAppend n m u v) (i.natAdd n)).trans
    (drawsVector_append_right n m u v i)

end
end SecondOrder
