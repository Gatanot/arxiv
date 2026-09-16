import S3RD.lean.Core
namespace S3RD

abbrev Vertex (m n : Nat) := Fin m × Fin n

/-- Actual vertices and four-neighbor cylinder adjacency; the path coordinate does not wrap. -/
def Adjacent {m n : Nat} (v w : Vertex m n) : Prop :=
  (w.1.val=v.1.val ∧ (w.2.val=left n v.2.val ∨ w.2.val=right n v.2.val)) ∨
  (w.2.val=v.2.val ∧ (w.1.val+1=v.1.val ∨ v.1.val+1=w.1.val))

theorem left_lt (n j : Nat) (hn : 0<n) (hj : j<n) : left n j<n := by
  unfold left; split <;> omega

theorem right_lt (n j : Nat) (hn : 0<n) (_hj : j<n) : right n j<n := by
  unfold right; split <;> omega

theorem sees_iff_neighbor {m n : Nat} (hn : 0<n) (f : Grid) (r : Fin m) (j : Fin n) (c : Nat) :
    Sees m n f r j c ↔ ∃ w : Vertex m n, Adjacent (r,j) w ∧ f w.1 w.2=c := by
  constructor
  · intro h
    rcases h with h|h|⟨hu,h⟩|⟨hd,h⟩
    · exact ⟨(r,⟨left n j,left_lt n j hn j.isLt⟩),Or.inl ⟨rfl,Or.inl rfl⟩,h⟩
    · exact ⟨(r,⟨right n j,right_lt n j hn j.isLt⟩),Or.inl ⟨rfl,Or.inr rfl⟩,h⟩
    · refine ⟨(⟨r.val-1,by have := r.isLt; omega⟩,j),Or.inr ⟨rfl,Or.inl ?_⟩,h⟩
      change r.val-1+1=r.val
      omega
    · exact ⟨(⟨r.val+1,hd⟩,j),Or.inr ⟨rfl,Or.inr rfl⟩,h⟩
  · rintro ⟨⟨s,k⟩,ha,hc⟩
    simp only [Adjacent] at ha
    change f s.val k.val=c at hc
    rcases ha with ⟨hr,hj|hj⟩|⟨hj,hr|hr⟩
    · exact Or.inl (by simpa [hr,hj] using hc)
    · exact Or.inr (Or.inl (by simpa [hr,hj] using hc))
    · exact Or.inr (Or.inr (Or.inl ⟨by omega,by simpa [show s.val=r.val-1 by omega,hj] using hc⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨by have := s.isLt; omega,by simpa [← hr,hj] using hc⟩))

def SingletonRainbow (m n : Nat) (f : Grid) : Prop :=
  ∀ v : Vertex m n, f v.1 v.2≤3 ∧
    (f v.1 v.2=0 → ∀ c : Fin 3, ∃ w : Vertex m n, Adjacent v w ∧ f w.1 w.2=c.val+1)

theorem valid_iff_singletonRainbow {m n : Nat} (hn : 0<n) (f : Grid) :
    Valid m n f ↔ SingletonRainbow m n f := by
  constructor
  · intro h v
    refine ⟨(h v.1 v.2).1,?_⟩
    intro hz c
    exact (sees_iff_neighbor hn f v.1 v.2 (c.val+1)).mp ((h v.1 v.2).2 hz c)
  · intro h r j
    refine ⟨(h (r,j)).1,?_⟩
    intro hz c
    exact (sees_iff_neighbor hn f r j (c.val+1)).mpr ((h (r,j)).2 hz c)

#print axioms valid_iff_singletonRainbow
end S3RD
