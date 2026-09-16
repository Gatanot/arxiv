import S3RD.lean.WidthThree
namespace S3RD
open ColorCycle

theorem column_encoded (a b c : Nat) (ha : a≤3) (hb : b≤3) (hc : c≤3)
    (hs : (a=0 ∧ b≠0 ∧ c=0) ∨ (a≠0 ∧ b=0 ∧ c≠0)) :
    ∃q : Fin 12, color q 0=a ∧ color q 1=b ∧ color q 2=c := by
  rcases hs with ⟨rfl,hb0,rfl⟩|⟨ha0,rfl,hc0⟩
  · have hb' : b-1<3 := by omega
    refine ⟨⟨b-1,by omega⟩,?_,?_,?_⟩ <;> simp [color,hb'] <;> omega
  · have he : ¬3+3*(a-1)+(c-1)<3 := by omega
    refine ⟨⟨3+3*(a-1)+(c-1),by omega⟩,?_,?_,?_⟩ <;>
      simp [color,he] <;> omega

theorem width3_half_period {n : Nat} {f : Grid} (hf : Valid 3 n f) (hn : 3≤n)
    (hw : 2*weight 3 n f=3*n) : n%4=0 ∨ n%6=0 := by
  classical
  have he : ∀j : Fin n, ∃q : Fin 12, ∀r : Fin 3, color q r=f r j := by
    intro j
    obtain ⟨q,h0,h1,h2⟩ := column_encoded _ _ _ (hf ⟨0,by decide⟩ j).1
      (hf ⟨1,by decide⟩ j).1 (hf ⟨2,by decide⟩ j).1 (width3_column_shape hf hn hw j)
    refine ⟨q,?_⟩
    intro r
    have hr : r.val=0 ∨ r.val=1 ∨ r.val=2 := by have := r.isLt; omega
    rcases hr with hr|hr|hr <;> change color q r.val=f r.val j <;> simp [hr,h0,h1,h2]
  let enc (j : Fin n) : Fin 12 := Classical.choose (he j)
  have hd (j : Fin n) (r : Fin 3) : color (enc j) r=f r j := Classical.choose_spec (he j) r
  have hz (q : Fin 12) : color q 0=0 ↔ q.val<3 := by
    simp [color]
  have hop (j : Fin n) : Opposite (enc j) (enc ⟨right n j,right_lt n j (by omega) j.isLt⟩) := by
    have h := width3_alternating hf hn hw ⟨0,by decide⟩ j
    let jr : Fin n := ⟨right n j,right_lt n j (by omega) j.isLt⟩
    have h0 := hd j ⟨0,by decide⟩
    have h1 := hd jr ⟨0,by decide⟩
    have z0 := hz (enc j)
    have z1 := hz (enc jr)
    change Opposite (enc j) (enc jr)
    unfold Opposite
    simp only [pairWeight,occupied] at h
    change color (enc j) 0=f 0 j at h0
    change color (enc jr) 0=f 0 (right n j) at h1
    grind
  let col (k : Nat) : Fin n := ⟨k%n,Nat.mod_lt _ (by omega)⟩
  have hr (k : Nat) : right n (col k)=(col (k+1)).val := by
    simp only [col,right]
    rw [←Nat.mod_add_mod k n 1]
    have hlt := Nat.mod_lt k (show 0<n by omega)
    split
    · exact (Nat.mod_eq_of_lt (by omega)).symm
    · have he : k%n+1=n := by omega
      rw [he,Nat.mod_self]
  let s (k : Nat) := enc (col k)
  apply closed_walk_period s n
  · intro k
    have hop0 := hop (col k)
    have hop1 := hop (col (k+1))
    have er (k : Nat) : (⟨right n (col k),right_lt n (col k) (by omega) (col k).isLt⟩ : Fin n)=col (k+1) := by
      apply Fin.ext; exact hr k
    rw [er] at hop0 hop1
    refine ⟨hop0,hop1,?_⟩
    intro r hzero d
    have hzero' : f r (col (k+1))=0 := by rw [←hd]; exact hzero
    have hv := (hf r (col (k+1))).2 hzero' d
    have hl : left n (col (k+1))=(col k).val := by rw [←hr k]; exact left_right n (col k) (by omega) (col k).isLt
    simp only [Sees,hl,hr] at hv
    change color (s k) r=d.val+1 ∨ color (s (k+2)) r=d.val+1 ∨
      (0<r.val ∧ color (s (k+1)) (r.val-1)=d.val+1) ∨
      (r.val+1<3 ∧ color (s (k+1)) (r.val+1)=d.val+1)
    rcases hv with h|h|⟨hri,h⟩|⟨hri,h⟩
    · left; exact (hd (col k) r).trans h
    · right; left; exact (hd (col (k+2)) r).trans h
    · right; right; left; exact ⟨hri,(hd (col (k+1)) ⟨r.val-1,by omega⟩).trans h⟩
    · right; right; right; exact ⟨hri,(hd (col (k+1)) ⟨r.val+1,hri⟩).trans h⟩
  · intro k
    simp [s,col,Nat.add_mod_right]

#print axioms width3_half_period
end S3RD
