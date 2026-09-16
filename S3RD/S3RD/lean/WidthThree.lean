import S3RD.lean.Main
import S3RD.lean.Semantics
import S3RD.lean.ColorPeriod
namespace S3RD

theorem occupied_le (a : Nat) : occupied a≤1 := by unfold occupied; split <;> omega
theorem occupied_eq_zero (a : Nat) : occupied a=0 ↔ a=0 := by unfold occupied; split <;> simp_all

theorem up_of_horizontal_zero {m n : Nat} {f : Grid} (hf : Valid m n f)
    (r : Fin m) (j : Fin n) (hz : f r j=0)
    (hh : f r (left n j)=0 ∨ f r (right n j)=0) :
    0<r.val ∧ f (r.val-1) j≠0 := by
  have h1 : Sees m n f r j 1 := (hf r j).2 hz ⟨0,by decide⟩
  have h2 : Sees m n f r j 2 := (hf r j).2 hz ⟨1,by decide⟩
  have h3 : Sees m n f r j 3 := (hf r j).2 hz ⟨2,by decide⟩
  simp only [Sees] at h1 h2 h3
  constructor <;> grind

def pairWeight (n : Nat) (f : Grid) (r j : Nat) :=
  occupied (f r j)+occupied (f r (right n j))

theorem rowpair_zero {n : Nat} {f : Grid} (hf : Valid 3 n f) (hn : 3≤n)
    (r : Fin 3) (j : Fin n) (hz : pairWeight n f r j=0) :
    r.val=1 ∧ pairWeight n f 0 j=2 ∧ pairWeight n f 2 j=2 := by
  have hz1 : f r j=0 := by
    have : occupied (f r j)=0 := by unfold pairWeight at hz; omega
    exact (occupied_eq_zero _).mp this
  have hz2 : f r (right n j)=0 := by
    have : occupied (f r (right n j))=0 := by unfold pairWeight at hz; omega
    exact (occupied_eq_zero _).mp this
  have hleft : f r (left n (right n j))=0 := by
    rw [left_right n j (by omega) j.isLt]; exact hz1
  have up1 := up_of_horizontal_zero hf r j hz1 (Or.inr hz2)
  have dn1 := down_of_horizontal_zero hf r j hz1 (Or.inr hz2)
  let jr : Fin n := ⟨right n j,right_lt n j (by omega) j.isLt⟩
  have up2 := up_of_horizontal_zero hf r jr hz2 (Or.inl hleft)
  have dn2 := down_of_horizontal_zero hf r jr hz2 (Or.inl hleft)
  have hr : r.val=1 := by omega
  refine ⟨hr,?_,?_⟩
  · have h1 : f 0 j≠0 := by simpa [hr] using up1.2
    have h2 : f 0 (right n j)≠0 := by simpa [hr,jr] using up2.2
    simp [pairWeight,occupied,h1,h2]
  · have h1 : f 2 j≠0 := by simpa [hr] using dn1.2
    have h2 : f 2 (right n j)≠0 := by simpa [hr,jr] using dn2.2
    simp [pairWeight,occupied,h1,h2]

theorem three_pair_lower {n : Nat} {f : Grid} (hf : Valid 3 n f) (hn : 3≤n)
    (j : Fin n) : 3≤count 3 (fun r => pairWeight n f r j) := by
  have h0 : pairWeight n f 0 j≠0 := by
    intro h; have := (rowpair_zero hf hn ⟨0,by decide⟩ j h).1; contradiction
  have h2 : pairWeight n f 2 j≠0 := by
    intro h; have := (rowpair_zero hf hn ⟨2,by decide⟩ j h).1; contradiction
  by_cases h1 : pairWeight n f 1 j=0
  · have h := rowpair_zero hf hn ⟨1,by decide⟩ j h1
    simp [count,h.2.1,h.2.2,h1]
  · simp only [count]; omega

theorem count_eq_const {k a : Nat} {f : Nat → Nat} (h : ∀i,i<k → a≤f i)
    (he : count k f=k*a) : ∀i,i<k → f i=a := by
  induction k with
  | zero => intros; omega
  | succ k ih =>
    have hl : k*a≤count k f := by simpa [count_const] using count_mono (k:=k) (f:=fun _=>a) (g:=f) (by intros; apply h; omega)
    have hk := h k (by omega)
    have hsum : count k f+f k=(k+1)*a := he
    have ha : (k+1)*a=k*a+a := by simp [Nat.add_mul]
    have heq : f k=a := by omega
    have hprev : count k f=k*a := by omega
    intro i hi
    by_cases hit : i<k
    · exact ih (by intros; apply h; omega) hprev i hit
    · have : i=k := by omega
      simpa [this] using heq

theorem pairs_sum (m n : Nat) (f : Grid) :
    count n (fun j => count m (fun r => pairWeight n f r j))=2*weight m n f := by
  unfold pairWeight
  have hs : count n (fun j => count m (fun r => occupied (f r j)+occupied (f r (right n j))))=
      count n (fun j => count m (fun r => occupied (f r j))+count m (fun r => occupied (f r (right n j)))) := by
    apply count_congr; intros; apply count_sum
  rw [hs,count_sum,count_right n (fun j => count m (fun r => occupied (f r j))),←count_swap]
  unfold weight; omega

/-- Actual half-weight colorings on width three alternate in every row. -/
theorem width3_alternating {n : Nat} {f : Grid} (hf : Valid 3 n f) (hn : 3≤n)
    (hw : 2*weight 3 n f=3*n) :
    ∀r : Fin 3, ∀j : Fin n, pairWeight n f r j=1 := by
  have hp : ∀j,j<n → 3≤count 3 (fun r => pairWeight n f r j) := by
    intro j hj; exact three_pair_lower hf hn ⟨j,hj⟩
  have hsum : count n (fun j => count 3 (fun r => pairWeight n f r j))=n*3 := by
    rw [pairs_sum,hw,Nat.mul_comm]
  have he := count_eq_const hp hsum
  intro r j
  have ht := he j.val j.isLt
  have h0 : pairWeight n f 0 j≠0 := by
    intro h; have := (rowpair_zero hf hn ⟨0,by decide⟩ j h).1; contradiction
  have h2 : pairWeight n f 2 j≠0 := by
    intro h; have := (rowpair_zero hf hn ⟨2,by decide⟩ j h).1; contradiction
  have h1 : pairWeight n f 1 j≠0 := by
    intro h
    have hx := rowpair_zero hf hn ⟨1,by decide⟩ j h
    simp only [count] at ht
    omega
  simp only [count] at ht
  have hr : r.val=0 ∨ r.val=1 ∨ r.val=2 := by have := r.isLt; omega
  rcases hr with hr|hr|hr <;> change pairWeight n f r.val j.val=1 <;> rw [hr] <;> omega

theorem boundary_zero_middle {n : Nat} {f : Grid} (hf : Valid 3 n f)
    (r : Fin 3) (hr : r.val=0 ∨ r.val=2) (j : Fin n) (hz : f r j=0) : f 1 j≠0 := by
  have h1 := (hf r j).2 hz ⟨0,by decide⟩
  have h2 := (hf r j).2 hz ⟨1,by decide⟩
  have h3 := (hf r j).2 hz ⟨2,by decide⟩
  simp only [Sees] at h1 h2 h3
  rcases hr with hr|hr <;> simp only [hr] at h1 h2 h3 <;> grind

theorem width3_column_shape {n : Nat} {f : Grid} (hf : Valid 3 n f) (hn : 3≤n)
    (hw : 2*weight 3 n f=3*n) (j : Fin n) :
    (f 0 j=0 ∧ f 1 j≠0 ∧ f 2 j=0) ∨ (f 0 j≠0 ∧ f 1 j=0 ∧ f 2 j≠0) := by
  have ha := width3_alternating hf hn hw
  have hb : ∀r : Fin 3, r.val=0 ∨ r.val=2 → (f r j=0 ↔ f 1 j≠0) := by
    intro r hr
    constructor
    · exact boundary_zero_middle hf r hr j
    · intro hm
      by_cases h : f r j=0
      · exact h
      exfalso
      have hp := ha r j
      have hz : f r (right n j)=0 := by
        simp [pairWeight,occupied,h] at hp
        exact hp
      let jr : Fin n := ⟨right n j,right_lt n j (by omega) j.isLt⟩
      have hm2 := boundary_zero_middle hf r hr jr hz
      have hp1 := ha ⟨1,by decide⟩ j
      change f 1 (right n j)≠0 at hm2
      simp [pairWeight,occupied,hm,hm2] at hp1
  have h0 := hb ⟨0,by decide⟩ (Or.inl rfl)
  have h2 := hb ⟨2,by decide⟩ (Or.inr rfl)
  by_cases h : f 1 j=0
  · right; grind
  · left; grind

#print axioms width3_alternating
#print axioms width3_column_shape
end S3RD
