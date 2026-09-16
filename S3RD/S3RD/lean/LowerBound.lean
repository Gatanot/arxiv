import S3RD.lean.Core
namespace S3RD

theorem count_offset (k : Nat) (f : Nat → Nat) :
    count (k+1) f=f 0+count k (fun i => f (i+1)) := by
  induction k with
  | zero => simp [count]
  | succ k ih => simp only [count] at ih ⊢; omega

theorem count_mono {k : Nat} {f g : Nat → Nat}
    (h : ∀i,i<k → f i≤g i) : count k f≤count k g := by
  induction k with
  | zero => simp [count]
  | succ k ih =>
    have h1 := ih (by intros; apply h; omega)
    have h2 := h k (by omega)
    simp only [count]; omega

theorem count_const (k a : Nat) : count k (fun _ => a)=k*a := by
  induction k with
  | zero => simp [count]
  | succ k ih => simp [count,ih,Nat.succ_mul]

theorem count_swap (m n : Nat) (f : Nat → Nat → Nat) :
    count m (fun r => count n (f r))=count n (fun j => count m (fun r => f r j)) := by
  induction m with
  | zero => simp [count,count_const]
  | succ m ih =>
    simp only [count]
    rw [count_sum,ih]

theorem count_right (n : Nat) (f : Nat → Nat) :
    count n (fun j => f (right n j))=count n f := by
  cases n with
  | zero => rfl
  | succ k =>
    rw [count,count_offset]
    have hc : count k (fun j => f (right (k+1) j))=count k (fun j => f (j+1)) := by
      apply count_congr
      intro j hj
      simp [right,show j+1<k+1 by omega]
    rw [hc]
    simp [right]; omega

theorem left_right (n j : Nat) (hn : 0<n) (hj : j<n) : left n (right n j)=j := by
  by_cases h : j+1<n
  · simp [right,h,left]
  · have he : j=n-1 := by omega
    simp only [right,if_neg h,left]
    simp
    omega

/-- A zero row-pair must be immediately followed by a full row-pair. -/
theorem pair_count_lower (m : Nat) (s : Nat → Nat)
    (h : ∀r,r<m → s r=0 → r+1<m ∧ s (r+1)=2) : m≤count m s := by
  induction m using Nat.strongRecOn generalizing s with
  | ind m ih =>
    cases m with
    | zero => simp [count]
    | succ k =>
      by_cases hz : s 0=0
      · have hh := h 0 (by omega) hz
        cases k with
        | zero => omega
        | succ t =>
          have ht := ih t (by omega) (fun i => s (i+2)) (by
            intro r hr hz
            have hx := h (r+2) (by omega) hz
            constructor
            · omega
            · simpa [Nat.add_assoc] using hx.2)
          rw [count_offset,count_offset]
          simp only [hz,Nat.zero_add] at *
          have he : count t (fun i => s (i+1+1))=count t (fun i => s (i+2)) := by
            apply count_congr; intros; congr 1 <;> omega
          rw [he]
          omega
      · have ht := ih k (by omega) (fun i => s (i+1)) (by
          intro r hr hz
          have hx := h (r+1) (by omega) hz
          constructor
          · omega
          · simpa [Nat.add_assoc] using hx.2)
        rw [count_offset]
        omega

theorem down_of_horizontal_zero {m n : Nat} {f : Grid} (hf : Valid m n f)
    (r : Fin m) (j : Fin n) (hz : f r j=0)
    (hh : f r (left n j)=0 ∨ f r (right n j)=0) :
    r.val+1<m ∧ f (r.val+1) j≠0 := by
  have h1 : Sees m n f r j 1 := (hf r j).2 hz ⟨0,by decide⟩
  have h2 : Sees m n f r j 2 := (hf r j).2 hz ⟨1,by decide⟩
  have h3 : Sees m n f r j 3 := (hf r j).2 hz ⟨2,by decide⟩
  simp only [Sees] at h1 h2 h3
  constructor
  · grind
  · grind

theorem lower_bound {m n : Nat} {f : Grid} (hn : 3≤n) (hf : Valid m n f) :
    m*n≤2*weight m n f := by
  have hp : ∀j,j<n → m≤count m (fun r => occupied (f r j)+occupied (f r (right n j))) := by
    intro j hj
    apply pair_count_lower
    intro r hr hz
    have hjr : right n j<n := by unfold right; split <;> omega
    have hz1 : f r j=0 := by unfold occupied at hz; split at hz <;> omega
    have hz2 : f r (right n j)=0 := by unfold occupied at hz; split at hz <;> split at hz <;> omega
    have hd1 := down_of_horizontal_zero hf ⟨r,hr⟩ ⟨j,hj⟩ hz1 (Or.inr hz2)
    have hleft : f r (left n (right n j))=0 := by rw [left_right n j (by omega) hj]; exact hz1
    have hd2 := down_of_horizontal_zero hf ⟨r,hr⟩ ⟨right n j,hjr⟩ hz2 (Or.inl hleft)
    exact ⟨hd1.1,by simp [occupied,hd1.2,hd2.2]⟩
  have hc := count_mono hp
  rw [count_const] at hc
  have hs : count n (fun j => count m (fun r => occupied (f r j)+occupied (f r (right n j))))=
      2*weight m n f := by
    have hsplit : count n (fun j => count m (fun r => occupied (f r j)+occupied (f r (right n j))))=
        count n (fun j => count m (fun r => occupied (f r j))+count m (fun r => occupied (f r (right n j)))) := by
      apply count_congr; intros; apply count_sum
    rw [hsplit,count_sum]
    rw [count_right n (fun j => count m (fun r => occupied (f r j)))]
    rw [← count_swap]
    unfold weight
    omega
  rw [hs] at hc
  simpa [Nat.mul_comm] using hc

#print axioms lower_bound
end S3RD
