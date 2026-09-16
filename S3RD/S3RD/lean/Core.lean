import Std

namespace S3RD

abbrev Grid := Nat → Nat → Nat

def left (n j : Nat) := if j = 0 then n - 1 else j - 1
def right (n j : Nat) := if j + 1 < n then j + 1 else 0

def Sees (m n : Nat) (f : Grid) (r j c : Nat) : Prop :=
  f r (left n j) = c ∨ f r (right n j) = c ∨
  (0 < r ∧ f (r-1) j = c) ∨ (r+1 < m ∧ f (r+1) j = c)

instance (m n : Nat) (f : Grid) (r j c : Nat) : Decidable (Sees m n f r j c) :=
  inferInstanceAs (Decidable (_ ∨ _ ∨ _ ∨ _))

def Valid (m n : Nat) (f : Grid) : Prop :=
  ∀ r : Fin m, ∀ j : Fin n, f r j ≤ 3 ∧
    (f r j = 0 → ∀ c : Fin 3, Sees m n f r j (c.val+1))

instance (m n : Nat) (f : Grid) : Decidable (Valid m n f) :=
  inferInstanceAs (Decidable (∀ _r : Fin m, ∀ _j : Fin n, _))

def count : Nat → (Nat → Nat) → Nat
  | 0, _ => 0
  | k+1, f => count k f + f k

def occupied (x : Nat) := if x = 0 then 0 else 1
def weight (m n : Nat) (f : Grid) := count m (fun r => count n (fun j => occupied (f r j)))

def hcat (a : Nat) (f g : Grid) : Grid := fun r j => if j<a then f r j else g r (j-a)
def vcat (a : Nat) (f g : Grid) : Grid := fun r j => if r<a then f r j else g (r-a) j

theorem count_congr {k : Nat} {f g : Nat → Nat}
    (h : ∀ i, i<k → f i=g i) : count k f=count k g := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [count]
    rw [ih (by intros; apply h; omega), h k (by omega)]

theorem count_add (a b : Nat) (f : Nat → Nat) :
    count (a+b) f=count a f+count b (fun i => f (a+i)) := by
  induction b with
  | zero => simp [count]
  | succ b ih => simp [count, ih, Nat.add_assoc]

theorem count_sum (k : Nat) (f g : Nat → Nat) :
    count k (fun i => f i+g i)=count k f+count k g := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [count, ih]; omega

theorem weight_hcat (m a b : Nat) (f g : Grid) :
    weight m (a+b) (hcat a f g)=weight m a f+weight m b g := by
  unfold weight
  rw [← count_sum]
  apply count_congr
  intro r hr
  rw [count_add]
  congr 1
  · apply count_congr; intro j hj; simp [hcat, hj]
  · apply count_congr; intro j hj; simp [hcat, show ¬a+j<a by omega]

theorem weight_vcat (a b n : Nat) (f g : Grid) :
    weight (a+b) n (vcat a f g)=weight a n f+weight b n g := by
  unfold weight
  rw [count_add]
  congr 1
  · apply count_congr; intro r hr
    apply count_congr; intro j hj; simp [vcat, hr]
  · apply count_congr; intro r hr
    apply count_congr; intro j hj; simp [vcat, show ¬a+r<a by omega]

theorem valid_vcat {a b n : Nat} {f g : Grid}
    (hf : Valid a n f) (hg : Valid b n g) : Valid (a+b) n (vcat a f g) := by
  intro r j
  have hr := r.isLt
  have hj := j.isLt
  by_cases h : r.val<a
  · have hv := hf ⟨r.val,h⟩ j
    constructor
    · simpa [vcat,h] using hv.1
    · intro hz c
      have hs := hv.2 (by simpa [vcat,h] using hz) c
      simp only [Sees] at hs ⊢
      rcases hs with hs|hs|⟨hu,hs⟩|⟨hd,hs⟩
      · exact Or.inl (by simpa [vcat,h] using hs)
      · exact Or.inr (Or.inl (by simpa [vcat,h] using hs))
      · exact Or.inr (Or.inr (Or.inl ⟨hu,by simpa [vcat,show r.val-1<a by omega] using hs⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨by omega,by simpa [vcat,hd] using hs⟩))
  · have hb : r.val-a<b := by omega
    have hv := hg ⟨r.val-a,hb⟩ j
    constructor
    · simpa [vcat,h] using hv.1
    · intro hz c
      have hs := hv.2 (by simpa [vcat,h] using hz) c
      simp only [Sees] at hs ⊢
      rcases hs with hs|hs|⟨hu,hs⟩|⟨hd,hs⟩
      · exact Or.inl (by simpa [vcat,h] using hs)
      · exact Or.inr (Or.inl (by simpa [vcat,h] using hs))
      · exact Or.inr (Or.inr (Or.inl ⟨by omega,by simpa [vcat,show ¬r.val-1<a by omega,show r.val-1-a=r.val-a-1 by omega] using hs⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨by omega,by simpa [vcat,show ¬r.val+1<a by omega,show r.val+1-a=r.val-a+1 by omega] using hs⟩))

theorem valid_hcat {m a b : Nat} {f g : Grid}
    (ha : 0<a) (hb : 0<b) (hf : Valid m a f) (hg : Valid m b g)
    (first : ∀ r, r<m → f r 0=g r 0)
    (last : ∀ r, r<m → f r (a-1)=g r (b-1)) :
    Valid m (a+b) (hcat a f g) := by
  intro r j
  have hr := r.isLt
  have hj := j.isLt
  by_cases h : j.val<a
  · have hv := hf r ⟨j.val,h⟩
    have hl : hcat a f g r.val (left (a+b) j.val)=f r.val (left a j.val) := by
      by_cases hz : j.val=0
      · simp [left,hz,hcat,show ¬a+b-1<a by omega,show a+b-1-a=b-1 by omega,last r.val hr]
      · simp [left,hz,hcat,show j.val-1<a by omega]
    have hright : hcat a f g r.val (right (a+b) j.val)=f r.val (right a j.val) := by
      by_cases hi : j.val+1<a
      · simp [right,hi,show j.val+1<a+b by omega,hcat]
      · have he : j.val+1=a := by omega
        simp [right,hcat,he,hb,first r.val hr]
    constructor
    · simpa [hcat,h] using hv.1
    · intro hz c
      have hs := hv.2 (by simpa [hcat,h] using hz) c
      simp only [Sees] at hs ⊢
      rcases hs with hs|hs|⟨hu,hs⟩|⟨hd,hs⟩
      · exact Or.inl (hl.trans hs)
      · exact Or.inr (Or.inl (hright.trans hs))
      · exact Or.inr (Or.inr (Or.inl ⟨hu,by simpa [hcat,h] using hs⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨hd,by simpa [hcat,h] using hs⟩))
  · have ht : j.val-a<b := by omega
    have hv := hg r ⟨j.val-a,ht⟩
    have hl : hcat a f g r.val (left (a+b) j.val)=g r.val (left b (j.val-a)) := by
      by_cases hz : j.val=a
      · simp [left,hz,hcat,show a≠0 by omega,show a-1<a by omega,last r.val hr]
      · simp [left,show j.val≠0 by omega,show j.val-a≠0 by omega,hcat,
          show ¬j.val-1<a by omega,show j.val-1-a=j.val-a-1 by omega]
    have hright : hcat a f g r.val (right (a+b) j.val)=g r.val (right b (j.val-a)) := by
      by_cases hi : j.val+1<a+b
      · simp [right,hi,show j.val-a+1<b by omega,hcat,
          show ¬j.val+1<a by omega,show j.val+1-a=j.val-a+1 by omega]
      · simp [right,hi,show ¬j.val-a+1<b by omega,hcat,ha,first r.val hr]
    constructor
    · simpa [hcat,h] using hv.1
    · intro hz c
      have hs := hv.2 (by simpa [hcat,h] using hz) c
      simp only [Sees] at hs ⊢
      rcases hs with hs|hs|⟨hu,hs⟩|⟨hd,hs⟩
      · exact Or.inl (hl.trans hs)
      · exact Or.inr (Or.inl (hright.trans hs))
      · exact Or.inr (Or.inr (Or.inl ⟨hu,by simpa [hcat,h] using hs⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨hd,by simpa [hcat,h] using hs⟩))

-- Explicit finite columns use default 0 only outside their declared rectangle.
def ofColumns (cs : List (List Nat)) : Grid := fun r j => (cs[j]?.getD [])[r]?.getD 0

#print axioms valid_hcat
#print axioms valid_vcat
#print axioms weight_hcat
#print axioms weight_vcat
end S3RD
