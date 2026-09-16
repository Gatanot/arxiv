import S3RD.lean.Assembly
import S3RD.lean.LowerBound
namespace S3RD

def Template (n : Nat) (p : Grid) : Prop :=
  ∀ r : Fin 4, ∀ j : Fin n, p r j≤3 ∧
    (r.val%2=0 → p (left 4 r) j=p (right 4 r) j) ∧
    (p r j=0 → ∀ c : Fin 3,
      p r (left n j)=c.val+1 ∨ p r (right n j)=c.val+1 ∨
      p (left 4 r) j=c.val+1 ∨ p (right 4 r) j=c.val+1)

instance (n : Nat) (p : Grid) : Decidable (Template n p) :=
  inferInstanceAs (Decidable (∀ _r : Fin 4, ∀ _j : Fin n, _))

def liftRows (p : Grid) : Grid := fun r j => p (r%4) j

theorem mod_right (r : Nat) : right 4 (r%4)=(r+1)%4 := by
  unfold right
  split <;> omega

theorem mod_left (r : Nat) (hr : 0<r) : left 4 (r%4)=(r-1)%4 := by
  unfold left
  split <;> omega

theorem template_valid {m n : Nat} {p : Grid} (hm : 3≤m) (ho : m%2=1)
    (hp : Template n p) : Valid m n (liftRows p) := by
  intro r j
  have hr := r.isLt
  have hv := hp ⟨r.val%4,by omega⟩ j
  constructor
  · exact hv.1
  · intro hz c
    have hs := hv.2.2 hz c
    simp only [Sees]
    rcases hs with h|h|h|h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · by_cases hu : 0<r.val
      · exact Or.inr (Or.inr (Or.inl ⟨hu,by simpa [liftRows,mod_left r.val hu] using h⟩))
      · have hr0 : r.val=0 := by omega
        have he := hv.2.1 (by simp [hr0])
        have hd : r.val+1<m := by omega
        exact Or.inr (Or.inr (Or.inr ⟨hd,by simpa [liftRows,mod_right] using he.symm.trans h⟩))
    · by_cases hd : r.val+1<m
      · exact Or.inr (Or.inr (Or.inr ⟨hd,by simpa [liftRows,mod_right] using h⟩))
      · have hu : 0<r.val := by omega
        have he := hv.2.1 (by change (r.val%4)%2=0; omega)
        exact Or.inr (Or.inr (Or.inl ⟨hu,by simpa [liftRows,mod_left r.val hu] using he.trans h⟩))

theorem count_alternating (k E O : Nat) :
    count (2*k+1) (fun r => if r%2=0 then E else O)=(k+1)*E+k*O := by
  induction k with
  | zero => simp [count]
  | succ k ih =>
    have he : 2*(k+1)+1=(2*k+1)+1+1 := by omega
    rw [he,count,count,ih]
    simp [Nat.add_mod,Nat.add_mul]
    omega

theorem template_weight {n E O : Nat} {p : Grid}
    (h : ∀ r : Fin 4, count n (fun j => occupied (p r j))=if r.val%2=0 then E else O)
    (k : Nat) : weight (2*k+1) n (liftRows p)=(k+1)*E+k*O := by
  unfold weight
  rw [← count_alternating k E O]
  apply count_congr
  intro r hr
  have hh := h ⟨r%4,by omega⟩
  have he : (r%4)%2=r%2 := by omega
  simpa [liftRows,he] using hh

def t3 : Grid := ofColumns [[1,0,3,0],[3,0,1,0],[0,2,0,2]]
def t4 : Grid := ofColumns [[1,0,3,0],[0,2,0,2],[3,0,1,0],[0,2,0,2]]
def t5 : Grid := ofColumns [[1,0,3,0],[1,0,3,0],[0,2,0,2],[3,0,1,0],[0,2,0,2]]

theorem t3_valid : Template 3 t3 := by decide
theorem t4_valid : Template 4 t4 := by decide
theorem t5_valid : Template 5 t5 := by decide

def firstOdd (r : Nat) := ([1,0,3,0] : List Nat)[r%4]?.getD 0
def lastOdd (r : Nat) := ([0,2,0,2] : List Nat)[r%4]?.getD 0

theorem odd_pack3 (k : Nat) (hk : 1≤k) : Pack (2*k+1) 3 (3*k+2) firstOdd lastOdd := by
  refine ⟨liftRows t3,template_valid (by omega) (by omega) t3_valid,?_,?_⟩
  · have h := template_weight (n:=3) (p:=t3) (E:=2) (O:=1) (by decide) k
    omega
  · intro r; exact ⟨rfl,rfl⟩

theorem odd_pack4 (k : Nat) (hk : 1≤k) : Pack (2*k+1) 4 (4*k+2) firstOdd lastOdd := by
  refine ⟨liftRows t4,template_valid (by omega) (by omega) t4_valid,?_,?_⟩
  · have h := template_weight (n:=4) (p:=t4) (E:=2) (O:=2) (by decide) k
    omega
  · intro r; exact ⟨rfl,rfl⟩

theorem odd_pack5 (k : Nat) (hk : 1≤k) : Pack (2*k+1) 5 (5*k+3) firstOdd lastOdd := by
  refine ⟨liftRows t5,template_valid (by omega) (by omega) t5_valid,?_,?_⟩
  · have h := template_weight (n:=5) (p:=t5) (E:=3) (O:=2) (by decide) k
    omega
  · intro r; exact ⟨rfl,rfl⟩

/-- Independent explicit construction also covers the previously cited odd/odd case. -/
theorem odd_odd_upper (m n : Nat) (hm : 3≤m) (ho : m%2=1)
    (hn : 3≤n) (he : n%2=1) :
    ∃ f : Grid, Valid m n f ∧ 2*weight m n f=m*n+1 := by
  obtain ⟨k,hk,hkm⟩ : ∃k,1≤k ∧ m=2*k+1 := ⟨m/2,by omega,by omega⟩
  subst m
  have hh : (∃t,n=3+4*t) ∨ (∃t,n=5+4*t) := by
    by_cases h : n%4=3
    · exact Or.inl ⟨(n-3)/4,by omega⟩
    · exact Or.inr ⟨(n-5)/4,by omega⟩
  rcases hh with ⟨t,rfl⟩|⟨t,rfl⟩
  · obtain ⟨f,hf,hw,_⟩ := pack_extend (by decide) (by decide) (odd_pack3 k hk) (odd_pack4 k hk) t
    exact ⟨f,hf,by rw [hw]; grind⟩
  · obtain ⟨f,hf,hw,_⟩ := pack_extend (by decide) (by decide) (odd_pack5 k hk) (odd_pack4 k hk) t
    exact ⟨f,hf,by rw [hw]; grind⟩

#print axioms odd_odd_upper
end S3RD
