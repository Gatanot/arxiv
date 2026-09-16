import S3RD.lean.Core
namespace S3RD

def Half (m n : Nat) : Prop := ∃ f : Grid, Valid m n f ∧ 2*weight m n f=m*n

def Pack (m n w : Nat) (A Z : Nat → Nat) : Prop :=
  ∃ f : Grid, Valid m n f ∧ weight m n f=w ∧
    ∀ r : Fin m, f r 0=A r ∧ f r (n-1)=Z r

theorem pack_concat {m a b u v : Nat} {A Z : Nat → Nat}
    (ha : 0<a) (hb : 0<b) (hf : Pack m a u A Z) (hg : Pack m b v A Z) :
    Pack m (a+b) (u+v) A Z := by
  obtain ⟨f,hf,wf,bf⟩ := hf
  obtain ⟨g,hg,wg,bg⟩ := hg
  refine ⟨hcat a f g,?_,?_,?_⟩
  · apply valid_hcat ha hb hf hg
    · intro r hr; exact (bf ⟨r,hr⟩).1.trans (bg ⟨r,hr⟩).1.symm
    · intro r hr; exact (bf ⟨r,hr⟩).2.trans (bg ⟨r,hr⟩).2.symm
  · rw [weight_hcat,wf,wg]
  · intro r
    constructor
    · simpa [hcat,ha] using (bf r).1
    · simpa [hcat,show ¬a+b-1<a by omega,show a+b-1-a=b-1 by omega] using (bg r).2

theorem pack_extend {m a b u v : Nat} {A Z : Nat → Nat}
    (ha : 0<a) (hb : 0<b) (hf : Pack m a u A Z) (hg : Pack m b v A Z)
    (k : Nat) : Pack m (a+b*k) (u+v*k) A Z := by
  induction k with
  | zero => simpa using hf
  | succ k ih =>
    have h := pack_concat (by omega : 0<a+b*k) hb ih hg
    simpa [Nat.mul_succ,Nat.add_assoc] using h

theorem pack_half {m n w : Nat} {A Z : Nat → Nat}
    (h : Pack m n w A Z) (hw : 2*w=m*n) : Half m n := by
  obtain ⟨f,hf,wf,_⟩ := h
  exact ⟨f,hf,by rw [wf]; exact hw⟩

theorem half_vcat {a b n : Nat} (hf : Half a n) (hg : Half b n) : Half (a+b) n := by
  obtain ⟨f,hf,wf⟩ := hf
  obtain ⟨g,hg,wg⟩ := hg
  refine ⟨vcat a f g,valid_vcat hf hg,?_⟩
  rw [weight_vcat,Nat.mul_add,wf,wg,Nat.add_mul]

theorem half_extend {a b n : Nat} (hf : Half a n) (hg : Half b n) (k : Nat) :
    Half (a+b*k) n := by
  induction k with
  | zero => simpa using hf
  | succ k ih => simpa [Nat.mul_succ,Nat.add_assoc] using half_vcat ih hg

theorem lengths_6_10_14 (n : Nat) (he : n%2=0) (hn : n=6 ∨ 10≤n) :
    (∃ k, n=6+6*k) ∨ (∃ k, n=10+6*k) ∨ (∃ k, n=14+6*k) := by
  have h : n%6=0 ∨ n%6=4 ∨ n%6=2 := by omega
  rcases h with h|h|h
  · exact Or.inl ⟨(n-6)/6,by omega⟩
  · exact Or.inr (Or.inl ⟨(n-10)/6,by omega⟩)
  · exact Or.inr (Or.inr ⟨(n-14)/6,by omega⟩)

theorem lengths_5 (n : Nat) (he : n%2=0) (hn : 4≤n) :
    n=4 ∨ n=10 ∨ (∃ k, n=6+6*k) ∨ (∃ k, n=8+6*k) ∨ (∃ k, n=16+6*k) := by
  by_cases h4 : n=4
  · exact Or.inl h4
  by_cases h10 : n=10
  · exact Or.inr (Or.inl h10)
  have h : n%6=0 ∨ n%6=2 ∨ n%6=4 := by omega
  rcases h with h|h|h
  · exact Or.inr (Or.inr (Or.inl ⟨(n-6)/6,by omega⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨(n-8)/6,by omega⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨(n-16)/6,by omega⟩)))

#print axioms pack_extend
#print axioms half_extend
#print axioms lengths_6_10_14
end S3RD
