import S3RD.lean.Blocks
namespace S3RD

theorem width4_half (n : Nat) (he : n%2=0) (hn : n=6 ∨ 10≤n) : Half 4 n := by
  rcases lengths_6_10_14 n he hn with ⟨k,rfl⟩|⟨k,rfl⟩|⟨k,rfl⟩
  · exact pack_half (pack_extend (by decide) (by decide) b4_6_pack b4_6_pack k) (by omega)
  · exact pack_half (pack_extend (by decide) (by decide) b4_10_pack b4_6_pack k) (by omega)
  · exact pack_half (pack_extend (by decide) (by decide) b4_14_pack b4_6_pack k) (by omega)

theorem width6_half_large (n : Nat) (he : n%2=0) (hn : n=6 ∨ 10≤n) : Half 6 n := by
  rcases lengths_6_10_14 n he hn with ⟨k,rfl⟩|⟨k,rfl⟩|⟨k,rfl⟩
  · exact pack_half (pack_extend (by decide) (by decide) b6_6_pack b6_6_pack k) (by omega)
  · exact pack_half (pack_extend (by decide) (by decide) b6_10_pack b6_6_pack k) (by omega)
  · exact pack_half (pack_extend (by decide) (by decide) b6_14_pack b6_6_pack k) (by omega)

theorem width5_half (n : Nat) (he : n%2=0) (hn : 4≤n) : Half 5 n := by
  rcases lengths_5 n he hn with rfl|rfl|⟨k,rfl⟩|⟨k,rfl⟩|⟨k,rfl⟩
  · exact b5_4_half
  · exact b5_10_half
  · exact pack_half (pack_extend (by decide) (by decide) b5_6_pack b5_6_pack k) (by omega)
  · exact pack_half (pack_extend (by decide) (by decide) b5_8_pack b5_6_pack k) (by omega)
  · have h16 := pack_concat (by decide) (by decide) b5_8_pack b5_8_pack
    exact pack_half (pack_extend (by decide) (by decide) h16 b5_6_pack k) (by omega)

theorem width7_half (n : Nat) (he : n%2=0) (hn : 4≤n) : Half 7 n := by
  by_cases h4 : n=4
  · subst n; exact b7_4_half
  by_cases h8 : n=8
  · subst n; exact b7_8_half
  rcases lengths_6_10_14 n he (by omega) with ⟨k,rfl⟩|⟨k,rfl⟩|⟨k,rfl⟩
  · exact pack_half (pack_extend (by decide) (by decide) b7_6_pack b7_6_pack k) (by omega)
  · exact pack_half (pack_extend (by decide) (by decide) b7_10_pack b7_6_pack k) (by omega)
  · exact pack_half (pack_extend (by decide) (by decide) b7_14_pack b7_6_pack k) (by omega)

theorem odd_short_half (m n : Nat) (hm : 5≤m) (ho : m%2=1) (hn : n=4 ∨ n=8) :
    Half m n := by
  have h3 : Half 3 n := by rcases hn with rfl|rfl; exact b3_4_half; exact b3_8_half
  have he : n%2=0 := by omega
  have hl : 4≤n := by omega
  have h5 := width5_half n he hl
  have h7 := width7_half n he hl
  have h6 : Half 6 n := half_vcat h3 h3
  have h9 : Half 9 n := half_vcat h3 h6
  have hh : (∃ k,m=5+6*k) ∨ (∃ k,m=7+6*k) ∨ (∃ k,m=9+6*k) := by
    have hx : m%6=5 ∨ m%6=1 ∨ m%6=3 := by omega
    rcases hx with hx|hx|hx
    · exact Or.inl ⟨(m-5)/6,by omega⟩
    · exact Or.inr (Or.inl ⟨(m-7)/6,by omega⟩)
    · exact Or.inr (Or.inr ⟨(m-9)/6,by omega⟩)
  rcases hh with ⟨k,rfl⟩|⟨k,rfl⟩|⟨k,rfl⟩
  · exact half_extend h5 h6 k
  · exact half_extend h7 h6 k
  · exact half_extend h9 h6 k

/-- Unconditional infinite-family construction, from the actual cylinder coloring definition. -/
theorem odd_even_half (m n : Nat) (hm : 5≤m) (ho : m%2=1)
    (hn : 4≤n) (he : n%2=0) : Half m n := by
  by_cases hs : n=4 ∨ n=8
  · exact odd_short_half m n hm ho hs
  have h4 := width4_half n he (by omega)
  have hh : (∃ k,m=5+4*k) ∨ (∃ k,m=7+4*k) := by
    by_cases h : m%4=1
    · exact Or.inl ⟨(m-5)/4,by omega⟩
    · exact Or.inr ⟨(m-7)/4,by omega⟩
  rcases hh with ⟨k,rfl⟩|⟨k,rfl⟩
  · exact half_extend (width5_half n he hn) h4 k
  · exact half_extend (width7_half n he hn) h4 k

def Optimal (m n : Nat) (f : Grid) : Prop :=
  Valid m n f ∧ ∀ g : Grid, Valid m n g → weight m n f ≤ weight m n g

/-- The missing general lower bound is explicit, not inserted as an axiom. -/
theorem odd_even_optimal_of_lower (m n : Nat) (hm : 5≤m) (ho : m%2=1)
    (hn : 4≤n) (he : n%2=0)
    (lower : ∀ g : Grid, Valid m n g → m*n≤2*weight m n g) :
    ∃ f : Grid, Optimal m n f ∧ 2*weight m n f=m*n := by
  obtain ⟨f,hf,hw⟩ := odd_even_half m n hm ho hn he
  refine ⟨f,⟨hf,?_⟩,hw⟩
  intro g hg
  have h := lower g hg
  omega

#print axioms width5_half
#print axioms width7_half
#print axioms odd_even_half
#print axioms odd_even_optimal_of_lower
end S3RD
