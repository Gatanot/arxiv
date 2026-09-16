import S3RD.lean.WidthThreePeriod
namespace S3RD

def end3 (a b c : Nat) (r : Nat) := ([a,b,c] : List Nat)[r]?.getD 0
theorem three4 : Pack 3 4 6 (end3 1 0 3) (end3 0 2 0) := by
  refine ⟨ofColumns [[1,0,3],[0,2,0],[3,0,1],[0,2,0]],?_⟩; decide
theorem three6 : Pack 3 6 9 (end3 1 0 1) (end3 0 3 0) := by
  refine ⟨ofColumns [[1,0,1],[0,2,0],[3,0,3],[0,1,0],[2,0,2],[0,3,0]],?_⟩; decide
theorem three_defect : Pack 3 6 10 (end3 1 0 3) (end3 0 2 0) := by
  refine ⟨ofColumns [[1,0,3],[1,0,2],[0,3,0],[2,0,1],[3,0,1],[0,2,0]],?_⟩; decide

theorem width3_half_upper (n : Nat) (hn : 3≤n) (hp : n%4=0 ∨ n%6=0) : Half 3 n := by
  rcases hp with hp|hp
  · have he : n=4+4*((n-4)/4) := by omega
    rw [he]
    apply pack_half (pack_extend (by decide) (by decide) three4 three4 ((n-4)/4))
    omega
  · have he : n=6+6*((n-6)/6) := by omega
    rw [he]
    apply pack_half (pack_extend (by decide) (by decide) three6 three6 ((n-6)/6))
    omega

theorem width3_defect_upper (n : Nat) (hn : 3≤n) (hp : n%4=2) :
    ∃f, Valid 3 n f ∧ 2*weight 3 n f=3*n+2 := by
  have he : n=6+4*((n-6)/4) := by omega
  obtain ⟨f,hf,hw,_⟩ := pack_extend (by decide) (by decide) three_defect three4 ((n-6)/4)
  refine ⟨f,?_,?_⟩
  · simpa [←he] using hf
  · rw [he,hw]; omega

def exception (m n : Nat) : Nat := if m=3 ∧ (n%12=2 ∨ n%12=10) then 1 else 0

theorem width3_optimal (n : Nat) (hn : 3≤n) :
    ∃f, Optimal 3 n f ∧ weight 3 n f=(3*n+1)/2+exception 3 n := by
  by_cases hx : n%12=2 ∨ n%12=10
  · obtain ⟨f,hf,hw⟩ := width3_defect_upper n hn (by omega)
    refine ⟨f,⟨hf,?_⟩,?_⟩
    · intro g hg
      have hl := lower_bound hn hg
      have hne : 2*weight 3 n g≠3*n := by
        intro he
        have := width3_half_period hg hn he
        omega
      omega
    · simp [exception,hx]; omega
  · have hex : exception 3 n=0 := by simp [exception,hx]
    rw [hex,Nat.add_zero]
    by_cases he : n%2=0
    · obtain ⟨f,hf,hw⟩ := width3_half_upper n hn (by omega)
      refine ⟨f,⟨hf,?_⟩,by omega⟩
      intro g hg
      have := lower_bound hn hg
      omega
    · exact odd_odd_optimal 3 n (by decide) (by decide) hn (by omega)

/-- Complete exact classification for all odd widths at least three. -/
theorem all_odd_optimal (m n : Nat) (hm : 3≤m) (ho : m%2=1) (hn : 3≤n) :
    ∃f, Optimal m n f ∧ weight m n f=(m*n+1)/2+exception m n := by
  by_cases he : m=3
  · subst m; exact width3_optimal n hn
  · have hx : exception m n=0 := by simp [exception,he]
    rw [hx,Nat.add_zero]
    exact odd_width_optimal m n (by omega) ho hn

#print axioms three_defect
#print axioms width3_optimal
#print axioms all_odd_optimal
end S3RD
