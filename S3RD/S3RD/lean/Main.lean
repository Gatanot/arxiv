import S3RD.lean.UpperBounds
import S3RD.lean.LowerBound
import S3RD.lean.OddCircumference
namespace S3RD

/-- Exact optimality for the newly completed odd-width/even-circumference family.
    Both the general lower bound and the infinite construction are proved in Lean. -/
theorem odd_even_optimal (m n : Nat) (hm : 5≤m) (ho : m%2=1)
    (hn : 4≤n) (he : n%2=0) :
    ∃ f : Grid, Optimal m n f ∧ 2*weight m n f=m*n := by
  apply odd_even_optimal_of_lower m n hm ho hn he
  intro g hg
  exact lower_bound (by omega) hg

#print axioms odd_even_optimal

theorem odd_odd_optimal (m n : Nat) (hm : 3≤m) (ho : m%2=1)
    (hn : 3≤n) (he : n%2=1) :
    ∃ f : Grid, Optimal m n f ∧ weight m n f=(m*n+1)/2 := by
  obtain ⟨f,hf,hw⟩ := odd_odd_upper m n hm ho hn he
  refine ⟨f,⟨hf,?_⟩,by omega⟩
  intro g hg
  have h := lower_bound hn hg
  omega

/-- All circumferences, with no literature theorem left as a hypothesis. -/
theorem odd_width_optimal (m n : Nat) (hm : 5≤m) (ho : m%2=1) (hn : 3≤n) :
    ∃ f : Grid, Optimal m n f ∧ weight m n f=(m*n+1)/2 := by
  by_cases he : n%2=0
  · obtain ⟨f,hf,hw⟩ := odd_even_optimal m n hm ho (by omega) he
    exact ⟨f,hf,by omega⟩
  · exact odd_odd_optimal m n (by omega) ho hn (by omega)

#print axioms odd_odd_optimal
#print axioms odd_width_optimal
end S3RD
