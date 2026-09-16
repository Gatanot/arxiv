import S3RD.lean.Main
import S3RD.lean.Semantics
import S3RD.lean.Classification
import S3RD.lean.EvenWidths
import S3RD.lean.WidthThreeCount
namespace S3RD

/-- Same main result stated directly with actual finite vertices and neighboring colors. -/
theorem odd_width_graph_optimal (m n : Nat) (hm : 5≤m) (ho : m%2=1) (hn : 3≤n) :
    ∃ f : Grid, SingletonRainbow m n f ∧ weight m n f=(m*n+1)/2 ∧
      ∀ g : Grid, SingletonRainbow m n g → weight m n f≤weight m n g := by
  obtain ⟨f,hf,hw⟩ := odd_width_optimal m n hm ho hn
  refine ⟨f,(valid_iff_singletonRainbow (by omega) f).mp hf.1,hw,?_⟩
  intro g hg
  exact hf.2 g ((valid_iff_singletonRainbow (by omega) g).mpr hg)

theorem all_odd_graph_optimal (m n : Nat) (hm : 3≤m) (ho : m%2=1) (hn : 3≤n) :
    ∃ f : Grid, SingletonRainbow m n f ∧
      weight m n f=(m*n+1)/2+exception m n ∧
      ∀ g : Grid, SingletonRainbow m n g → weight m n f≤weight m n g := by
  obtain ⟨f,hf,hw⟩ := all_odd_optimal m n hm ho hn
  refine ⟨f,(valid_iff_singletonRainbow (by omega) f).mp hf.1,hw,?_⟩
  intro g hg
  exact hf.2 g ((valid_iff_singletonRainbow (by omega) g).mpr hg)

/-- Supplementary even-width theorem stated with the finite graph semantics. -/
theorem even_even_graph_optimal_large (m n : Nat) (hm : 4 ≤ m) (hme : m % 2 = 0)
    (hn3 : 3 ≤ n) (hne : n % 2 = 0) (hn : n = 6 ∨ 10 ≤ n) :
    ∃ f : Grid, SingletonRainbow m n f ∧ 2 * weight m n f = m*n ∧
      ∀ g : Grid, SingletonRainbow m n g → weight m n f ≤ weight m n g := by
  obtain ⟨f, hf, hw⟩ := even_even_optimal_large m n hm hme hn3 hne hn
  refine ⟨f, (valid_iff_singletonRainbow (by omega) f).mp hf.1, hw, ?_⟩
  intro g hg
  exact hf.2 g ((valid_iff_singletonRainbow (by omega) g).mpr hg)

theorem width6_even_graph_optimal (n : Nat) (hn : 3 ≤ n) (he : n % 2 = 0) :
    ∃ f : Grid, SingletonRainbow 6 n f ∧ weight 6 n f = 3*n ∧
      ∀ g : Grid, SingletonRainbow 6 n g → weight 6 n f ≤ weight 6 n g := by
  obtain ⟨f, hf, hw⟩ := width6_even_optimal n hn he
  refine ⟨f, (valid_iff_singletonRainbow (by omega) f).mp hf.1, hw, ?_⟩
  intro g hg
  exact hf.2 g ((valid_iff_singletonRainbow (by omega) g).mpr hg)

theorem width6_graph_optimal (n : Nat) (hn : 3 ≤ n) :
    ∃ f : Grid, SingletonRainbow 6 n f ∧ weight 6 n f = 3*n+n%2 ∧
      ∀ g : Grid, SingletonRainbow 6 n g → weight 6 n f ≤ weight 6 n g := by
  obtain ⟨f, hf, hw⟩ := width6_optimal n hn
  refine ⟨f, (valid_iff_singletonRainbow (by omega) f).mp hf.1, hw, ?_⟩
  intro g hg
  exact hf.2 g ((valid_iff_singletonRainbow (by omega) g).mpr hg)

/-- Complete graph-semantic formula for every even width at least six. -/
theorem even_width_graph_optimal (m n : Nat) (hm : 6 ≤ m) (hme : m % 2 = 0)
    (hn : 3 ≤ n) :
    ∃ f : Grid, SingletonRainbow m n f ∧ weight m n f = m*n/2+n%2 ∧
      ∀ g : Grid, SingletonRainbow m n g → weight m n f ≤ weight m n g := by
  obtain ⟨f, hf, hw⟩ := even_width_optimal m n hm hme hn
  refine ⟨f, (valid_iff_singletonRainbow (by omega) f).mp hf.1, hw, ?_⟩
  intro g hg
  exact hf.2 g ((valid_iff_singletonRainbow (by omega) g).mpr hg)

/-- Width four at every odd circumference, stated directly with the finite
    graph semantics.  The only width-four parameters not covered by this and
    the large even-circumference theorem are `n = 4` and `n = 8`. -/
theorem width4_odd_graph_optimal (n : Nat) (hn : 3 ≤ n) (hne : n % 2 = 1) :
    ∃ f : Grid, SingletonRainbow 4 n f ∧ weight 4 n f = 2*n+1 ∧
      ∀ g : Grid, SingletonRainbow 4 n g → weight 4 n f ≤ weight 4 n g := by
  obtain ⟨f, hf, hw⟩ := width4_odd_optimal n hn hne
  refine ⟨f, (valid_iff_singletonRainbow (by omega) f).mp hf.1, hw, ?_⟩
  intro g hg
  exact hf.2 g ((valid_iff_singletonRainbow (by omega) g).mpr hg)

/-- Unified optimum theorem for all widths at least five.  Odd widths attain
    the ceiling bound; even widths require one additional occupied vertex
    exactly at odd circumference. -/
theorem all_widths_ge_five_graph_optimal (m n : Nat) (hm : 5 ≤ m) (hn : 3 ≤ n) :
    ∃ f : Grid, SingletonRainbow m n f ∧
      weight m n f = (m*n+1)/2 + (if m%2=0 then n%2 else 0) ∧
      ∀ g : Grid, SingletonRainbow m n g → weight m n f ≤ weight m n g := by
  by_cases hme : m % 2 = 0
  · obtain ⟨f, hf, hw, ho⟩ := even_width_graph_optimal m n (by omega) hme hn
    have hprod : (m*n) % 2 = 0 := by
      rw [Nat.mul_mod]
      simp [hme]
    exact ⟨f, hf, by simp [hme]; omega, ho⟩
  · have hmo : m % 2 = 1 := by omega
    obtain ⟨f, hf, hw, ho⟩ := odd_width_graph_optimal m n hm hmo hn
    exact ⟨f, hf, by simp [hme, hw], ho⟩

#check all_odd_graph_optimal
#print axioms all_odd_graph_optimal
#check odd_width_graph_optimal
#print axioms odd_width_graph_optimal
#print axioms lower_bound
#print axioms odd_even_half
#print axioms odd_odd_upper
#print axioms valid_iff_singletonRainbow
#print axioms even_even_half_large
#print axioms even_even_optimal_large
#print axioms width6_even_optimal
#print axioms even_odd_upper
#print axioms width6_upper
#print axioms equality_support_alternating
#print axioms equality_support_even_circumference
#print axioms even_width_odd_strict_lower
#print axioms even_odd_optimal
#print axioms width6_optimal
#print axioms even_even_graph_optimal_large
#print axioms width6_even_graph_optimal
#print axioms width6_graph_optimal
#print axioms even_width_graph_optimal
#print axioms width4_odd_graph_optimal
#check all_widths_ge_five_graph_optimal
#print axioms all_widths_ge_five_graph_optimal
#print axioms equality_support_phases
#print axioms equality_strip_decomposition
#print axioms ColorCycle.good_pair_closes_iff
#print axioms ColorCycle.labeledHalfCount_formula
end S3RD
