import S3RD.lean.EqualitySupport

namespace S3RD

/-- Every even width at least four has a half-weight coloring for the
    circumferences covered by the compatible width-four and width-six packs. -/
theorem even_even_half_large (m n : Nat) (hm : 4 ≤ m) (hme : m % 2 = 0)
    (hne : n % 2 = 0) (hn : n = 6 ∨ 10 ≤ n) : Half m n := by
  have h4 := width4_half n hne hn
  have h6 := width6_half_large n hne hn
  by_cases h0 : m % 4 = 0
  · obtain ⟨k, rfl⟩ : ∃ k, m = 4 + 4*k := ⟨(m-4)/4, by omega⟩
    exact half_extend h4 h4 k
  · obtain ⟨k, rfl⟩ : ∃ k, m = 6 + 4*k := ⟨(m-6)/4, by omega⟩
    exact half_extend h6 h4 k

theorem width6_half_short (n : Nat) (hn : n = 4 ∨ n = 8) : Half 6 n := by
  have h3 : Half 3 n := by
    rcases hn with rfl | rfl
    · exact b3_4_half
    · exact b3_8_half
  exact half_vcat h3 h3

/-- The short even circumferences are also covered at every even width at
    least six: split the width as `3 + (m-3)` and stack odd-width blocks. -/
theorem even_even_half_short (m n : Nat) (hm : 6 ≤ m) (hme : m % 2 = 0)
    (hn : n = 4 ∨ n = 8) : Half m n := by
  have h3 : Half 3 n := by
    rcases hn with rfl | rfl
    · exact b3_4_half
    · exact b3_8_half
  by_cases h6 : m = 6
  · subst m
    exact half_vcat h3 h3
  · have hrest : 5 ≤ m - 3 := by omega
    have hrestOdd : (m - 3) % 2 = 1 := by omega
    have hmadd : 3 + (m - 3) = m := by omega
    simpa [hmadd] using half_vcat h3 (odd_short_half (m - 3) n hrest hrestOdd hn)

/-- Every even width at least six has a half-weight coloring at every even
    circumference.  The only short cases missing from the large-block theorem
    are supplied by `even_even_half_short`. -/
theorem even_even_half (m n : Nat) (hm : 6 ≤ m) (hme : m % 2 = 0)
    (hn : 3 ≤ n) (hne : n % 2 = 0) : Half m n := by
  by_cases hs : n = 4 ∨ n = 8
  · exact even_even_half_short m n hm hme hs
  · exact even_even_half_large m n (by omega) hme hne (by omega)

theorem width6_half (n : Nat) (hn : 3 ≤ n) (he : n % 2 = 0) : Half 6 n := by
  by_cases hs : n = 4 ∨ n = 8
  · exact width6_half_short n hs
  · exact width6_half_large n he (by omega)

theorem optimal_of_half {m n : Nat} (hn : 3 ≤ n) (h : Half m n) :
    ∃ f : Grid, Optimal m n f ∧ 2 * weight m n f = m*n := by
  obtain ⟨f, hf, hw⟩ := h
  refine ⟨f, ⟨hf, ?_⟩, hw⟩
  intro g hg
  have hl := lower_bound hn hg
  omega

/-- Fully formalized version of Theorem A in `docs/even_widths.md`. -/
theorem even_even_optimal_large (m n : Nat) (hm : 4 ≤ m) (hme : m % 2 = 0)
    (hn3 : 3 ≤ n) (hne : n % 2 = 0) (hn : n = 6 ∨ 10 ≤ n) :
    ∃ f : Grid, Optimal m n f ∧ 2 * weight m n f = m*n := by
  exact optimal_of_half hn3 (even_even_half_large m n hm hme hne hn)

/-- Complete optimum theorem for even widths at least six and even
    circumferences, including circumferences four and eight. -/
theorem even_even_optimal (m n : Nat) (hm : 6 ≤ m) (hme : m % 2 = 0)
    (hn : 3 ≤ n) (hne : n % 2 = 0) :
    ∃ f : Grid, Optimal m n f ∧ 2 * weight m n f = m*n := by
  exact optimal_of_half hn (even_even_half m n hm hme hn hne)

/-- Exact width-six result at every even circumference. -/
theorem width6_even_optimal (n : Nat) (hn : 3 ≤ n) (he : n % 2 = 0) :
    ∃ f : Grid, Optimal 6 n f ∧ weight 6 n f = 3*n := by
  obtain ⟨f, hf, hw⟩ := optimal_of_half hn (width6_half n hn he)
  exact ⟨f, hf, by omega⟩

/-- Constructive half of the even-width, odd-circumference formula. -/
theorem even_odd_upper (m n : Nat) (hm : 6 ≤ m) (hme : m % 2 = 0)
    (hn : 3 ≤ n) (hne : n % 2 = 1) :
    ∃ f : Grid, Valid m n f ∧ 2 * weight m n f = m*n + 2 := by
  have hrest : 3 ≤ m-3 := by omega
  have hrestOdd : (m-3) % 2 = 1 := by omega
  have hmadd : 3 + (m-3) = m := by omega
  obtain ⟨f, hf, hwf⟩ := odd_odd_upper 3 n (by omega) (by omega) hn hne
  obtain ⟨g, hg, hwg⟩ := odd_odd_upper (m-3) n hrest hrestOdd hn hne
  refine ⟨vcat 3 f g, by simpa [hmadd] using valid_vcat hf hg, ?_⟩
  rw [← hmadd]
  rw [weight_vcat]
  calc
    2 * (weight 3 n f + weight (m-3) n g) =
        2 * weight 3 n f + 2 * weight (m-3) n g := by omega
    _ = (3*n+1) + ((m-3)*n+1) := by rw [hwf, hwg]
    _ = (3+(m-3))*n+2 := by rw [Nat.add_mul]; omega

/-- Complete optimum theorem for even width at odd circumference. -/
theorem even_odd_optimal (m n : Nat) (hm : 6 ≤ m) (hme : m % 2 = 0)
    (hn : 3 ≤ n) (hne : n % 2 = 1) :
    ∃ f : Grid, Optimal m n f ∧ 2 * weight m n f = m*n + 2 := by
  obtain ⟨f, hf, hw⟩ := even_odd_upper m n hm hme hn hne
  refine ⟨f, ⟨hf, ?_⟩, hw⟩
  intro g hg
  have hl := even_width_odd_strict_lower (by omega) hme hn hne hg
  omega

/-- Compatible odd-circumference blocks give the width-four upper bound for
    every odd circumference. -/
theorem width4_odd_upper (n : Nat) (hn : 3 ≤ n) (hne : n % 2 = 1) :
    ∃ f : Grid, Valid 4 n f ∧ weight 4 n f = 2*n+1 := by
  have hr : n % 6 = 1 ∨ n % 6 = 3 ∨ n % 6 = 5 := by omega
  rcases hr with hr | hr | hr
  · obtain ⟨k, rfl⟩ : ∃ k, n = 7 + 6*k := ⟨(n-7)/6, by omega⟩
    obtain ⟨f, hf, hw, _⟩ := pack_extend (by decide) (by decide)
      b4_7_odd_pack b4_6_pack k
    exact ⟨f, hf, by rw [hw]; omega⟩
  · obtain ⟨k, rfl⟩ : ∃ k, n = 3 + 6*k := ⟨(n-3)/6, by omega⟩
    obtain ⟨f, hf, hw, _⟩ := pack_extend (by decide) (by decide)
      b4_3_odd_pack b4_6_pack k
    exact ⟨f, hf, by rw [hw]; omega⟩
  · obtain ⟨k, rfl⟩ : ∃ k, n = 5 + 6*k := ⟨(n-5)/6, by omega⟩
    obtain ⟨f, hf, hw, _⟩ := pack_extend (by decide) (by decide)
      b4_5_odd_pack b4_6_pack k
    exact ⟨f, hf, by rw [hw]; omega⟩

/-- Exact width-four formula at every odd circumference. -/
theorem width4_odd_optimal (n : Nat) (hn : 3 ≤ n) (hne : n % 2 = 1) :
    ∃ f : Grid, Optimal 4 n f ∧ weight 4 n f = 2*n+1 := by
  obtain ⟨f, hf, hw⟩ := width4_odd_upper n hn hne
  refine ⟨f, ⟨hf, ?_⟩, hw⟩
  intro g hg
  have hl := even_width_odd_strict_lower (m:=4) (by omega) (by decide) hn hne hg
  omega

/-- Explicit upper bounds for the two short even circumferences. -/
theorem width4_short_upper (n : Nat) (hn : n = 4 ∨ n = 8) :
    ∃ f : Grid, Valid 4 n f ∧ weight 4 n f = (if n=4 then 9 else 18) := by
  rcases hn with rfl | rfl
  · obtain ⟨f, hf, hw, _⟩ := b4_4_exception_pack
    exact ⟨f, hf, by simpa using hw⟩
  · obtain ⟨f, hf, hw, _⟩ := b4_8_exception_pack
    exact ⟨f, hf, by simpa using hw⟩

/-- Complete exact formula for every even width at least six and every
    circumference. -/
theorem even_width_optimal (m n : Nat) (hm : 6 ≤ m) (hme : m % 2 = 0)
    (hn : 3 ≤ n) :
    ∃ f : Grid, Optimal m n f ∧ weight m n f = m*n/2 + n%2 := by
  by_cases hne : n % 2 = 0
  · obtain ⟨f, hf, hw⟩ := even_even_optimal m n hm hme hn hne
    exact ⟨f, hf, by omega⟩
  · obtain ⟨f, hf, hw⟩ := even_odd_optimal m n hm hme hn (by omega)
    exact ⟨f, hf, by omega⟩

/-- A coloring attaining the claimed width-six value for every circumference. -/
theorem width6_upper (n : Nat) (hn : 3 ≤ n) :
    ∃ f : Grid, Valid 6 n f ∧ weight 6 n f = 3*n + n%2 := by
  by_cases he : n % 2 = 0
  · obtain ⟨f, hf, hw⟩ := width6_half n hn he
    exact ⟨f, hf, by omega⟩
  · obtain ⟨f, hf, hw⟩ := even_odd_upper 6 n (by omega) (by omega) hn (by omega)
    exact ⟨f, hf, by omega⟩

/-- Complete width-six formula at every circumference. -/
theorem width6_optimal (n : Nat) (hn : 3 ≤ n) :
    ∃ f : Grid, Optimal 6 n f ∧ weight 6 n f = 3*n + n%2 := by
  by_cases he : n % 2 = 0
  · obtain ⟨f, hf, hw⟩ := width6_even_optimal n hn he
    exact ⟨f, hf, by omega⟩
  · obtain ⟨f, hf, hw⟩ := even_odd_optimal 6 n (by omega) (by omega) hn (by omega)
    exact ⟨f, hf, by omega⟩

#print axioms even_even_half_large
#print axioms even_even_half_short
#print axioms even_even_half
#print axioms even_even_optimal_large
#print axioms even_even_optimal
#print axioms width6_even_optimal
#print axioms even_odd_upper
#print axioms even_odd_optimal
#print axioms width4_odd_upper
#print axioms width4_odd_optimal
#print axioms width4_short_upper
#print axioms even_width_optimal
#print axioms width6_upper
#print axioms width6_optimal

end S3RD
