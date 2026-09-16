import S3RD.lean.WidthThree

namespace S3RD

/-- A finite path sequence bounded by two, whose zero entries have full
    neighbours on both sides, is identically one when its sum is its length. -/
theorem count_eq_one_of_flanked_zero (m : Nat) (s : Nat → Nat) (hm : 1 ≤ m)
    (hle : ∀ r, r < m → s r ≤ 2)
    (hfirst : s 0 ≠ 0) (hlast : s (m-1) ≠ 0)
    (hzero : ∀ r, r < m → s r = 0 →
      (0 < r ∧ s (r-1) = 2) ∧ (r+1 < m ∧ s (r+1) = 2))
    (hsum : count m s = m) : ∀ r, r < m → s r = 1 := by
  induction m using Nat.strongRecOn generalizing s with
  | ind m ih =>
    cases m with
    | zero => omega
    | succ k =>
      have h0le : s 0 ≤ 2 := hle 0 (by omega)
      have h0 : s 0 = 1 ∨ s 0 = 2 := by omega
      rcases h0 with h0 | h0
      · intro r hr
        by_cases hk : k = 0
        · have hr0 : r = 0 := by omega
          simpa [hr0] using h0
        · have hkpos : 1 ≤ k := by omega
          let t : Nat → Nat := fun i => s (i+1)
          have tsum : count k t = k := by
            rw [count_offset] at hsum
            change s 0 + count k t = k+1 at hsum
            omega
          have tle : ∀ i, i < k → t i ≤ 2 := by
            intro i hi
            exact hle (i+1) (by omega)
          have tfirst : t 0 ≠ 0 := by
            intro hz
            have hz' : s 1 = 0 := by simpa [t] using hz
            have hp := (hzero 1 (by omega) hz').1.2
            have hp' : s 0 = 2 := by simpa using hp
            omega
          have tlast : t (k-1) ≠ 0 := by
            simpa [t, show k-1+1=k by omega, show k+1-1=k by omega] using hlast
          have tzero : ∀ i, i < k → t i = 0 →
              (0 < i ∧ t (i-1) = 2) ∧ (i+1 < k ∧ t (i+1) = 2) := by
            intro i hi hz
            have hz' : s (i+1) = 0 := by simpa [t] using hz
            have hh := hzero (i+1) (by omega) hz'
            constructor
            · constructor
              · by_cases hi0 : i = 0
                · subst i; exact False.elim (tfirst hz)
                · omega
              · have hip : i-1+1=i := by
                  by_cases hi0 : i = 0
                  · subst i; exact False.elim (tfirst hz)
                  · omega
                simpa [t, hip] using hh.1.2
            · constructor
              · omega
              · simpa [t, Nat.add_assoc] using hh.2.2
          have tall := ih k (by omega) t hkpos tle tfirst tlast tzero tsum
          by_cases hr0 : r = 0
          · simpa [hr0] using h0
          · have := tall (r-1) (by omega)
            simpa [t, show r-1+1=r by omega] using this
      · let t : Nat → Nat := fun i => s (i+1)
        have tlower : k ≤ count k t := by
          apply pair_count_lower
          intro i hi hz
          have hh := (hzero (i+1) (by omega) (by simpa [t] using hz)).2
          exact ⟨by omega, by simpa [t, Nat.add_assoc] using hh.2⟩
        rw [count_offset] at hsum
        change s 0 + count k t = k+1 at hsum
        omega

/-- A zero horizontal pair in any row is internal and is flanked vertically by
    two full horizontal pairs. -/
theorem rowpair_zero_general {m n : Nat} {f : Grid} (hf : Valid m n f) (hn : 3 ≤ n)
    (r : Fin m) (j : Fin n) (hz : pairWeight n f r j = 0) :
    (0 < r.val ∧ pairWeight n f (r.val-1) j = 2) ∧
      (r.val+1 < m ∧ pairWeight n f (r.val+1) j = 2) := by
  have hz1 : f r j = 0 := by
    apply (occupied_eq_zero _).mp
    unfold pairWeight at hz
    omega
  have hz2 : f r (right n j) = 0 := by
    apply (occupied_eq_zero _).mp
    unfold pairWeight at hz
    omega
  have hjr : right n j < n := right_lt n j (by omega) j.isLt
  let jr : Fin n := ⟨right n j, hjr⟩
  have hleft : f r (left n (right n j)) = 0 := by
    rw [left_right n j (by omega) j.isLt]
    exact hz1
  have up1 := up_of_horizontal_zero hf r j hz1 (Or.inr hz2)
  have up2 := up_of_horizontal_zero hf r jr hz2 (Or.inl hleft)
  have dn1 := down_of_horizontal_zero hf r j hz1 (Or.inr hz2)
  have dn2 := down_of_horizontal_zero hf r jr hz2 (Or.inl hleft)
  constructor
  · refine ⟨up1.1, ?_⟩
    simp [pairWeight, occupied, up1.2, up2.2, jr]
  · refine ⟨dn1.1, ?_⟩
    simp [pairWeight, occupied, dn1.2, dn2.2, jr]

theorem pair_lower_general {m n : Nat} {f : Grid} (hf : Valid m n f) (hn : 3 ≤ n)
    (j : Fin n) : m ≤ count m (fun r => pairWeight n f r j) := by
  apply pair_count_lower
  intro r hr hz
  exact (rowpair_zero_general hf hn ⟨r, hr⟩ j hz).2

/-- General equality-support theorem: every row of a half-weight coloring
    alternates between occupied and unoccupied vertices. -/
theorem equality_support_alternating {m n : Nat} {f : Grid} (hm : 1 ≤ m)
    (hn : 3 ≤ n) (hf : Valid m n f) (hw : 2 * weight m n f = m*n) :
    ∀ r : Fin m, ∀ j : Fin n, pairWeight n f r j = 1 := by
  have hp : ∀ j, j < n → m ≤ count m (fun r => pairWeight n f r j) := by
    intro j hj
    exact pair_lower_general hf hn ⟨j, hj⟩
  have hsum : count n (fun j => count m (fun r => pairWeight n f r j)) = n*m := by
    rw [pairs_sum, hw, Nat.mul_comm]
  have heach := count_eq_const hp hsum
  intro r j
  let s : Nat → Nat := fun i => pairWeight n f i j
  have se : count m s = m := heach j j.isLt
  have sle : ∀ i, i < m → s i ≤ 2 := by
    intro i hi
    unfold s pairWeight
    have h1 := occupied_le (f i j)
    have h2 := occupied_le (f i (right n j))
    omega
  have szero : ∀ i, i < m → s i = 0 →
      (0 < i ∧ s (i-1) = 2) ∧ (i+1 < m ∧ s (i+1) = 2) := by
    intro i hi hz
    exact rowpair_zero_general hf hn ⟨i, hi⟩ j hz
  have sfirst : s 0 ≠ 0 := by
    intro hz
    have := (szero 0 (by omega) hz).1.1
    omega
  have slast : s (m-1) ≠ 0 := by
    intro hz
    have := (szero (m-1) (by omega) hz).2.1
    omega
  exact count_eq_one_of_flanked_zero m s hm sle sfirst slast szero se r r.isLt

/-- In particular, equality in the universal lower bound forces even
    circumference. -/
theorem equality_support_even_circumference {m n : Nat} {f : Grid} (hm : 1 ≤ m)
    (hn : 3 ≤ n) (hf : Valid m n f) (hw : 2 * weight m n f = m*n) : n % 2 = 0 := by
  have halt := equality_support_alternating hm hn hf hw
  have hc : count n (fun j => pairWeight n f 0 j) = n := by
    calc
      count n (fun j => pairWeight n f 0 j) = count n (fun _ => 1) := by
        apply count_congr
        intro j hj
        exact halt ⟨0, hm⟩ ⟨j, hj⟩
      _ = n := by simp [count_const]
  unfold pairWeight at hc
  rw [count_sum] at hc
  have hr := count_right n (fun j => occupied (f 0 j))
  omega

theorem occupied_eq_one (a : Nat) : occupied a = 1 ↔ a ≠ 0 := by
  unfold occupied
  split <;> simp_all

theorem top_zero_forces_down {m n : Nat} {f : Grid} (hm : 2 ≤ m) (hf : Valid m n f)
    (j : Fin n) (hz : f 0 j = 0) : f 1 j ≠ 0 := by
  intro hd
  have h1 := (hf ⟨0, by omega⟩ j).2 hz ⟨0, by decide⟩
  have h2 := (hf ⟨0, by omega⟩ j).2 hz ⟨1, by decide⟩
  have h3 := (hf ⟨0, by omega⟩ j).2 hz ⟨2, by decide⟩
  simp only [Sees] at h1 h2 h3
  grind

theorem bottom_zero_forces_up {m n : Nat} {f : Grid} (hm : 2 ≤ m) (hf : Valid m n f)
    (j : Fin n) (hz : f (m-1) j = 0) : f (m-2) j ≠ 0 := by
  intro hu
  have hr : m-1 < m := by omega
  have h1 := (hf ⟨m-1, hr⟩ j).2 hz ⟨0, by decide⟩
  have h2 := (hf ⟨m-1, hr⟩ j).2 hz ⟨1, by decide⟩
  have h3 := (hf ⟨m-1, hr⟩ j).2 hz ⟨2, by decide⟩
  simp only [Sees] at h1 h2 h3
  grind

theorem vertical_zero_triple_impossible {m n : Nat} {f : Grid} (hf : Valid m n f)
    (r : Nat) (hr : r+2 < m) (j : Fin n)
    (hu : f r j = 0) (hz : f (r+1) j = 0) (hd : f (r+2) j = 0) : False := by
  have h1 := (hf ⟨r+1, by omega⟩ j).2 hz ⟨0, by decide⟩
  have h2 := (hf ⟨r+1, by omega⟩ j).2 hz ⟨1, by decide⟩
  have h3 := (hf ⟨r+1, by omega⟩ j).2 hz ⟨2, by decide⟩
  simp only [Sees] at h1 h2 h3
  grind

/-- The remaining phase conditions from the paper equality theorem: the two
    boundary interfaces have opposite phases, and no three consecutive rows
    have the same phase. -/
theorem equality_support_phases {m n : Nat} {f : Grid} (hm : 3 ≤ m)
    (hn : 3 ≤ n) (hf : Valid m n f) (hw : 2 * weight m n f = m*n) :
    occupied (f 0 0) + occupied (f 1 0) = 1 ∧
    occupied (f (m-2) 0) + occupied (f (m-1) 0) = 1 ∧
    ∀ r, r+2 < m → ¬(occupied (f r 0) = occupied (f (r+1) 0) ∧
      occupied (f (r+1) 0) = occupied (f (r+2) 0)) := by
  have halt := equality_support_alternating (by omega) hn hf hw
  let j0 : Fin n := ⟨0, by omega⟩
  let j1 : Fin n := ⟨right n 0, right_lt n 0 (by omega) (by omega)⟩
  have hrow (r : Nat) (hr : r < m) :
      occupied (f r 0) + occupied (f r (right n 0)) = 1 :=
    halt ⟨r, hr⟩ j0
  have htop : occupied (f 0 0) + occupied (f 1 0) = 1 := by
    by_cases hz : f 0 0 = 0
    · have hd := top_zero_forces_down (m:=m) (n:=n) (f:=f) (by omega) hf j0 hz
      have hd' : f 1 0 ≠ 0 := by simpa [j0] using hd
      rw [(occupied_eq_zero _).mpr hz, (occupied_eq_one _).mpr hd']
    · have hz1 : f 0 (right n 0) = 0 := by
        have hh := hrow 0 (by omega)
        have ha : occupied (f 0 0) = 1 := (occupied_eq_one _).mpr hz
        apply (occupied_eq_zero _).mp
        omega
      have hd := top_zero_forces_down (m:=m) (n:=n) (f:=f) (by omega) hf j1 hz1
      have hd' : f 1 (right n 0) ≠ 0 := by simpa [j1] using hd
      have hh := hrow 1 (by omega)
      have ha : occupied (f 0 0) = 1 := (occupied_eq_one _).mpr hz
      have hb : occupied (f 1 (right n 0)) = 1 := (occupied_eq_one _).mpr hd'
      omega
  have hbot : occupied (f (m-2) 0) + occupied (f (m-1) 0) = 1 := by
    by_cases hz : f (m-1) 0 = 0
    · have hu := bottom_zero_forces_up (m:=m) (n:=n) (f:=f) (by omega) hf j0 hz
      have hu' : f (m-2) 0 ≠ 0 := by simpa [j0] using hu
      rw [(occupied_eq_one _).mpr hu', (occupied_eq_zero _).mpr hz]
    · have hz1 : f (m-1) (right n 0) = 0 := by
        have hh := hrow (m-1) (by omega)
        have ha : occupied (f (m-1) 0) = 1 := (occupied_eq_one _).mpr hz
        apply (occupied_eq_zero _).mp
        omega
      have hu := bottom_zero_forces_up (m:=m) (n:=n) (f:=f) (by omega) hf j1 hz1
      have hu' : f (m-2) (right n 0) ≠ 0 := by simpa [j1] using hu
      have hh := hrow (m-2) (by omega)
      have ha : occupied (f (m-1) 0) = 1 := (occupied_eq_one _).mpr hz
      have hb : occupied (f (m-2) (right n 0)) = 1 := (occupied_eq_one _).mpr hu'
      omega
  refine ⟨htop, hbot, ?_⟩
  intro r hr hsame
  by_cases hz : f (r+1) 0 = 0
  · have hu : f r 0 = 0 := by
      apply (occupied_eq_zero _).mp
      have hc : occupied (f (r+1) 0) = 0 := (occupied_eq_zero _).mpr hz
      rw [hsame.1, hc]
    have hd : f (r+2) 0 = 0 := by
      apply (occupied_eq_zero _).mp
      have hc : occupied (f (r+1) 0) = 0 := (occupied_eq_zero _).mpr hz
      rw [← hsame.2, hc]
    exact vertical_zero_triple_impossible hf r hr j0 hu hz hd
  · have hmid := hrow (r+1) (by omega)
    have hup := hrow r (by omega)
    have hdn := hrow (r+2) (by omega)
    have hc : occupied (f (r+1) 0) = 1 := (occupied_eq_one _).mpr hz
    have hcu : occupied (f r 0) = 1 := by rw [hsame.1, hc]
    have hcd : occupied (f (r+2) 0) = 1 := by rw [← hsame.2, hc]
    have zmid : f (r+1) (right n 0) = 0 := by
      apply (occupied_eq_zero _).mp
      omega
    have zup : f r (right n 0) = 0 := by
      apply (occupied_eq_zero _).mp
      omega
    have zdn : f (r+2) (right n 0) = 0 := by
      apply (occupied_eq_zero _).mp
      omega
    exact vertical_zero_triple_impossible hf r hr j1 zup zmid zdn

def SamePhase (f : Grid) (r : Nat) : Prop :=
  occupied (f r 0) = occupied (f (r+1) 0)

theorem alternating_rows_same_phase {m n : Nat} {f : Grid} (_hn : 1 ≤ n)
    (r s : Fin m)
    (hr : ∀ j : Fin n, pairWeight n f r j = 1)
    (hs : ∀ j : Fin n, pairWeight n f s j = 1)
    (h0 : occupied (f r 0) = occupied (f s 0)) :
    ∀ j : Fin n, occupied (f r j) = occupied (f s j) := by
  intro j
  have h : ∀ k, k < n → occupied (f r k) = occupied (f s k) := by
    intro k hk
    induction k with
    | zero => exact h0
    | succ k ih =>
      have hk' : k < n := by omega
      have hprev : occupied (f r k) = occupied (f s k) := ih hk'
      have hright : right n k = k+1 := by simp [right, show k+1<n by omega]
      have er : occupied (f r k) + occupied (f r (k+1)) = 1 := by
        simpa [pairWeight, hright] using hr ⟨k, hk'⟩
      have es : occupied (f s k) + occupied (f s (k+1)) = 1 := by
        simpa [pairWeight, hright] using hs ⟨k, hk'⟩
      omega
  exact h j j.isLt

/-- Formal strip-decomposition certificate.  Equal-phase interfaces join
    zero to zero (or occupied to occupied) in every column, so deleting such
    an interface removes no colored neighbour of a zero.  Boundary interfaces
    are not cuts and two cuts are never adjacent; consequently every resulting
    checkerboard strip has width at least two. -/
theorem equality_strip_decomposition {m n : Nat} {f : Grid} (hm : 3 ≤ m)
    (hn : 3 ≤ n) (hf : Valid m n f) (hw : 2 * weight m n f = m*n) :
    (∀ r, r+1 < m → SamePhase f r → ∀ j : Fin n,
      (f r j = 0 ↔ f (r+1) j = 0)) ∧
    ¬SamePhase f 0 ∧ ¬SamePhase f (m-2) ∧
    ∀ r, r+2 < m → ¬(SamePhase f r ∧ SamePhase f (r+1)) := by
  have halt := equality_support_alternating (by omega) hn hf hw
  have hp := equality_support_phases hm hn hf hw
  constructor
  · intro r hr hsame j
    have hall := alternating_rows_same_phase (m:=m) (n:=n) (f:=f) (by omega)
      ⟨r, by omega⟩ ⟨r+1, hr⟩ (halt ⟨r, by omega⟩) (halt ⟨r+1, hr⟩) hsame
    have he := hall j
    constructor <;> intro hz
    · apply (occupied_eq_zero _).mp
      rw [← he, (occupied_eq_zero _).mpr hz]
    · apply (occupied_eq_zero _).mp
      rw [he, (occupied_eq_zero _).mpr hz]
  · constructor
    · intro hs
      unfold SamePhase at hs
      simp only [Nat.zero_add] at hs
      have hb := hp.1
      have h0 := occupied_le (f 0 0)
      have h1 := occupied_le (f 1 0)
      omega
    · constructor
      · intro hs
        unfold SamePhase at hs
        have he : m-2+1=m-1 := by omega
        rw [he] at hs
        have hb := hp.2.1
        have h0 := occupied_le (f (m-2) 0)
        have h1 := occupied_le (f (m-1) 0)
        omega
      · intro r hr hs
        apply hp.2.2 r hr
        unfold SamePhase at hs
        have he : r+1+1=r+2 := by omega
        rw [he] at hs
        exact ⟨hs.1, hs.2⟩

/-- Strict lower bound for even width and odd circumference. -/
theorem even_width_odd_strict_lower {m n : Nat} {f : Grid} (hm : 1 ≤ m)
    (hme : m % 2 = 0) (hn : 3 ≤ n) (hne : n % 2 = 1) (hf : Valid m n f) :
    m*n + 2 ≤ 2 * weight m n f := by
  have hl := lower_bound hn hf
  have hp : (m*n) % 2 = 0 := by simp [Nat.mul_mod, hme]
  have hwpar : (2 * weight m n f) % 2 = 0 := by simp
  by_cases heq : 2 * weight m n f = m*n
  · have := equality_support_even_circumference hm hn hf heq
    omega
  · omega

#print axioms equality_support_alternating
#print axioms equality_support_even_circumference
#print axioms equality_support_phases
#print axioms equality_strip_decomposition
#print axioms even_width_odd_strict_lower

end S3RD
