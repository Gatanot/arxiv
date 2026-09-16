import S3RD.lean.WidthThreePeriod

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace S3RD.ColorCycle

def stateA (i : Nat) : Fin 12 := ⟨(i / 12) % 12, Nat.mod_lt _ (by decide)⟩
def stateB (i : Nat) : Fin 12 := ⟨i % 12, Nat.mod_lt _ (by decide)⟩

def nextTable : List Nat := [0,0,0,0,2,1,2,2,0,1,0,1,0,0,0,2,2,1,2,0,0,1,0,0,0,0,0,1,2,1,2,0,0,1,0,0,0,11,7,0,0,0,0,0,0,0,0,0,0,0,6,0,0,0,0,0,0,0,0,0,0,9,0,0,0,0,0,0,0,0,0,0,0,0,4,0,0,0,0,0,0,0,0,0,11,0,3,0,0,0,0,0,0,0,0,0,10,0,0,0,0,0,0,0,0,0,0,0,0,5,0,0,0,0,0,0,0,0,0,0,8,0,0,0,0,0,0,0,0,0,0,0,7,3,0,0,0,0,0,0,0,0,0,0]

def nextCol (a b : Fin 12) : Fin 12 :=
  ⟨(nextTable[12*a.val+b.val]?.getD 0) % 12, Nat.mod_lt _ (by decide)⟩

abbrev PairState := Fin 12 × Fin 12
def stepPair (p : PairState) : PairState := (p.2, nextCol p.1 p.2)
def steps : Nat → PairState → PairState
  | 0, p => p
  | k+1, p => stepPair (steps k p)

def PairGood (p : PairState) := Good p.1 p.2
instance (p : PairState) : Decidable (PairGood p) := inferInstanceAs (Decidable (Good p.1 p.2))
def pairPeriod (p : PairState) := period p.1 p.2
def pairPosition (p : PairState) := position p.1 p.2

theorem step_certificate : ∀ a b : Fin 12, Good a b →
    PairGood (stepPair (a,b)) ∧ Transition a b (stepPair (a,b)).2 ∧
    pairPeriod (stepPair (a,b)) = pairPeriod (a,b) ∧
    pairPosition (stepPair (a,b)) = (pairPosition (a,b)+1) % pairPeriod (a,b) := by decide

theorem period_return : ∀ a b : Fin 12, Good a b →
    steps (pairPeriod (a,b)) (a,b) = (a,b) := by decide

theorem steps_add (a b : Nat) (p : PairState) : steps (a+b) p = steps a (steps b p) := by
  induction a generalizing p with
  | zero => simp [steps]
  | succ a ih => simp only [Nat.succ_add, steps, ih]

theorem steps_good (p : PairState) (hp : PairGood p) : ∀ k, PairGood (steps k p) := by
  intro k
  induction k with
  | zero => exact hp
  | succ k ih => exact (step_certificate _ _ ih).1

theorem steps_period_mul (p : PairState) (hp : PairGood p) (k : Nat) :
    steps (pairPeriod p*k) p = p := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Nat.mul_succ, steps_add, period_return p.1 p.2 hp, ih]

theorem steps_position (p : PairState) (hp : PairGood p) : ∀ k,
    pairPeriod (steps k p) = pairPeriod p ∧
    pairPosition (steps k p) = (pairPosition p+k) % pairPeriod p := by
  intro k
  induction k with
  | zero =>
    have hb := position_bound p.1 p.2 hp
    exact ⟨rfl, (Nat.mod_eq_of_lt hb).symm⟩
  | succ k ih =>
    have hs := step_certificate (steps k p).1 (steps k p).2 (steps_good p hp k)
    constructor
    · exact hs.2.2.1.trans ih.1
    · change pairPosition (stepPair (steps k p)) = _
      rw [hs.2.2.2, ih.1, ih.2]
      change period p.1 p.2 = 4 ∨ period p.1 p.2 = 6 at hp
      simp only [pairPeriod] at *
      rcases hp with hp | hp <;> rw [hp] <;> omega

theorem good_pair_closes_iff (p : PairState) (hp : PairGood p) (n : Nat) :
    steps n p = p ↔ n % pairPeriod p = 0 := by
  constructor
  · intro hc
    have hpos := (steps_position p hp n).2
    rw [hc] at hpos
    have hb := position_bound p.1 p.2 hp
    change period p.1 p.2 = 4 ∨ period p.1 p.2 = 6 at hp
    simp only [pairPeriod] at hpos ⊢
    rcases hp with hp | hp <;> rw [hp] at hpos hb ⊢ <;> omega
  · intro hd
    change period p.1 p.2 = 4 ∨ period p.1 p.2 = 6 at hp
    simp only [pairPeriod] at hd ⊢
    rcases hp with hp | hp
    · have hn : n = pairPeriod p * (n / pairPeriod p) := by
        simp only [pairPeriod]; rw [hp] at hd ⊢; omega
      rw [hn]
      exact steps_period_mul p (Or.inl hp) _
    · have hn : n = pairPeriod p * (n / pairPeriod p) := by
        simp only [pairPeriod]; rw [hp] at hd ⊢; omega
      rw [hn]
      exact steps_period_mul p (Or.inr hp) _

def periodPairCount (p : Nat) : Nat :=
  (List.range 144).countP fun i =>
    decide (Good (stateA i) (stateB i) ∧ period (stateA i) (stateB i) = p)

/-- Number of distinguished initial column-pairs in the certified transition
    automaton that close after `n` columns. -/
def labeledHalfCount (n : Nat) : Nat :=
  (if n % 4 = 0 then periodPairCount 4 else 0) +
  (if n % 6 = 0 then periodPairCount 6 else 0)

theorem transition_next_unique : ∀ a b c d : Fin 12,
    Good a b → Good b c → Good b d → Transition a b c → Transition a b d → c = d := by decide

theorem color_encoding_injective : ∀ q q' : Fin 12,
    (∀ r : Fin 3, color q r = color q' r) → q = q' := by decide

theorem shaped_column_unique (a b c : Nat) (ha : a ≤ 3) (hb : b ≤ 3) (hc : c ≤ 3)
    (hs : (a=0 ∧ b≠0 ∧ c=0) ∨ (a≠0 ∧ b=0 ∧ c≠0)) :
    ∃ q : Fin 12, (color q 0 = a ∧ color q 1 = b ∧ color q 2 = c) ∧
      ∀ q' : Fin 12, color q' 0 = a ∧ color q' 1 = b ∧ color q' 2 = c → q' = q := by
  obtain ⟨q, h0, h1, h2⟩ := column_encoded a b c ha hb hc hs
  refine ⟨q, ⟨h0, h1, h2⟩, ?_⟩
  intro q' hq'
  apply color_encoding_injective q' q
  intro r
  have hr : r.val=0 ∨ r.val=1 ∨ r.val=2 := by have := r.isLt; omega
  rcases hr with hr | hr | hr <;> change color q' r.val = color q r.val <;> rw [hr] <;> simp_all

theorem good_pair_count_period4 :
    periodPairCount 4 = 12 := by decide

theorem good_pair_count_period6 :
    periodPairCount 6 = 12 := by decide

/-- Proposition 7's all-circumference formula, evaluated from the same finite
    local certificate used by the arbitrary-length period proof. -/
theorem labeledHalfCount_formula (n : Nat) :
    labeledHalfCount n =
      12 * (if n % 4 = 0 then 1 else 0) +
      12 * (if n % 6 = 0 then 1 else 0) := by
  rw [labeledHalfCount, good_pair_count_period4, good_pair_count_period6]
  by_cases h4 : n % 4 = 0 <;> by_cases h6 : n % 6 = 0 <;> simp [h4, h6]

#print axioms transition_next_unique
#print axioms color_encoding_injective
#print axioms shaped_column_unique
#print axioms good_pair_closes_iff
#print axioms good_pair_count_period4
#print axioms good_pair_count_period6
#print axioms labeledHalfCount_formula

end S3RD.ColorCycle
