import S3RD.lean.ColorCycle
namespace S3RD.ColorCycle

/-- Local color rules on an arbitrary closed walk force period four or six. -/
theorem closed_walk_period (s : Nat → Fin 12) (n : Nat)
    (ht : ∀k, Transition (s k) (s (k+1)) (s (k+2)))
    (hc : ∀k, s (k+n)=s k) : n%4=0 ∨ n%6=0 := by
  have hg : ∀k, Good (s (k+1)) (s (k+2)) := by
    intro k
    exact local_good _ _ _ _ (ht k) (ht (k+1))
  let p := period (s 1) (s 2)
  let x := position (s 1) (s 2)
  have hp : p=4 ∨ p=6 := hg 0
  have hpos : x<p := position_bound _ _ (hg 0)
  have hi : ∀k, period (s (k+1)) (s (k+2))=p ∧
      position (s (k+1)) (s (k+2))=(x+k)%p := by
    intro k
    induction k with
    | zero => simp [p,x,Nat.mod_eq_of_lt hpos]
    | succ k ih =>
      have h := local_progress _ _ _ (hg k) (hg (k+1)) (ht (k+1))
      constructor
      · exact h.1.trans ih.1
      · rw [h.2,ih.1,ih.2]
        rcases hp with hp|hp <;> rw [hp] <;> omega
  have hend := (hi n).2
  have h1 : s (n+1)=s 1 := by simpa [Nat.add_comm] using hc 1
  have h2 : s (n+2)=s 2 := by simpa [Nat.add_comm] using hc 2
  rw [h1,h2] at hend
  change x=(x+n)%p at hend
  rcases hp with hp|hp
  · left; rw [hp] at hend hpos; omega
  · right; rw [hp] at hend hpos; omega

#print axioms closed_walk_period
end S3RD.ColorCycle
