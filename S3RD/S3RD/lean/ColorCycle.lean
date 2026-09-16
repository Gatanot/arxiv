import S3RD.lean.Core
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
namespace S3RD.ColorCycle
def color (q : Fin 12) (r : Nat) : Nat :=
  if q.val<3 then (if r=1 then q.val+1 else 0)
  else if r=0 then (q.val-3)/3+1 else if r=2 then (q.val-3)%3+1 else 0
def Opposite (a b : Fin 12) : Prop := (a.val<3 ∧ ¬b.val<3) ∨ (¬a.val<3 ∧ b.val<3)
instance (a b : Fin 12) : Decidable (Opposite a b) :=
  inferInstanceAs (Decidable ((_ ∧ _) ∨ (_ ∧ _)))
def Transition (a b c : Fin 12) : Prop :=
  Opposite a b ∧ Opposite b c ∧ ∀r : Fin 3, color b r=0 → ∀d : Fin 3,
    color a r=d.val+1 ∨ color c r=d.val+1 ∨
    (0<r.val ∧ color b (r.val-1)=d.val+1) ∨ (r.val+1<3 ∧ color b (r.val+1)=d.val+1)
instance (a b c : Fin 12) : Decidable (Transition a b c) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ ∀_r : Fin 3, _))
def periodTable : List Nat := [0,0,0,0,0,0,0,6,4,0,4,6,0,0,0,6,0,4,0,0,0,4,0,6,0,0,0,6,4,0,4,6,0,0,0,0,0,6,6,0,0,0,0,0,0,0,0,0,0,0,4,0,0,0,0,0,0,0,0,0,0,4,0,0,0,0,0,0,0,0,0,0,0,0,4,0,0,0,0,0,0,0,0,0,6,0,6,0,0,0,0,0,0,0,0,0,4,0,0,0,0,0,0,0,0,0,0,0,0,4,0,0,0,0,0,0,0,0,0,0,4,0,0,0,0,0,0,0,0,0,0,0,6,6,0,0,0,0,0,0,0,0,0,0]
def positionTable : List Nat := [0,0,0,0,0,0,0,0,0,0,2,0,0,0,0,2,0,0,0,0,0,2,0,4,0,0,0,2,0,0,2,4,0,0,0,0,0,3,3,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,3,0,0,0,0,0,0,0,0,0,5,0,1,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0,0,0,0,0,3,0,0,0,0,0,0,0,0,0,0,3,0,0,0,0,0,0,0,0,0,0,0,5,1,0,0,0,0,0,0,0,0,0,0]
def period (a b : Fin 12) := periodTable[12*a.val+b.val]?.getD 0
def position (a b : Fin 12) := positionTable[12*a.val+b.val]?.getD 0
def Good (a b : Fin 12) : Prop := period a b=4 ∨ period a b=6
instance (a b : Fin 12) : Decidable (Good a b) := inferInstanceAs (Decidable (_ ∨ _))
theorem local_good : ∀a b c d : Fin 12, Transition a b c → Transition b c d → Good b c := by decide
theorem local_progress : ∀a b c : Fin 12, Good a b → Good b c → Transition a b c →
    period b c=period a b ∧ position b c=(position a b+1)%period a b := by decide
theorem position_bound : ∀a b : Fin 12, Good a b → position a b<period a b := by decide
#print axioms local_good
#print axioms local_progress
#print axioms position_bound
end S3RD.ColorCycle
