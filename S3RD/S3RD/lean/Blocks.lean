import S3RD.lean.Assembly

set_option maxRecDepth 100000

set_option maxHeartbeats 2000000

namespace S3RD

def b4_6 : List (List Nat) := [[1,0,1,0],[0,2,0,3],[3,0,2,0],[0,1,0,1],[2,0,3,0],[0,3,0,2]]

theorem b4_6_pack : Pack 4 6 12 (fun r => ([1,0,1,0] : List Nat)[r]?.getD 0) (fun r => ([0,3,0,2] : List Nat)[r]?.getD 0) := by
  refine ⟨ofColumns b4_6, ?_⟩
  decide

theorem b4_6_half : Half 4 6 := pack_half b4_6_pack (by decide)

#print axioms b4_6_pack

def b4_10 : List (List Nat) := [[1,0,1,0],[0,2,0,3],[3,0,1,0],[0,1,0,2],[2,0,3,0],[0,1,0,1],[3,0,2,0],[0,1,0,3],[2,0,1,0],[0,3,0,2]]

theorem b4_10_pack : Pack 4 10 20 (fun r => ([1,0,1,0] : List Nat)[r]?.getD 0) (fun r => ([0,3,0,2] : List Nat)[r]?.getD 0) := by
  refine ⟨ofColumns b4_10, ?_⟩
  decide

theorem b4_10_half : Half 4 10 := pack_half b4_10_pack (by decide)

#print axioms b4_10_pack

def b4_14 : List (List Nat) := [[1,0,1,0],[0,2,0,3],[3,0,1,0],[0,1,0,2],[2,0,3,0],[0,1,0,1],[3,0,2,0],[0,1,0,3],[2,0,2,0],[0,3,0,1],[1,0,2,0],[0,3,0,3],[2,0,1,0],[0,3,0,2]]

theorem b4_14_pack : Pack 4 14 28 (fun r => ([1,0,1,0] : List Nat)[r]?.getD 0) (fun r => ([0,3,0,2] : List Nat)[r]?.getD 0) := by
  refine ⟨ofColumns b4_14, ?_⟩
  decide

theorem b4_14_half : Half 4 14 := pack_half b4_14_pack (by decide)

#print axioms b4_14_pack

def b6_6 : List (List Nat) := [[1,0,1,0,1,0],[0,2,0,3,0,2],[3,0,2,0,3,0],[0,1,0,1,0,1],[2,0,3,0,2,0],[0,3,0,2,0,3]]

theorem b6_6_pack : Pack 6 6 18 (fun r => ([1,0,1,0,1,0] : List Nat)[r]?.getD 0) (fun r => ([0,3,0,2,0,3] : List Nat)[r]?.getD 0) := by
  refine ⟨ofColumns b6_6, ?_⟩
  decide

theorem b6_6_half : Half 6 6 := pack_half b6_6_pack (by decide)

#print axioms b6_6_pack

def b6_10 : List (List Nat) := [[1,0,1,0,1,0],[0,2,0,3,0,2],[3,0,1,0,1,0],[0,1,0,2,0,3],[2,0,3,0,1,0],[0,1,0,1,0,2],[3,0,2,0,3,0],[0,1,0,1,0,1],[2,0,3,0,2,0],[0,3,0,2,0,3]]

theorem b6_10_pack : Pack 6 10 30 (fun r => ([1,0,1,0,1,0] : List Nat)[r]?.getD 0) (fun r => ([0,3,0,2,0,3] : List Nat)[r]?.getD 0) := by
  refine ⟨ofColumns b6_10, ?_⟩
  decide

theorem b6_10_half : Half 6 10 := pack_half b6_10_pack (by decide)

#print axioms b6_10_pack

def b6_14 : List (List Nat) := [[1,0,1,0,1,0],[0,2,0,3,0,2],[3,0,1,0,1,0],[0,1,0,2,0,3],[2,0,3,0,1,0],[0,1,0,1,0,2],[3,0,2,0,3,0],[0,1,0,1,0,1],[2,0,3,0,2,0],[0,1,0,1,0,3],[3,0,2,0,1,0],[0,1,0,3,0,2],[2,0,1,0,1,0],[0,3,0,2,0,3]]

theorem b6_14_pack : Pack 6 14 42 (fun r => ([1,0,1,0,1,0] : List Nat)[r]?.getD 0) (fun r => ([0,3,0,2,0,3] : List Nat)[r]?.getD 0) := by
  refine ⟨ofColumns b6_14, ?_⟩
  decide

theorem b6_14_half : Half 6 14 := pack_half b6_14_pack (by decide)

#print axioms b6_14_pack

def b5_6 : List (List Nat) := [[1,0,1,0,1],[0,2,0,3,0],[3,0,2,0,2],[0,1,0,1,0],[2,0,3,0,3],[0,3,0,2,0]]

theorem b5_6_pack : Pack 5 6 15 (fun r => ([1,0,1,0,1] : List Nat)[r]?.getD 0) (fun r => ([0,3,0,2,0] : List Nat)[r]?.getD 0) := by
  refine ⟨ofColumns b5_6, ?_⟩
  decide

theorem b5_6_half : Half 5 6 := pack_half b5_6_pack (by decide)

#print axioms b5_6_pack

def b5_8 : List (List Nat) := [[1,0,1,0,1],[0,2,0,3,0],[3,0,1,0,2],[0,2,0,3,0],[1,0,1,0,1],[0,3,0,2,0],[2,0,1,0,3],[0,3,0,2,0]]

theorem b5_8_pack : Pack 5 8 20 (fun r => ([1,0,1,0,1] : List Nat)[r]?.getD 0) (fun r => ([0,3,0,2,0] : List Nat)[r]?.getD 0) := by
  refine ⟨ofColumns b5_8, ?_⟩
  decide

theorem b5_8_half : Half 5 8 := pack_half b5_8_pack (by decide)

#print axioms b5_8_pack

def b5_10 : List (List Nat) := [[1,0,1,0,2],[0,2,0,3,0],[3,0,1,0,1],[0,1,0,2,0],[2,0,3,0,3],[0,1,0,1,0],[3,0,2,0,2],[0,1,0,3,0],[2,0,2,0,1],[0,3,0,3,0]]

theorem b5_10_pack : Pack 5 10 25 (fun r => ([1,0,1,0,2] : List Nat)[r]?.getD 0) (fun r => ([0,3,0,3,0] : List Nat)[r]?.getD 0) := by
  refine ⟨ofColumns b5_10, ?_⟩
  decide

theorem b5_10_half : Half 5 10 := pack_half b5_10_pack (by decide)

#print axioms b5_10_pack

def b7_6 : List (List Nat) := [[1,0,1,0,1,0,1],[0,2,0,2,0,3,0],[3,0,3,0,2,0,2],[0,1,0,1,0,1,0],[2,0,2,0,3,0,3],[0,3,0,3,0,2,0]]

theorem b7_6_pack : Pack 7 6 21 (fun r => ([1,0,1,0,1,0,1] : List Nat)[r]?.getD 0) (fun r => ([0,3,0,3,0,2,0] : List Nat)[r]?.getD 0) := by
  refine ⟨ofColumns b7_6, ?_⟩
  decide

theorem b7_6_half : Half 7 6 := pack_half b7_6_pack (by decide)

#print axioms b7_6_pack

def b7_10 : List (List Nat) := [[1,0,1,0,1,0,1],[0,2,0,2,0,3,0],[3,0,3,0,1,0,2],[0,1,0,2,0,1,0],[2,0,3,0,3,0,3],[0,1,0,1,0,2,0],[3,0,2,0,3,0,1],[0,1,0,3,0,2,0],[2,0,2,0,1,0,3],[0,3,0,3,0,2,0]]

theorem b7_10_pack : Pack 7 10 35 (fun r => ([1,0,1,0,1,0,1] : List Nat)[r]?.getD 0) (fun r => ([0,3,0,3,0,2,0] : List Nat)[r]?.getD 0) := by
  refine ⟨ofColumns b7_10, ?_⟩
  decide

theorem b7_10_half : Half 7 10 := pack_half b7_10_pack (by decide)

#print axioms b7_10_pack

def b7_14 : List (List Nat) := [[1,0,1,0,1,0,1],[0,2,0,2,0,3,0],[3,0,3,0,1,0,2],[0,1,0,2,0,1,0],[2,0,3,0,3,0,3],[0,1,0,1,0,2,0],[3,0,2,0,2,0,1],[0,1,0,3,0,3,0],[2,0,3,0,1,0,2],[0,1,0,2,0,3,0],[3,0,2,0,1,0,1],[0,1,0,3,0,2,0],[2,0,2,0,1,0,3],[0,3,0,3,0,2,0]]

theorem b7_14_pack : Pack 7 14 49 (fun r => ([1,0,1,0,1,0,1] : List Nat)[r]?.getD 0) (fun r => ([0,3,0,3,0,2,0] : List Nat)[r]?.getD 0) := by
  refine ⟨ofColumns b7_14, ?_⟩
  decide

theorem b7_14_half : Half 7 14 := pack_half b7_14_pack (by decide)

#print axioms b7_14_pack

def b3_4 : List (List Nat) := [[1,0,3],[0,2,0],[3,0,1],[0,2,0]]

theorem b3_4_pack : Pack 3 4 6 (fun r => ([1,0,3] : List Nat)[r]?.getD 0) (fun r => ([0,2,0] : List Nat)[r]?.getD 0) := by
  refine ⟨ofColumns b3_4, ?_⟩
  decide

theorem b3_4_half : Half 3 4 := pack_half b3_4_pack (by decide)

#print axioms b3_4_pack

def b3_8 : List (List Nat) := [[1,0,3],[0,2,0],[3,0,1],[0,2,0],[1,0,3],[0,2,0],[3,0,1],[0,2,0]]

theorem b3_8_pack : Pack 3 8 12 (fun r => ([1,0,3] : List Nat)[r]?.getD 0) (fun r => ([0,2,0] : List Nat)[r]?.getD 0) := by
  refine ⟨ofColumns b3_8, ?_⟩
  decide

theorem b3_8_half : Half 3 8 := pack_half b3_8_pack (by decide)

#print axioms b3_8_pack

def b5_4 : List (List Nat) := [[1,0,3,0,1],[0,2,0,2,0],[3,0,1,0,3],[0,2,0,2,0]]

theorem b5_4_pack : Pack 5 4 10 (fun r => ([1,0,3,0,1] : List Nat)[r]?.getD 0) (fun r => ([0,2,0,2,0] : List Nat)[r]?.getD 0) := by
  refine ⟨ofColumns b5_4, ?_⟩
  decide

theorem b5_4_half : Half 5 4 := pack_half b5_4_pack (by decide)

#print axioms b5_4_pack

def b7_4 : List (List Nat) := [[1,0,3,0,1,0,3],[0,2,0,2,0,2,0],[3,0,1,0,3,0,1],[0,2,0,2,0,2,0]]

theorem b7_4_pack : Pack 7 4 14 (fun r => ([1,0,3,0,1,0,3] : List Nat)[r]?.getD 0) (fun r => ([0,2,0,2,0,2,0] : List Nat)[r]?.getD 0) := by
  refine ⟨ofColumns b7_4, ?_⟩
  decide

theorem b7_4_half : Half 7 4 := pack_half b7_4_pack (by decide)

#print axioms b7_4_pack

def b7_8 : List (List Nat) := [[1,0,3,0,1,0,3],[0,2,0,2,0,2,0],[3,0,1,0,3,0,1],[0,2,0,2,0,2,0],[1,0,3,0,1,0,3],[0,2,0,2,0,2,0],[3,0,1,0,3,0,1],[0,2,0,2,0,2,0]]

theorem b7_8_pack : Pack 7 8 28 (fun r => ([1,0,3,0,1,0,3] : List Nat)[r]?.getD 0) (fun r => ([0,2,0,2,0,2,0] : List Nat)[r]?.getD 0) := by
  refine ⟨ofColumns b7_8, ?_⟩
  decide

theorem b7_8_half : Half 7 8 := pack_half b7_8_pack (by decide)

#print axioms b7_8_pack

/- Width-four blocks for the remaining circumference classes.  The three odd
   blocks share the endpoints of `b4_6`, so appending length-six blocks keeps
   a single extra occupied vertex. -/

def b4_3_odd : List (List Nat) := [[1,0,1,0],[2,2,0,3],[0,3,0,2]]

theorem b4_3_odd_pack : Pack 4 3 7 (fun r => ([1,0,1,0] : List Nat)[r]?.getD 0) (fun r => ([0,3,0,2] : List Nat)[r]?.getD 0) := by
  refine ⟨ofColumns b4_3_odd, ?_⟩
  decide

#print axioms b4_3_odd_pack

def b4_5_odd : List (List Nat) := [[1,0,1,0],[0,2,0,3],[3,0,1,0],[2,3,0,2],[0,3,0,2]]

theorem b4_5_odd_pack : Pack 4 5 11 (fun r => ([1,0,1,0] : List Nat)[r]?.getD 0) (fun r => ([0,3,0,2] : List Nat)[r]?.getD 0) := by
  refine ⟨ofColumns b4_5_odd, ?_⟩
  decide

#print axioms b4_5_odd_pack

def b4_7_odd : List (List Nat) := [[1,0,1,0],[2,2,0,3],[0,3,0,1],[1,0,2,0],[0,3,0,3],[2,0,1,0],[0,3,0,2]]

theorem b4_7_odd_pack : Pack 4 7 15 (fun r => ([1,0,1,0] : List Nat)[r]?.getD 0) (fun r => ([0,3,0,2] : List Nat)[r]?.getD 0) := by
  refine ⟨ofColumns b4_7_odd, ?_⟩
  decide

#print axioms b4_7_odd_pack

def b4_4_exception : List (List Nat) := [[2,0,1,0],[0,3,0,3],[1,0,2,2],[0,3,0,2]]

theorem b4_4_exception_pack : Pack 4 4 9 (fun r => ([2,0,1,0] : List Nat)[r]?.getD 0) (fun r => ([0,3,0,2] : List Nat)[r]?.getD 0) := by
  refine ⟨ofColumns b4_4_exception, ?_⟩
  decide

#print axioms b4_4_exception_pack

def b4_8_exception : List (List Nat) := [[2,0,3,0],[0,1,0,1],[3,0,2,0],[2,3,0,3],[1,0,1,1],[0,2,0,3],[3,0,1,0],[0,1,0,2]]

theorem b4_8_exception_pack : Pack 4 8 18 (fun r => ([2,0,3,0] : List Nat)[r]?.getD 0) (fun r => ([0,1,0,2] : List Nat)[r]?.getD 0) := by
  refine ⟨ofColumns b4_8_exception, ?_⟩
  decide

#print axioms b4_8_exception_pack

end S3RD
