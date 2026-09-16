import S3RD.lean.EvenWidths

namespace S3RD.WidthFourSearch

def bit (x r : Nat) : Nat := (x / 2^r) % 2
def supportWeight (x : Nat) : Nat := bit x 0 + bit x 1 + bit x 2 + bit x 3

def supportCellGood (a b c r : Nat) : Bool :=
  bit b r != 0 ||
    3 ≤ bit a r + bit c r + (if r=0 then 0 else bit b (r-1)) +
      (if r+1<4 then bit b (r+1) else 0)

def supportGood (a b c : Nat) : Bool :=
  supportCellGood a b c 0 && supportCellGood a b c 1 &&
    supportCellGood a b c 2 && supportCellGood a b c 3

def supportExtend (paths : List (List Nat)) : List (List Nat) :=
  paths.flatMap fun p =>
    (List.range 16).filterMap fun c =>
      if p.foldl (fun w x => w + supportWeight x) 0 + supportWeight c ≤ 17 then
        if supportGood (p.reverse[1]?.getD 0) (p.getLast?.getD 0) c then
          some (p ++ [c])
        else none
      else none

def supportPairs : List (List Nat) :=
  (List.range 16).flatMap fun a => (List.range 16).map fun b => [a,b]

def supportPrefixes8 : List (List Nat) :=
  supportExtend (supportExtend (supportExtend (supportExtend (supportExtend (supportExtend supportPairs)))))

def supportCloses (p : List Nat) : Bool :=
  supportGood (p.reverse[1]?.getD 0) (p.getLast?.getD 0) (p[0]?.getD 0) &&
  supportGood (p.getLast?.getD 0) (p[0]?.getD 0) (p[1]?.getD 0)

def supportCycles8 : List (List Nat) := supportPrefixes8.filter supportCloses

/-- The 68 oriented low-weight support cycles produced by the support search.
    Kept explicitly so the color certificate does not recompute the much
    larger prefix search. -/
def lowSupports : List (List Nat) := [
  [5,10,13,10,5,10,5,10], [5,10,7,10,5,10,5,10],
  [5,10,5,14,5,10,5,10], [5,10,5,11,5,10,5,10],
  [5,10,5,10,13,10,5,10], [5,10,5,10,7,10,5,10],
  [5,10,5,10,5,14,5,10], [5,10,5,10,5,11,5,10],
  [5,10,5,10,5,10,13,10], [5,10,5,10,5,10,7,10],
  [5,10,5,10,5,10,5,14], [5,10,5,10,5,10,5,11],
  [5,10,5,10,5,10,5,10], [5,11,5,10,5,10,5,10],
  [5,14,5,10,5,10,5,10], [6,9,14,9,6,9,6,9],
  [6,9,7,9,6,9,6,9], [6,9,6,13,6,9,6,9],
  [6,9,6,11,6,9,6,9], [6,9,6,9,14,9,6,9],
  [6,9,6,9,7,9,6,9], [6,9,6,9,6,13,6,9],
  [6,9,6,9,6,11,6,9], [6,9,6,9,6,9,14,9],
  [6,9,6,9,6,9,7,9], [6,9,6,9,6,9,6,13],
  [6,9,6,9,6,9,6,11], [6,9,6,9,6,9,6,9],
  [6,11,6,9,6,9,6,9], [6,13,6,9,6,9,6,9],
  [7,9,6,9,6,9,6,9], [7,10,5,10,5,10,5,10],
  [9,6,13,6,9,6,9,6], [9,6,11,6,9,6,9,6],
  [9,6,9,14,9,6,9,6], [9,6,9,7,9,6,9,6],
  [9,6,9,6,13,6,9,6], [9,6,9,6,11,6,9,6],
  [9,6,9,6,9,14,9,6], [9,6,9,6,9,7,9,6],
  [9,6,9,6,9,6,13,6], [9,6,9,6,9,6,11,6],
  [9,6,9,6,9,6,9,14], [9,6,9,6,9,6,9,7],
  [9,6,9,6,9,6,9,6], [9,7,9,6,9,6,9,6],
  [9,14,9,6,9,6,9,6], [10,5,14,5,10,5,10,5],
  [10,5,11,5,10,5,10,5], [10,5,10,13,10,5,10,5],
  [10,5,10,7,10,5,10,5], [10,5,10,5,14,5,10,5],
  [10,5,10,5,11,5,10,5], [10,5,10,5,10,13,10,5],
  [10,5,10,5,10,7,10,5], [10,5,10,5,10,5,14,5],
  [10,5,10,5,10,5,11,5], [10,5,10,5,10,5,10,13],
  [10,5,10,5,10,5,10,7], [10,5,10,5,10,5,10,5],
  [10,7,10,5,10,5,10,5], [10,13,10,5,10,5,10,5],
  [11,5,10,5,10,5,10,5], [11,6,9,6,9,6,9,6],
  [13,6,9,6,9,6,9,6], [13,10,5,10,5,10,5,10],
  [14,5,10,5,10,5,10,5], [14,9,6,9,6,9,6,9]
]

/-- Representatives modulo cyclic rotation and reflection. -/
def lowSupportRepresentatives : List (List Nat) := [
  [10,5,10,5,10,5,10,5],
  [6,9,6,9,6,9,6,9],
  [10,5,10,5,10,5,10,13],
  [10,5,10,5,10,5,10,7],
  [10,5,10,5,10,5,14,5],
  [10,5,10,5,10,5,11,5],
  [6,9,6,9,6,9,6,13],
  [6,9,6,9,6,9,6,11],
  [6,9,6,9,6,9,14,9],
  [6,9,6,9,6,9,7,9]
]

def masksOfWeight (w : Nat) : List Nat :=
  (List.range 16).filter fun s => supportWeight s=w

def weightTriplePossible (a b c : Nat) : Bool :=
  (masksOfWeight a).any fun x => (masksOfWeight b).any fun y =>
    (masksOfWeight c).any fun z => supportGood x y z

def lowWeightPatterns : List (List Nat) := [
  [2,2,2,2,2,2,2,2],
  [2,2,2,2,2,2,2,3], [2,2,2,2,2,2,3,2],
  [2,2,2,2,2,3,2,2], [2,2,2,2,3,2,2,2],
  [2,2,2,3,2,2,2,2], [2,2,3,2,2,2,2,2],
  [2,3,2,2,2,2,2,2], [3,2,2,2,2,2,2,2]
]

def weightSearchFrom (p : List Nat) : Nat → Bool
  | 0 =>
      p.foldl (fun a x => a+x) 0 > 17 ||
      p.getLast?.getD 0 + p[0]?.getD 0 < 4 ||
      !weightTriplePossible (p.reverse[1]?.getD 0) (p.getLast?.getD 0) (p[0]?.getD 0) ||
      !weightTriplePossible (p.getLast?.getD 0) (p[0]?.getD 0) (p[1]?.getD 0) ||
      lowWeightPatterns.contains p
  | k+1 => (List.range 5).all fun c =>
      p.foldl (fun a x => a+x) 0 + c > 17 ||
      p.getLast?.getD 0 + c < 4 ||
      !weightTriplePossible (p.reverse[1]?.getD 0) (p.getLast?.getD 0) c ||
      weightSearchFrom (p ++ [c]) k

def weightSearchComplete : Bool :=
  (List.range 5).all fun a => (List.range 5).all fun b =>
    a+b<4 || weightSearchFrom [a,b] 6

def supportForWeightsFrom (w p : List Nat) : Nat → Bool
  | 0 => !supportCloses p || lowSupports.contains p
  | k+1 =>
      (masksOfWeight (w[w.length-(k+1)]?.getD 0)).all fun c =>
        !supportGood (p.reverse[1]?.getD 0) (p.getLast?.getD 0) c ||
        supportForWeightsFrom w (p ++ [c]) k

def supportForWeightsComplete (w : List Nat) : Bool :=
  (masksOfWeight (w[0]?.getD 0)).all fun a =>
    (masksOfWeight (w[1]?.getD 0)).all fun b =>
      supportForWeightsFrom w [a,b] (w.length-2)

def supportSearchCompleteFrom (p : List Nat) : Nat → Bool
  | 0 =>
      supportWeight (p.getLast?.getD 0) + supportWeight (p[0]?.getD 0) < 4 ||
      !supportCloses p || lowSupports.contains p
  | k+1 => (List.range 16).all fun c =>
      17 < p.foldl (fun w x => w + supportWeight x) 0 + supportWeight c ||
      supportWeight (p.getLast?.getD 0) + supportWeight c < 4 ||
      !supportGood (p.reverse[1]?.getD 0) (p.getLast?.getD 0) c ||
      supportSearchCompleteFrom (p ++ [c]) k

def supportSearchComplete : Bool :=
  (List.range 16).all fun a => (List.range 16).all fun b =>
    supportWeight a + supportWeight b < 4 || supportSearchCompleteFrom [a,b] 6

def colorAt (x r : Nat) : Nat := (x / 4^r) % 4
def colorSupport (x : Nat) : Nat :=
  (if colorAt x 0=0 then 0 else 1) +
  (if colorAt x 1=0 then 0 else 2) +
  (if colorAt x 2=0 then 0 else 4) +
  (if colorAt x 3=0 then 0 else 8)

def colorSees (a b c r d : Nat) : Bool :=
  colorAt a r=d || colorAt c r=d ||
    (r != 0 && colorAt b (r-1)=d) ||
    (r+1<4 && colorAt b (r+1)=d)

def colorCellGood (a b c r : Nat) : Bool :=
  colorAt b r != 0 ||
    (colorSees a b c r 1 && colorSees a b c r 2 && colorSees a b c r 3)

def colorGood (a b c : Nat) : Bool :=
  colorCellGood a b c 0 && colorCellGood a b c 1 &&
    colorCellGood a b c 2 && colorCellGood a b c 3

def colorChoices (s : Nat) : List Nat := (List.range 256).filter fun c => colorSupport c=s

def colorExtend (s : Nat) (paths : List (List Nat)) : List (List Nat) :=
  paths.flatMap fun p => (colorChoices s).filterMap fun c =>
    if colorGood (p.reverse[1]?.getD 0) (p.getLast?.getD 0) c
      then some (p ++ [c]) else none

def colorCyclesFor (s : List Nat) : List (List Nat) :=
  let pairs := (colorChoices (s[0]?.getD 0)).flatMap fun a =>
    (colorChoices (s[1]?.getD 0)).map fun b => [a,b]
  let paths := colorExtend (s[7]?.getD 0)
    (colorExtend (s[6]?.getD 0)
    (colorExtend (s[5]?.getD 0)
    (colorExtend (s[4]?.getD 0)
    (colorExtend (s[3]?.getD 0)
    (colorExtend (s[2]?.getD 0) pairs)))))
  paths.filter fun p =>
    colorGood (p.reverse[1]?.getD 0) (p.getLast?.getD 0) (p[0]?.getD 0) &&
    colorGood (p.getLast?.getD 0) (p[0]?.getD 0) (p[1]?.getD 0)

/-- Allocation-free depth-first checker for the same finite color search. -/
def noColorCompletion (s : List Nat) (first second pp p : Nat) : Nat → Bool
  | 0 => !(colorGood pp p first && colorGood p first second)
  | k+1 =>
      (colorChoices (s[s.length-(k+1)]?.getD 0)).all fun c =>
        !colorGood pp p c || noColorCompletion s first second p c k

def noColorFor (s : List Nat) : Bool :=
  (colorChoices (s[0]?.getD 0)).all fun a =>
    (colorChoices (s[1]?.getD 0)).all fun b =>
      noColorCompletion s a b a b (s.length-2)

def halfSupportRepresentatives4 : List (List Nat) := [
  [5,10,5,10], [10,5,10,5], [6,9,6,9], [9,6,9,6]
]

set_option maxHeartbeats 50000000 in
set_option maxRecDepth 1000000 in
theorem low_support_color_impossible :
    lowSupports.all noColorFor = true := by decide

theorem half_support_color_impossible4 :
    halfSupportRepresentatives4.all noColorFor = true := by decide

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 1000000 in
theorem weight_patterns_complete : weightSearchComplete = true := by decide

set_option maxHeartbeats 20000000 in
set_option maxRecDepth 1000000 in
theorem support_patterns_complete :
    lowWeightPatterns.all supportForWeightsComplete = true := by decide

#print axioms low_support_color_impossible
#print axioms half_support_color_impossible4
#print axioms weight_patterns_complete
#print axioms support_patterns_complete

end S3RD.WidthFourSearch
