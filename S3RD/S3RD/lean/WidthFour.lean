import S3RD.lean.WidthFourSearch

namespace S3RD
open WidthFourSearch

def encodeColumn (f : Grid) (j : Nat) : Nat :=
  f 0 j + 4*f 1 j + 16*f 2 j + 64*f 3 j

def encodeSupport (f : Grid) (j : Nat) : Nat :=
  occupied (f 0 j) + 2*occupied (f 1 j) +
    4*occupied (f 2 j) + 8*occupied (f 3 j)

theorem colorAt_encodeColumn {f : Grid} {j r : Nat} (hr : r<4)
    (hb : ∀q, q<4 → f q j≤3) : colorAt (encodeColumn f j) r = f r j := by
  have h0 := hb 0 (by omega)
  have h1 := hb 1 (by omega)
  have h2 := hb 2 (by omega)
  have h3 := hb 3 (by omega)
  have hcases : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases hcases with rfl | rfl | rfl | rfl <;>
    simp [colorAt, encodeColumn] <;> omega

theorem encodeColumn_lt {f : Grid} {j : Nat} (hb : ∀q, q<4 → f q j≤3) :
    encodeColumn f j < 256 := by
  simp [encodeColumn]
  have h0 := hb 0 (by omega)
  have h1 := hb 1 (by omega)
  have h2 := hb 2 (by omega)
  have h3 := hb 3 (by omega)
  omega

theorem colorSupport_encodeColumn {f : Grid} {j : Nat}
    (hb : ∀q, q<4 → f q j≤3) :
    colorSupport (encodeColumn f j) = encodeSupport f j := by
  have h0 := colorAt_encodeColumn (f:=f) (j:=j) (r:=0) (by omega) hb
  have h1 := colorAt_encodeColumn (f:=f) (j:=j) (r:=1) (by omega) hb
  have h2 := colorAt_encodeColumn (f:=f) (j:=j) (r:=2) (by omega) hb
  have h3 := colorAt_encodeColumn (f:=f) (j:=j) (r:=3) (by omega) hb
  by_cases z0 : f 0 j=0 <;> by_cases z1 : f 1 j=0 <;>
    by_cases z2 : f 2 j=0 <;> by_cases z3 : f 3 j=0 <;>
    simp [colorSupport, encodeSupport, occupied, h0, h1, h2, h3, z0, z1, z2, z3]

theorem supportWeight_encodeSupport (f : Grid) (j : Nat) :
    supportWeight (encodeSupport f j) =
      occupied (f 0 j) + occupied (f 1 j) +
        occupied (f 2 j) + occupied (f 3 j) := by
  have h0 := occupied_le (f 0 j)
  have h1 := occupied_le (f 1 j)
  have h2 := occupied_le (f 2 j)
  have h3 := occupied_le (f 3 j)
  simp [supportWeight, bit, encodeSupport]
  omega

theorem encodeSupport_lt (f : Grid) (j : Nat) : encodeSupport f j < 16 := by
  have h0 := occupied_le (f 0 j)
  have h1 := occupied_le (f 1 j)
  have h2 := occupied_le (f 2 j)
  have h3 := occupied_le (f 3 j)
  simp [encodeSupport]
  omega

theorem weightTriplePossible_of_support {a b c : Nat}
    (ha : a<16) (hb : b<16) (hc : c<16) (hg : supportGood a b c=true) :
    weightTriplePossible (supportWeight a) (supportWeight b) (supportWeight c)=true := by
  simp only [weightTriplePossible, List.any_eq_true]
  refine ⟨a, ?_, ⟨b, ?_, ⟨c, ?_, hg⟩⟩⟩
  · simp [masksOfWeight, ha]
  · simp [masksOfWeight, hb]
  · simp [masksOfWeight, hc]

theorem encodeColumn_mem_choices {f : Grid} {j : Nat}
    (hb : ∀q, q<4 → f q j≤3) :
    encodeColumn f j ∈ colorChoices (encodeSupport f j) := by
  simp [colorChoices, encodeColumn_lt hb, colorSupport_encodeColumn hb]

theorem bit_encodeSupport {f : Grid} {j r : Nat} (hr : r<4) :
    bit (encodeSupport f j) r = occupied (f r j) := by
  have h0 := occupied_le (f 0 j)
  have h1 := occupied_le (f 1 j)
  have h2 := occupied_le (f 2 j)
  have h3 := occupied_le (f 3 j)
  have hcases : r=0 ∨ r=1 ∨ r=2 ∨ r=3 := by omega
  rcases hcases with rfl | rfl | rfl | rfl <;>
    simp [bit, encodeSupport] <;> omega

theorem colorGood_encode_of_valid {n : Nat} {f : Grid} (hn : 3≤n)
    (hf : Valid 4 n f) (j : Nat) (hj : j<n) :
    colorGood (encodeColumn f (left n j)) (encodeColumn f j)
      (encodeColumn f (right n j)) = true := by
  have hleft : left n j<n := left_lt n j (by omega) hj
  have hright : right n j<n := right_lt n j (by omega) hj
  have hb (k q : Nat) (hk : k<n) (hq : q<4) : f q k≤3 :=
    (hf ⟨q,hq⟩ ⟨k,hk⟩).1
  have hd (k q : Nat) (hk : k<n) (hq : q<4) :
      colorAt (encodeColumn f k) q=f q k :=
    colorAt_encodeColumn hq (fun t ht => hb k t hk ht)
  have cell (r : Nat) (hr : r<4) :
      colorCellGood (encodeColumn f (left n j)) (encodeColumn f j)
        (encodeColumn f (right n j)) r = true := by
    by_cases hz : f r j=0
    · have h1 := (hf ⟨r,hr⟩ ⟨j,hj⟩).2 hz ⟨0,by decide⟩
      have h2 := (hf ⟨r,hr⟩ ⟨j,hj⟩).2 hz ⟨1,by decide⟩
      have h3 := (hf ⟨r,hr⟩ ⟨j,hj⟩).2 hz ⟨2,by decide⟩
      simp only [Sees] at h1 h2 h3
      simp [colorCellGood, colorSees, hd _ _ hleft hr, hd _ _ hj hr,
        hd _ _ hright hr, hz]
      grind
    · simp [colorCellGood, hd _ _ hj hr, hz]
  simp [colorGood, cell 0 (by omega), cell 1 (by omega),
    cell 2 (by omega), cell 3 (by omega)]

theorem colorGood_encode_of_valid8 {f : Grid} (hf : Valid 4 8 f)
    (j : Nat) (hj : j<8) :
    colorGood (encodeColumn f (left 8 j)) (encodeColumn f j)
      (encodeColumn f (right 8 j)) = true :=
  colorGood_encode_of_valid (by omega) hf j hj

theorem supportGood_encode_of_valid8 {f : Grid} (hf : Valid 4 8 f)
    (j : Nat) (hj : j<8) :
    supportGood (encodeSupport f (left 8 j)) (encodeSupport f j)
      (encodeSupport f (right 8 j)) = true := by
  have hleft : left 8 j<8 := left_lt 8 j (by omega) hj
  have hright : right 8 j<8 := right_lt 8 j (by omega) hj
  have cell (r : Nat) (hr : r<4) :
      supportCellGood (encodeSupport f (left 8 j)) (encodeSupport f j)
        (encodeSupport f (right 8 j)) r = true := by
    have hbc := bit_encodeSupport (f:=f) (j:=j) hr
    have hbl := bit_encodeSupport (f:=f) (j:=left 8 j) hr
    have hbr := bit_encodeSupport (f:=f) (j:=right 8 j) hr
    have hup : (if r=0 then 0 else bit (encodeSupport f j) (r-1)) =
        occupied (if r=0 then 0 else f (r-1) j) := by
      by_cases h : r=0
      · simp [h, occupied]
      · have hh : r-1<4 := by omega
        simp [h, bit_encodeSupport (f:=f) (j:=j) hh]
    have hdown : (if r+1<4 then bit (encodeSupport f j) (r+1) else 0) =
        occupied (if r+1<4 then f (r+1) j else 0) := by
      by_cases h : r+1<4
      · simp [h, bit_encodeSupport (f:=f) (j:=j) h]
      · simp [h, occupied]
    by_cases hz : f r j=0
    · have h1 := (hf ⟨r,hr⟩ ⟨j,hj⟩).2 hz ⟨0,by decide⟩
      have h2 := (hf ⟨r,hr⟩ ⟨j,hj⟩).2 hz ⟨1,by decide⟩
      have h3 := (hf ⟨r,hr⟩ ⟨j,hj⟩).2 hz ⟨2,by decide⟩
      simp only [Sees] at h1 h2 h3
      unfold supportCellGood
      rw [hbc, hbl, hbr, hup, hdown]
      simp [occupied, hz]
      grind (splits := 20)
    · unfold supportCellGood
      rw [hbc]
      simp [occupied, hz]
  simp [supportGood, cell 0 (by omega), cell 1 (by omega),
    cell 2 (by omega), cell 3 (by omega)]

def supportSequence8 (f : Grid) : List Nat :=
  [encodeSupport f 0, encodeSupport f 1, encodeSupport f 2, encodeSupport f 3,
   encodeSupport f 4, encodeSupport f 5, encodeSupport f 6, encodeSupport f 7]

theorem supportSequence8_weight (f : Grid) :
    (supportSequence8 f).foldl (fun a x => a + supportWeight x) 0 = weight 4 8 f := by
  simp [supportSequence8, supportWeight_encodeSupport, weight, count]
  omega

theorem adjacent_column_lower8 {f : Grid} (hf : Valid 4 8 f)
    (j : Nat) (hj : j<8) :
    4 ≤ supportWeight (encodeSupport f j) +
      supportWeight (encodeSupport f (right 8 j)) := by
  have hp : 4 ≤ count 4 (fun r =>
      occupied (f r j) + occupied (f r (right 8 j))) := by
    apply pair_count_lower
    intro r hr hz
    have hjr : right 8 j<8 := right_lt 8 j (by omega) hj
    have hz1 : f r j=0 := by
      unfold occupied at hz
      split at hz <;> omega
    have hz2 : f r (right 8 j)=0 := by
      unfold occupied at hz
      split at hz <;> split at hz <;> omega
    have hd1 := down_of_horizontal_zero hf ⟨r,hr⟩ ⟨j,hj⟩ hz1 (Or.inr hz2)
    have hleft : f r (left 8 (right 8 j))=0 := by
      rw [left_right 8 j (by omega) hj]
      exact hz1
    have hd2 := down_of_horizontal_zero hf ⟨r,hr⟩
      ⟨right 8 j,hjr⟩ hz2 (Or.inl hleft)
    exact ⟨hd1.1, by simp [occupied, hd1.2, hd2.2]⟩
  simp [count] at hp
  rw [supportWeight_encodeSupport, supportWeight_encodeSupport]
  omega

theorem weightSearch_step {p : List Nat} {k c : Nat}
    (h : weightSearchFrom p (k+1)=true) (hc : c<5)
    (hs : p.foldl (fun a x => a+x) 0 + c ≤ 17)
    (hp : 4≤p.getLast?.getD 0+c)
    (ht : weightTriplePossible (p.reverse[1]?.getD 0) (p.getLast?.getD 0) c=true) :
    weightSearchFrom (p++[c]) k=true := by
  simp only [weightSearchFrom] at h
  have hx := List.all_eq_true.mp h c (by simp [hc])
  simp only [Bool.or_eq_true, decide_eq_true_eq] at hx
  rcases hx with ((hbad | hbad) | hbad) | hx
  · omega
  · omega
  · simp_all
  · exact hx

theorem weightSearch_finish {p : List Nat}
    (h : weightSearchFrom p 0=true)
    (hs : p.foldl (fun a x => a+x) 0 ≤ 17)
    (hp : 4≤p.getLast?.getD 0+p[0]?.getD 0)
    (ht1 : weightTriplePossible (p.reverse[1]?.getD 0) (p.getLast?.getD 0)
      (p[0]?.getD 0)=true)
    (ht2 : weightTriplePossible (p.getLast?.getD 0) (p[0]?.getD 0)
      (p[1]?.getD 0)=true) : lowWeightPatterns.contains p=true := by
  simp only [weightSearchFrom, Bool.or_eq_true, decide_eq_true_eq] at h
  rcases h with (((hbad | hbad) | hbad) | hbad) | h
  · omega
  · omega
  · simp_all
  · simp_all
  · exact h

theorem weightPattern_of_cycle (w0 w1 w2 w3 w4 w5 w6 w7 : Nat)
    (hb0 : w0<5) (hb1 : w1<5) (hb2 : w2<5) (hb3 : w3<5)
    (hb4 : w4<5) (hb5 : w5<5) (hb6 : w6<5) (hb7 : w7<5)
    (hp01 : 4≤w0+w1) (hp12 : 4≤w1+w2) (hp23 : 4≤w2+w3)
    (hp34 : 4≤w3+w4) (hp45 : 4≤w4+w5) (hp56 : 4≤w5+w6)
    (hp67 : 4≤w6+w7) (hp70 : 4≤w7+w0)
    (ht012 : weightTriplePossible w0 w1 w2=true)
    (ht123 : weightTriplePossible w1 w2 w3=true)
    (ht234 : weightTriplePossible w2 w3 w4=true)
    (ht345 : weightTriplePossible w3 w4 w5=true)
    (ht456 : weightTriplePossible w4 w5 w6=true)
    (ht567 : weightTriplePossible w5 w6 w7=true)
    (ht670 : weightTriplePossible w6 w7 w0=true)
    (ht701 : weightTriplePossible w7 w0 w1=true)
    (hsum : w0+w1+w2+w3+w4+w5+w6+w7≤17) :
    [w0,w1,w2,w3,w4,w5,w6,w7] ∈ lowWeightPatterns := by
  have h0 := List.all_eq_true.mp weight_patterns_complete w0 (by simp [hb0])
  have h1 := List.all_eq_true.mp h0 w1 (by simp [hb1])
  simp only [Bool.or_eq_true, decide_eq_true_eq] at h1
  rcases h1 with hbad | h1
  · omega
  have h2 := weightSearch_step h1 hb2 (by simp; omega) (by simpa) (by simpa using ht012)
  have h3 := weightSearch_step h2 hb3 (by simp; omega) (by simpa) (by simpa using ht123)
  have h4 := weightSearch_step h3 hb4 (by simp; omega) (by simpa) (by simpa using ht234)
  have h5 := weightSearch_step h4 hb5 (by simp; omega) (by simpa) (by simpa using ht345)
  have h6 := weightSearch_step h5 hb6 (by simp; omega) (by simpa) (by simpa using ht456)
  have h7 := weightSearch_step h6 hb7 (by simp; omega) (by simpa) (by simpa using ht567)
  have hc := weightSearch_finish h7 (by simp; omega) (by simpa)
    (by simpa using ht670) (by simpa using ht701)
  simpa using hc

theorem supportForWeights_step {w p : List Nat} {k c : Nat}
    (h : supportForWeightsFrom w p (k+1)=true)
    (hc : c ∈ masksOfWeight (w[w.length-(k+1)]?.getD 0))
    (hg : supportGood (p.reverse[1]?.getD 0) (p.getLast?.getD 0) c=true) :
    supportForWeightsFrom w (p++[c]) k=true := by
  simp only [supportForWeightsFrom] at h
  have hx := List.all_eq_true.mp h c hc
  simp [hg] at hx
  exact hx

theorem supportForWeights_finish {w p : List Nat}
    (h : supportForWeightsFrom w p 0=true) (hc : supportCloses p=true) :
    lowSupports.contains p=true := by
  simp [supportForWeightsFrom, hc] at h
  exact List.contains_iff_mem.mpr h

theorem lowSupport_of_pattern
    (s0 s1 s2 s3 s4 s5 s6 s7 : Nat)
    (hs0 : s0<16) (hs1 : s1<16) (hs2 : s2<16) (hs3 : s3<16)
    (hs4 : s4<16) (hs5 : s5<16) (hs6 : s6<16) (hs7 : s7<16)
    (hw : [supportWeight s0,supportWeight s1,supportWeight s2,supportWeight s3,
      supportWeight s4,supportWeight s5,supportWeight s6,supportWeight s7] ∈
        lowWeightPatterns)
    (hg012 : supportGood s0 s1 s2=true) (hg123 : supportGood s1 s2 s3=true)
    (hg234 : supportGood s2 s3 s4=true) (hg345 : supportGood s3 s4 s5=true)
    (hg456 : supportGood s4 s5 s6=true) (hg567 : supportGood s5 s6 s7=true)
    (hg670 : supportGood s6 s7 s0=true) (hg701 : supportGood s7 s0 s1=true) :
    [s0,s1,s2,s3,s4,s5,s6,s7] ∈ lowSupports := by
  have hall := List.all_eq_true.mp support_patterns_complete _ hw
  unfold supportForWeightsComplete at hall
  have h0 := List.all_eq_true.mp hall s0 (by simp [masksOfWeight,hs0])
  have h1 := List.all_eq_true.mp h0 s1 (by simp [masksOfWeight,hs1])
  have h2 := supportForWeights_step h1 (by simp [masksOfWeight,hs2]) hg012
  have h3 := supportForWeights_step h2 (by simp [masksOfWeight,hs3]) hg123
  have h4 := supportForWeights_step h3 (by simp [masksOfWeight,hs4]) hg234
  have h5 := supportForWeights_step h4 (by simp [masksOfWeight,hs5]) hg345
  have h6 := supportForWeights_step h5 (by simp [masksOfWeight,hs6]) hg456
  have h7 := supportForWeights_step h6 (by simp [masksOfWeight,hs7]) hg567
  apply List.contains_iff_mem.mp
  apply supportForWeights_finish h7
  simp [supportCloses,hg670,hg701]

theorem noColorCompletion_step {s : List Nat} {first second pp p : Nat} {k c : Nat}
    (h : noColorCompletion s first second pp p (k+1)=true)
    (hc : c ∈ colorChoices (s[s.length-(k+1)]?.getD 0))
    (hg : colorGood pp p c=true) :
    noColorCompletion s first second p c k=true := by
  simp only [noColorCompletion] at h
  have hx := List.all_eq_true.mp h c hc
  simp [hg] at hx
  exact hx

theorem noColorFor_contradiction {s : List Nat} {c0 c1 c2 c3 c4 c5 c6 c7 : Nat}
    (hn : noColorFor s=true)
    (hs : s=[colorSupport c0,colorSupport c1,colorSupport c2,colorSupport c3,
      colorSupport c4,colorSupport c5,colorSupport c6,colorSupport c7])
    (hg012 : colorGood c0 c1 c2=true) (hg123 : colorGood c1 c2 c3=true)
    (hg234 : colorGood c2 c3 c4=true) (hg345 : colorGood c3 c4 c5=true)
    (hg456 : colorGood c4 c5 c6=true) (hg567 : colorGood c5 c6 c7=true)
    (hg670 : colorGood c6 c7 c0=true) (hg701 : colorGood c7 c0 c1=true)
    (hb0 : c0<256) (hb1 : c1<256) (hb2 : c2<256) (hb3 : c3<256)
    (hb4 : c4<256) (hb5 : c5<256) (hb6 : c6<256) (hb7 : c7<256) : False := by
  have choice (c : Nat) (hc : c<256) : c ∈ colorChoices (colorSupport c) := by
    simp [colorChoices,hc]
  unfold noColorFor at hn
  have h0 := List.all_eq_true.mp hn c0 (by simpa [hs] using choice c0 hb0)
  have h1 := List.all_eq_true.mp h0 c1 (by simpa [hs] using choice c1 hb1)
  simp [hs] at h1
  have h2 := noColorCompletion_step h1 (by simpa [hs] using choice c2 hb2) hg012
  have h3 := noColorCompletion_step h2 (by simpa [hs] using choice c3 hb3) hg123
  have h4 := noColorCompletion_step h3 (by simpa [hs] using choice c4 hb4) hg234
  have h5 := noColorCompletion_step h4 (by simpa [hs] using choice c5 hb5) hg345
  have h6 := noColorCompletion_step h5 (by simpa [hs] using choice c6 hb6) hg456
  have h7 := noColorCompletion_step h6 (by simpa [hs] using choice c7 hb7) hg567
  simp [noColorCompletion,hg670,hg701] at h7

def supportSequence4 (f : Grid) : List Nat :=
  [encodeSupport f 0, encodeSupport f 1, encodeSupport f 2, encodeSupport f 3]

set_option maxHeartbeats 2000000 in
theorem half_support_sequence4 {f : Grid} (hf : Valid 4 4 f)
    (hw : 2 * weight 4 4 f = 4*4) :
    supportSequence4 f ∈ halfSupportRepresentatives4 := by
  have ha := equality_support_alternating (m:=4) (n:=4) (f:=f)
    (by omega) (by omega) hf hw
  have hp := equality_support_phases (m:=4) (n:=4) (f:=f)
    (by omega) (by omega) hf hw
  simp at hp
  have hrow (r : Nat) (hr : r<4) :
      occupied (f r 0) + occupied (f r 1) = 1 ∧
      occupied (f r 1) + occupied (f r 2) = 1 ∧
      occupied (f r 2) + occupied (f r 3) = 1 := by
    have h0 := ha ⟨r,hr⟩ ⟨0,by omega⟩
    have h1 := ha ⟨r,hr⟩ ⟨1,by omega⟩
    have h2 := ha ⟨r,hr⟩ ⟨2,by omega⟩
    simpa [pairWeight, right] using And.intro h0 (And.intro h1 h2)
  have h0 := hrow 0 (by omega)
  have h1 := hrow 1 (by omega)
  have h2 := hrow 2 (by omega)
  have h3 := hrow 3 (by omega)
  have a0 := occupied_le (f 0 0)
  have a1 := occupied_le (f 1 0)
  have a2 := occupied_le (f 2 0)
  have a3 := occupied_le (f 3 0)
  have hcases :
      (occupied (f 0 0)=0 ∧ occupied (f 1 0)=1 ∧
        occupied (f 2 0)=0 ∧ occupied (f 3 0)=1) ∨
      (occupied (f 0 0)=0 ∧ occupied (f 1 0)=1 ∧
        occupied (f 2 0)=1 ∧ occupied (f 3 0)=0) ∨
      (occupied (f 0 0)=1 ∧ occupied (f 1 0)=0 ∧
        occupied (f 2 0)=0 ∧ occupied (f 3 0)=1) ∨
      (occupied (f 0 0)=1 ∧ occupied (f 1 0)=0 ∧
        occupied (f 2 0)=1 ∧ occupied (f 3 0)=0) := by
    omega
  rcases hcases with hc | hc | hc | hc <;>
    simp [halfSupportRepresentatives4, supportSequence4, encodeSupport] <;> omega

theorem width4_four_lower {f : Grid} (hf : Valid 4 4 f) : 9 ≤ weight 4 4 f := by
  by_cases hnot : 9 ≤ weight 4 4 f
  · exact hnot
  · exfalso
    have hl := lower_bound (m:=4) (n:=4) (f:=f) (by omega) hf
    have hw : 2 * weight 4 4 f = 4*4 := by omega
    have hs := half_support_sequence4 hf hw
    have hall := List.all_eq_true.mp half_support_color_impossible4
    have hno := hall (supportSequence4 f) hs
    have hb (j q : Nat) (hj : j<4) (hq : q<4) : f q j≤3 :=
      (hf ⟨q,hq⟩ ⟨j,hj⟩).1
    have hc0 := encodeColumn_mem_choices (f:=f) (j:=0) (fun q hq => hb 0 q (by omega) hq)
    have hc1 := encodeColumn_mem_choices (f:=f) (j:=1) (fun q hq => hb 1 q (by omega) hq)
    have hc2 := encodeColumn_mem_choices (f:=f) (j:=2) (fun q hq => hb 2 q (by omega) hq)
    have hc3 := encodeColumn_mem_choices (f:=f) (j:=3) (fun q hq => hb 3 q (by omega) hq)
    have g0 := colorGood_encode_of_valid (n:=4) (by omega) hf 0 (by omega)
    have g1 := colorGood_encode_of_valid (n:=4) (by omega) hf 1 (by omega)
    have g2 := colorGood_encode_of_valid (n:=4) (by omega) hf 2 (by omega)
    have g3 := colorGood_encode_of_valid (n:=4) (by omega) hf 3 (by omega)
    simp [left, right] at g0 g1 g2 g3
    unfold noColorFor at hno
    have h0 := (List.all_eq_true.mp hno) (encodeColumn f 0) (by
      simpa [supportSequence4] using hc0)
    have h1 := (List.all_eq_true.mp h0) (encodeColumn f 1) (by
      simpa [supportSequence4] using hc1)
    change noColorCompletion (supportSequence4 f) (encodeColumn f 0)
      (encodeColumn f 1) (encodeColumn f 0) (encodeColumn f 1) 2 = true at h1
    simp only [noColorCompletion] at h1
    have h2 := (List.all_eq_true.mp h1) (encodeColumn f 2) (by
      simpa [supportSequence4] using hc2)
    simp [g1] at h2
    have h3 := h2 (encodeColumn f 3) (by
      simpa [supportSequence4] using hc3)
    simp [g0, g2, g3] at h3

theorem width4_four_optimal :
    ∃ f : Grid, Optimal 4 4 f ∧ weight 4 4 f = 9 := by
  obtain ⟨f, hf, hw⟩ := width4_short_upper 4 (Or.inl rfl)
  have hw' : weight 4 4 f=9 := by simpa using hw
  refine ⟨f, ⟨hf, ?_⟩, hw'⟩
  intro g hg
  have hl := width4_four_lower hg
  omega

theorem supportWeight_encodeSupport_lt (f : Grid) (j : Nat) :
    supportWeight (encodeSupport f j)<5 := by
  rw [supportWeight_encodeSupport]
  have h0 := occupied_le (f 0 j)
  have h1 := occupied_le (f 1 j)
  have h2 := occupied_le (f 2 j)
  have h3 := occupied_le (f 3 j)
  omega

theorem width4_eight_lower {f : Grid} (hf : Valid 4 8 f) : 18 ≤ weight 4 8 f := by
  by_cases hbound : 18 ≤ weight 4 8 f
  · exact hbound
  · have hwtotal : weight 4 8 f ≤ 17 := by omega
    let s := fun j => encodeSupport f j
    let c := fun j => encodeColumn f j
    have hb (j q : Nat) (hj : j<8) (hq : q<4) : f q j≤3 :=
      (hf ⟨q,hq⟩ ⟨j,hj⟩).1
    have hslt (j : Nat) : s j<16 := encodeSupport_lt f j
    have hwlt (j : Nat) : supportWeight (s j)<5 := supportWeight_encodeSupport_lt f j
    have sg0 : supportGood (s 7) (s 0) (s 1)=true := by
      simpa [s, left, right] using supportGood_encode_of_valid8 hf 0 (by omega)
    have sg1 : supportGood (s 0) (s 1) (s 2)=true := by
      simpa [s, left, right] using supportGood_encode_of_valid8 hf 1 (by omega)
    have sg2 : supportGood (s 1) (s 2) (s 3)=true := by
      simpa [s, left, right] using supportGood_encode_of_valid8 hf 2 (by omega)
    have sg3 : supportGood (s 2) (s 3) (s 4)=true := by
      simpa [s, left, right] using supportGood_encode_of_valid8 hf 3 (by omega)
    have sg4 : supportGood (s 3) (s 4) (s 5)=true := by
      simpa [s, left, right] using supportGood_encode_of_valid8 hf 4 (by omega)
    have sg5 : supportGood (s 4) (s 5) (s 6)=true := by
      simpa [s, left, right] using supportGood_encode_of_valid8 hf 5 (by omega)
    have sg6 : supportGood (s 5) (s 6) (s 7)=true := by
      simpa [s, left, right] using supportGood_encode_of_valid8 hf 6 (by omega)
    have sg7 : supportGood (s 6) (s 7) (s 0)=true := by
      simpa [s, left, right] using supportGood_encode_of_valid8 hf 7 (by omega)
    have tp0 := weightTriplePossible_of_support (hslt 7) (hslt 0) (hslt 1) sg0
    have tp1 := weightTriplePossible_of_support (hslt 0) (hslt 1) (hslt 2) sg1
    have tp2 := weightTriplePossible_of_support (hslt 1) (hslt 2) (hslt 3) sg2
    have tp3 := weightTriplePossible_of_support (hslt 2) (hslt 3) (hslt 4) sg3
    have tp4 := weightTriplePossible_of_support (hslt 3) (hslt 4) (hslt 5) sg4
    have tp5 := weightTriplePossible_of_support (hslt 4) (hslt 5) (hslt 6) sg5
    have tp6 := weightTriplePossible_of_support (hslt 5) (hslt 6) (hslt 7) sg6
    have tp7 := weightTriplePossible_of_support (hslt 6) (hslt 7) (hslt 0) sg7
    have pair0 := adjacent_column_lower8 hf 0 (by omega)
    have pair1 := adjacent_column_lower8 hf 1 (by omega)
    have pair2 := adjacent_column_lower8 hf 2 (by omega)
    have pair3 := adjacent_column_lower8 hf 3 (by omega)
    have pair4 := adjacent_column_lower8 hf 4 (by omega)
    have pair5 := adjacent_column_lower8 hf 5 (by omega)
    have pair6 := adjacent_column_lower8 hf 6 (by omega)
    have pair7 := adjacent_column_lower8 hf 7 (by omega)
    simp [s, right] at pair0 pair1 pair2 pair3 pair4 pair5 pair6 pair7
    have hsum : supportWeight (s 0)+supportWeight (s 1)+supportWeight (s 2)+
        supportWeight (s 3)+supportWeight (s 4)+supportWeight (s 5)+
        supportWeight (s 6)+supportWeight (s 7)≤17 := by
      have hweight := supportSequence8_weight f
      dsimp [supportSequence8, s] at hweight ⊢
      omega
    have hwp := weightPattern_of_cycle
      (supportWeight (s 0)) (supportWeight (s 1)) (supportWeight (s 2))
      (supportWeight (s 3)) (supportWeight (s 4)) (supportWeight (s 5))
      (supportWeight (s 6)) (supportWeight (s 7))
      (hwlt 0) (hwlt 1) (hwlt 2) (hwlt 3) (hwlt 4) (hwlt 5) (hwlt 6) (hwlt 7)
      pair0 pair1 pair2 pair3 pair4 pair5 pair6 pair7
      tp1 tp2 tp3 tp4 tp5 tp6 tp7 tp0 hsum
    have hsupport := lowSupport_of_pattern (s 0) (s 1) (s 2) (s 3)
      (s 4) (s 5) (s 6) (s 7) (hslt 0) (hslt 1) (hslt 2) (hslt 3)
      (hslt 4) (hslt 5) (hslt 6) (hslt 7) hwp sg1 sg2 sg3 sg4 sg5 sg6 sg7 sg0
    have hn := List.all_eq_true.mp low_support_color_impossible _ hsupport
    have cg0 : colorGood (c 7) (c 0) (c 1)=true := by
      simpa [c, left, right] using colorGood_encode_of_valid8 hf 0 (by omega)
    have cg1 : colorGood (c 0) (c 1) (c 2)=true := by
      simpa [c, left, right] using colorGood_encode_of_valid8 hf 1 (by omega)
    have cg2 : colorGood (c 1) (c 2) (c 3)=true := by
      simpa [c, left, right] using colorGood_encode_of_valid8 hf 2 (by omega)
    have cg3 : colorGood (c 2) (c 3) (c 4)=true := by
      simpa [c, left, right] using colorGood_encode_of_valid8 hf 3 (by omega)
    have cg4 : colorGood (c 3) (c 4) (c 5)=true := by
      simpa [c, left, right] using colorGood_encode_of_valid8 hf 4 (by omega)
    have cg5 : colorGood (c 4) (c 5) (c 6)=true := by
      simpa [c, left, right] using colorGood_encode_of_valid8 hf 5 (by omega)
    have cg6 : colorGood (c 5) (c 6) (c 7)=true := by
      simpa [c, left, right] using colorGood_encode_of_valid8 hf 6 (by omega)
    have cg7 : colorGood (c 6) (c 7) (c 0)=true := by
      simpa [c, left, right] using colorGood_encode_of_valid8 hf 7 (by omega)
    have cblt (j : Nat) (hj : j<8) : c j<256 :=
      encodeColumn_lt (fun q hq => hb j q hj hq)
    exfalso
    apply noColorFor_contradiction hn
      (c0:=c 0) (c1:=c 1) (c2:=c 2) (c3:=c 3)
      (c4:=c 4) (c5:=c 5) (c6:=c 6) (c7:=c 7)
    · simp [s, c, colorSupport_encodeColumn (fun q hq => hb 0 q (by omega) hq),
        colorSupport_encodeColumn (fun q hq => hb 1 q (by omega) hq),
        colorSupport_encodeColumn (fun q hq => hb 2 q (by omega) hq),
        colorSupport_encodeColumn (fun q hq => hb 3 q (by omega) hq),
        colorSupport_encodeColumn (fun q hq => hb 4 q (by omega) hq),
        colorSupport_encodeColumn (fun q hq => hb 5 q (by omega) hq),
        colorSupport_encodeColumn (fun q hq => hb 6 q (by omega) hq),
        colorSupport_encodeColumn (fun q hq => hb 7 q (by omega) hq)]
    · exact cg1
    · exact cg2
    · exact cg3
    · exact cg4
    · exact cg5
    · exact cg6
    · exact cg7
    · exact cg0
    · exact cblt 0 (by omega)
    · exact cblt 1 (by omega)
    · exact cblt 2 (by omega)
    · exact cblt 3 (by omega)
    · exact cblt 4 (by omega)
    · exact cblt 5 (by omega)
    · exact cblt 6 (by omega)
    · exact cblt 7 (by omega)
  
theorem width4_eight_optimal :
    ∃ f : Grid, Optimal 4 8 f ∧ weight 4 8 f = 18 := by
  obtain ⟨f, hf, hw⟩ := width4_short_upper 8 (Or.inr rfl)
  have hw' : weight 4 8 f=18 := by simpa using hw
  refine ⟨f, ⟨hf, ?_⟩, hw'⟩
  intro g hg
  have hl := width4_eight_lower hg
  omega

#print axioms colorAt_encodeColumn
#print axioms encodeColumn_lt
#print axioms colorSupport_encodeColumn
#print axioms supportWeight_encodeSupport
#print axioms encodeSupport_lt
#print axioms weightTriplePossible_of_support
#print axioms encodeColumn_mem_choices
#print axioms bit_encodeSupport
#print axioms colorGood_encode_of_valid
#print axioms colorGood_encode_of_valid8
#print axioms supportGood_encode_of_valid8
#print axioms supportSequence8_weight
#print axioms adjacent_column_lower8
#print axioms half_support_sequence4
#print axioms width4_four_lower
#print axioms width4_four_optimal
#print axioms weightPattern_of_cycle
#print axioms lowSupport_of_pattern
#print axioms noColorFor_contradiction
#print axioms width4_eight_lower
#print axioms width4_eight_optimal

end S3RD
