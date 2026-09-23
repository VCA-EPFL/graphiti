import Graphiti.Projects.AsyncFifo.components.level0.Gray

/-!
# Gray codes on `BitVec` of arbitrary width

Lemmas about the binary-reflected Gray code used by the correctness proof of an
asynchronous FIFO whose read/write pointers are `(n+1)`-bit binary counters that are
exchanged between clock domains as Gray codes, together with a few `Nat`/`BitVec`
arithmetic facts about modular counters.

Everything here is proved for arbitrary width `w` by bit-level reasoning
(`BitVec.eq_of_getLsbD_eq`, `BitVec.getLsbD_xor`, `BitVec.getLsbD_add`, `BitVec.carry`),
without `bv_decide` and without Mathlib.
-/

namespace Graphiti.AsyncFifo.Gray


/-! ### Basic bit-level facts about `gray` -/

theorem getLsbD_gray {w : Nat} (x : BitVec w) (i : Nat) :
    (gray x).getLsbD i = (x.getLsbD i ^^ x.getLsbD (i + 1)) := by
  simp only [gray, BitVec.getLsbD_xor, BitVec.getLsbD_ushiftRight, Nat.add_comm 1 i]

theorem gray_ushiftRight_one {w : Nat} (x : BitVec w) : gray x >>> 1 = gray (x >>> 1) := by
  simp only [gray, BitVec.ushiftRight_xor_distrib]

/-- `gray` commutes with `xor` (it is linear over `GF(2)`). -/
theorem gray_xor_gray {w : Nat} (a b : BitVec w) : gray a ^^^ gray b = gray (a ^^^ b) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  simp only [getLsbD_gray, BitVec.getLsbD_xor]
  generalize a.getLsbD i = p
  generalize a.getLsbD (i + 1) = q
  generalize b.getLsbD i = r
  generalize b.getLsbD (i + 1) = s
  cases p <;> cases q <;> cases r <;> cases s <;> rfl

/-! ### `ungray` inverts `gray` -/

/-- Bit `i` of `k` prefix-xor steps applied to `gray x` telescopes to `x_i ^^ x_{i+k}`. -/
theorem getLsbD_ungrayAux_gray {w : Nat} (k : Nat) (x : BitVec w) (i : Nat) :
    (ungrayAux k (gray x)).getLsbD i = (x.getLsbD i ^^ x.getLsbD (i + k)) := by
  induction k generalizing x with
  | zero => simp [ungrayAux]
  | succ k ih =>
    rw [ungrayAux, BitVec.getLsbD_xor, gray_ushiftRight_one, ih, getLsbD_gray]
    simp only [BitVec.getLsbD_ushiftRight]
    rw [show 1 + i = i + 1 by lia, show 1 + (i + k) = i + (k + 1) by lia]
    generalize x.getLsbD i = a
    generalize x.getLsbD (i + 1) = b
    generalize x.getLsbD (i + (k + 1)) = c
    cases a <;> cases b <;> cases c <;> rfl

theorem ungray_gray {w : Nat} (x : BitVec w) : ungray (gray x) = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  rw [ungray, getLsbD_ungrayAux_gray, BitVec.getLsbD_of_ge x (i + w) (by lia), Bool.xor_false]

/-! ### Consecutive Gray codes differ in exactly one bit -/

/-- Bit `i` of `x ^^^ (x + 1)`: bit `i` flips on increment iff all lower bits are one
(the carry chain). -/
theorem getLsbD_xor_add_one {w : Nat} (x : BitVec w) (i : Nat) :
    (x ^^^ (x + 1)).getLsbD i = decide (i < w ∧ ∀ j < i, x.getLsbD j = true) := by
  by_cases hi : i < w
  · rw [BitVec.getLsbD_xor, BitVec.getLsbD_add hi, ← Bool.xor_assoc, Bool.xor_self,
      Bool.false_xor]
    have h1 : (1 : BitVec w) = 1#w := rfl
    rw [h1]
    cases i with
    | zero => simp [hi]
    | succ i =>
      rw [BitVec.carry_succ_one i x (by lia)]
      simp [hi, Nat.lt_succ_iff]
  · rw [BitVec.getLsbD_of_ge _ _ (Nat.le_of_not_lt hi)]
    simp [hi]

theorem getLsbD_gray_xor_gray_add_one {w : Nat} (x : BitVec w) (i : Nat) :
    (gray x ^^^ gray (x + 1)).getLsbD i =
      (decide (i < w ∧ ∀ j < i, x.getLsbD j = true) ^^
       decide (i + 1 < w ∧ ∀ j < i + 1, x.getLsbD j = true)) := by
  rw [gray_xor_gray, getLsbD_gray, getLsbD_xor_add_one, getLsbD_xor_add_one]

/-- `gray x ^^^ gray (x + 1)` has at most one set bit. -/
theorem gray_xor_gray_add_one_atMostOne {w : Nat} (x : BitVec w) (p q : Nat)
    (hp : (gray x ^^^ gray (x + 1)).getLsbD p = true)
    (hq : (gray x ^^^ gray (x + 1)).getLsbD q = true) : p = q := by
  rw [getLsbD_gray_xor_gray_add_one] at hp hq
  -- A set bit `r` means: the low `r` bits of `x` are all one, but not the low `r+1` bits.
  have key : ∀ r, (decide (r < w ∧ ∀ j < r, x.getLsbD j = true) ^^
       decide (r + 1 < w ∧ ∀ j < r + 1, x.getLsbD j = true)) = true →
       (r < w ∧ ∀ j < r, x.getLsbD j = true) ∧ ¬ (r + 1 < w ∧ ∀ j < r + 1, x.getLsbD j = true) := by
    intro r hr
    by_cases h1 : r < w ∧ ∀ j < r, x.getLsbD j = true
    · by_cases h2 : r + 1 < w ∧ ∀ j < r + 1, x.getLsbD j = true
      · rw [decide_eq_true h1, decide_eq_true h2] at hr
        exact absurd hr (by decide)
      · exact ⟨h1, h2⟩
    · by_cases h2 : r + 1 < w ∧ ∀ j < r + 1, x.getLsbD j = true
      · exact absurd ⟨by lia, fun j hj => h2.2 j (by lia)⟩ h1
      · rw [decide_eq_false h1, decide_eq_false h2] at hr
        exact absurd hr (by decide)
  obtain ⟨⟨hpw, hpall⟩, hpnot⟩ := key p hp
  obtain ⟨⟨hqw, hqall⟩, hqnot⟩ := key q hq
  rcases Nat.lt_trichotomy p q with hlt | heq | hgt
  · exact absurd ⟨by lia, fun j hj => hqall j (by lia)⟩ hpnot
  · exact heq
  · exact absurd ⟨by lia, fun j hj => hpall j (by lia)⟩ hqnot

/-- If `a` and `b` differ in at most one bit, then choosing bitwise between `a` and `b`
yields either `a` or `b`. -/
theorem choice_of_atMostOne {w : Nat} (a b j : BitVec w)
    (hone : ∀ p q, (a ^^^ b).getLsbD p = true → (a ^^^ b).getLsbD q = true → p = q)
    (h : ∀ i, j.getLsbD i = a.getLsbD i ∨ j.getLsbD i = b.getLsbD i) :
    j = a ∨ j = b := by
  have agree : ∀ i, (a ^^^ b).getLsbD i = false → a.getLsbD i = b.getLsbD i := by
    intro i hi
    rw [BitVec.getLsbD_xor] at hi
    revert hi
    cases a.getLsbD i <;> cases b.getLsbD i <;> simp
  by_cases hex : ∃ p, (a ^^^ b).getLsbD p = true
  · obtain ⟨p, hp⟩ := hex
    have hother : ∀ i, i ≠ p → a.getLsbD i = b.getLsbD i := by
      intro i hi
      apply agree
      cases hab : (a ^^^ b).getLsbD i
      · rfl
      · exact absurd (hone i p hab hp) hi
    rcases h p with hjp | hjp
    · left
      apply BitVec.eq_of_getLsbD_eq
      intro i _
      by_cases hi : i = p
      · subst hi; exact hjp
      · rcases h i with h' | h'
        · exact h'
        · rw [h', hother i hi]
    · right
      apply BitVec.eq_of_getLsbD_eq
      intro i _
      by_cases hi : i = p
      · subst hi; exact hjp
      · rcases h i with h' | h'
        · rw [h', hother i hi]
        · exact h'
  · left
    apply BitVec.eq_of_getLsbD_eq
    intro i _
    have hab : (a ^^^ b).getLsbD i = false := by
      cases hab : (a ^^^ b).getLsbD i
      · rfl
      · exact absurd ⟨i, hab⟩ hex
    rcases h i with h' | h'
    · exact h'
    · rw [h', agree i hab]

/-- Key clock-domain-crossing lemma: if every bit of `j` agrees either with the
corresponding bit of `gray x` or with that of `gray (x + 1)` (a metastable sampler
resolving each bit independently to the old or the new value), then `j` is one of
the two whole values, because consecutive Gray codes differ in exactly one bit. -/
theorem gray_succ_choice {w : Nat} (x j : BitVec w)
    (h : ∀ i, j.getLsbD i = (gray x).getLsbD i ∨ j.getLsbD i = (gray (x + 1)).getLsbD i) :
    j = gray x ∨ j = gray (x + 1) :=
  choice_of_atMostOne (gray x) (gray (x + 1)) j (gray_xor_gray_add_one_atMostOne x) h

/-- Degenerate mixture: choosing bitwise between `a` and `a` gives `a`. -/
theorem eq_of_getLsbD_choice_same {w : Nat} (a j : BitVec w)
    (h : ∀ i, j.getLsbD i = a.getLsbD i ∨ j.getLsbD i = a.getLsbD i) : j = a := by
  apply BitVec.eq_of_getLsbD_eq
  intro i _
  rcases h i with h' | h' <;> exact h'

/-! ### Modular counter arithmetic -/

theorem ofNat_succ (w k : Nat) : BitVec.ofNat w (k + 1) = BitVec.ofNat w k + 1#w :=
  BitVec.ofNat_add k 1

/-- Comparison of counters is exact inside a window smaller than the modulus. -/
theorem ofNat_eq_ofNat_iff_of_le {w a b : Nat} (hab : b ≤ a) (hw : a - b < 2 ^ w) :
    BitVec.ofNat w a = BitVec.ofNat w b ↔ a = b := by
  constructor
  · intro h
    rw [BitVec.toNat_eq, BitVec.toNat_ofNat, BitVec.toNat_ofNat] at h
    have h2 := Nat.sub_mod_eq_zero_of_mod_eq h
    rw [Nat.mod_eq_of_lt hw] at h2
    lia
  · intro h
    rw [h]

/-- "Full" detection: with (n+1)-bit pointers and a ≥ b, a - b ≤ 2^n,
the write pointer equals the read pointer plus 2^n iff exactly 2^n items are in flight. -/
theorem ofNat_eq_add_twoPow_iff {n a b : Nat} (hab : b ≤ a) (hw : a - b ≤ 2 ^ n) :
    BitVec.ofNat (n+1) a = BitVec.ofNat (n+1) b + BitVec.ofNat (n+1) (2 ^ n) ↔ a - b = 2 ^ n := by
  rw [BitVec.ofNat_add_ofNat]
  have hpow : 2 ^ (n + 1) = 2 ^ n * 2 := Nat.pow_succ 2 n
  have hpos : 0 < 2 ^ n := Nat.two_pow_pos n
  have key := ofNat_eq_ofNat_iff_of_le (w := n + 1) (a := b + 2 ^ n) (b := a)
    (by lia) (by lia)
  constructor
  · intro h
    have := key.mp h.symm
    lia
  · intro h
    exact (key.mpr (by lia)).symm

/-- Dropping the MSB of an (n+1)-bit counter gives the n-bit address. -/
theorem setWidth_ofNat_succ (n k : Nat) : (BitVec.ofNat (n+1) k).setWidth n = BitVec.ofNat n k :=
  BitVec.setWidth_ofNat_of_le (Nat.le_succ n) k

/-- Two counter values less than 2^n apart (and distinct) give distinct n-bit addresses. -/
theorem ofNat_ne_ofNat_of_lt {n i a : Nat} (h1 : i < a) (h2 : a - i < 2 ^ n) :
    BitVec.ofNat n i ≠ BitVec.ofNat n a := by
  intro h
  have := (ofNat_eq_ofNat_iff_of_le (Nat.le_of_lt h1) h2).mp h.symm
  lia

end Graphiti.AsyncFifo.Gray
