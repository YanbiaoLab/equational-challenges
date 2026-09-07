-- Equation2856 → Equation34579
-- Recorded verdict: false
-- Premise: x = ((x ◇ (x ◇ y)) ◇ y) ◇ y
-- Conclusion: x = ((x ◇ y) ◇ ((x ◇ y) ◇ y)) ◇ y
-- Original submission SHA-256: a7b6134883bea73f7dd7e0175d54e30019944d013fa232dd18e3138d16a28520
-- Aurora-accepted correction SHA-256: 3b0ffd49bcc95bb00cbe676e1a5bb0700c0205bd4597373685878e9d0363f949
-- Generator: equational-challenges standalone v2
-- All project definitions are embedded in this file.
import Lean.Elab.Tactic.Grind

-- Embedded module: JudgeMagma.Magma
section
/- Magma class, ◇ notation, and helpers for building finite magmas. -/

class Magma (α : Type _) where
  /-- The binary magma operation, written `◇`. -/
  op : α → α → α

@[inherit_doc] infix:65 " ◇ " => Magma.op

/-- Build a `Magma (Fin n)` from a flat list of values.
    Entry at index `i*n + j` gives the result of `i ◇ j`.
    Usage: `instance : Magma (Fin 3) := magmaFin 3 [0,0,0, 0,0,0, 0,0,1]`

    Marked `@[implicit_reducible]` because Lean 4.32 requires class-valued
    definitions to be transparent to instance resolution. Deliberately not
    plain `@[reducible]`: that would unfold the table literal during general
    unification too, which is pure cost for the large `Fin n` tables here. -/
@[implicit_reducible]
def magmaFin (n : Nat) (table : List Nat) : Magma (Fin n) where
  op a b :=
    let idx := a.val * n + b.val
    ⟨table[idx]! % n, Nat.mod_lt _ (Fin.pos a)⟩
end

-- Embedded module: JudgeProblem
section
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x = ((x ◇ (x ◇ y)) ◇ y) ◇ y
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x = ((x ◇ y) ◇ ((x ◇ y) ◇ y)) ◇ y
abbrev Goal : Prop := ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G
end

-- Aurora-accepted corrected submission body
                   
                             

namespace submission

set_option maxHeartbeats 0

namespace Eq713Nat

structure PS where
  R : Nat → Nat → Nat → Prop
  fn : ∀ {a b c d}, R a b c → R a b d → c = d
  eq713 : ∀ {x y yx yxx}, R y x yx → R yx x yxx → ∃ u, R y yxx u ∧ R y u x
  law2 : ∀ {x y}, ¬ R x y y
  law3 : ∀ {x xx}, R x x xx → ∃ xxx, R xx x xxx

def u (q d : Nat) := q + 1 + d

inductive Rule (ps : PS) (q a b : Nat) where
  | old {x y z} : ps.R x y z → Rule ps q a b
  | new : Rule ps q a b
  | d1 : a = b → Rule ps q a b
  | d2 : a = b → Rule ps q a b
  | d3 : a = b → Rule ps q a b
  | d4 : a = b → Rule ps q a b
  | o1 {d} : a ≠ b → ps.R d b a → Rule ps q a b
  | o2 {d} : a ≠ b → ps.R d b a → Rule ps q a b

def Rule.x : Rule ps q a b → Nat
  | .old (x := x) _ => x | .new => a | .d1 _ => q | .d2 _ => a
  | .d3 _ => a | .d4 _ => a | .o1 (d := d) _ _ => d | .o2 (d := d) _ _ => d

def Rule.y : Rule ps q a b → Nat
  | .old (y := y) _ => y | .new => b | .d1 _ => a | .d2 _ => q + 1
  | .d3 _ => q | .d4 _ => q + 2 | .o1 _ _ => q | .o2 (d := d) _ _ => u q d

def Rule.z : Rule ps q a b → Nat
  | .old (z := z) _ => z | .new => q | .d1 _ => q + 1 | .d2 _ => q + 2
  | .d3 _ => q + 2 | .d4 _ => a | .o1 (d := d) _ _ => u q d | .o2 _ _ => b

def New (ps : PS) (q a b x y z : Nat) : Prop :=
  ∃ r : Rule ps q a b, r.x = x ∧ r.y = y ∧ r.z = z

theorem New.old {x y z} (h : ps.R x y z) : New ps q a b x y z :=
  ⟨.old h, rfl, rfl, rfl⟩
theorem New.new : New ps q a b a b q := ⟨.new, rfl, rfl, rfl⟩
theorem New.d1 (h : a = b) : New ps q a b q a (q + 1) := ⟨.d1 h, rfl, rfl, rfl⟩
theorem New.d2 (h : a = b) : New ps q a b a (q + 1) (q + 2) := ⟨.d2 h, rfl, rfl, rfl⟩
theorem New.d3 (h : a = b) : New ps q a b a q (q + 2) := ⟨.d3 h, rfl, rfl, rfl⟩
theorem New.d4 (h : a = b) : New ps q a b a (q + 2) a := ⟨.d4 h, rfl, rfl, rfl⟩
theorem New.o1 {d} (h : a ≠ b) (k : ps.R d b a) : New ps q a b d q (u q d) :=
  ⟨.o1 h k, rfl, rfl, rfl⟩
theorem New.o2 {d} (h : a ≠ b) (k : ps.R d b a) : New ps q a b d (u q d) b :=
  ⟨.o2 h k, rfl, rfl, rfl⟩

attribute [grind =>] New.old New.d1 New.d2 New.d3 New.d4 New.o1 New.o2
attribute [grind .] New.new

variable (ps : PS) (q a b : Nat)
variable (mem : ∀ {x y z}, ps.R x y z → x < q ∧ y < q ∧ z < q)
variable (ha : a < q) (hb : b < q)
variable (undef : ∀ z, ¬ ps.R a b z)

include mem ha hb undef in
private theorem nfun : ∀ {x y z w}, New ps q a b x y z → New ps q a b x y w → z = w := by
  intro x y z w h k
  obtain ⟨r, rfl, rfl, rfl⟩ := h
  obtain ⟨s, hs, ht, hz⟩ := k
  cases r <;> cases s <;> simp only [Rule.x, Rule.y, Rule.z] at hs ht hz ⊢ <;>
    grind [ps.fn, ps.law2, u]

include mem ha hb undef in
private theorem nlaw2 : ∀ {x y}, ¬ New ps q a b x y y := by
  intro x y h
  obtain ⟨r, hx, hy, hz⟩ := h
  cases r <;> simp only [Rule.x, Rule.y, Rule.z] at hx hy hz <;> grind [ps.law2, u]

include undef in
private theorem relevant_ne {d : Nat} (h : ps.R d b a) : d ≠ b := by
  intro db
  subst d
  obtain ⟨z, hz⟩ := ps.law3 h
  exact undef z hz

private theorem law3Old {x xx : Nat} (h : ps.R x x xx) :
    ∃ z, New ps q a b xx x z := by
  obtain ⟨z, hz⟩ := ps.law3 h
  exact ⟨z, .old hz⟩

private theorem law3New (ab : a = b) : ∃ z, New ps q a b q a z :=
  ⟨q + 1, .d1 ab⟩

include mem ha hb undef in
private theorem nlaw3 : ∀ {x xx}, New ps q a b x x xx → ∃ z, New ps q a b xx x z := by
  intro x xx h
  obtain ⟨r, hx, hy, hz⟩ := h
  cases r <;> simp only [Rule.x, Rule.y, Rule.z] at hx hy hz ⊢
  all_goals subst_vars
  all_goals first
    | apply law3Old <;> assumption
    | apply law3New <;> rfl
    | grind [ps.law2, u]

private theorem eqOldOld {x y yx yxx : Nat} (h : ps.R y x yx) (k : ps.R yx x yxx) :
    ∃ z, New ps q a b y yxx z ∧ New ps q a b y z x := by
  obtain ⟨z, hz, hx⟩ := ps.eq713 h k
  exact ⟨z, .old hz, .old hx⟩

private theorem eqOldNew {d : Nat} (ab : a ≠ b) (h : ps.R d b a) :
    ∃ z, New ps q a b d q z ∧ New ps q a b d z b :=
  ⟨u q d, .o1 ab h, .o2 ab h⟩

private theorem eqNewD1 (ab : a = b) :
    ∃ z, New ps q a b a (q + 1) z ∧ New ps q a b a z a :=
  by subst b; exact ⟨q + 2, .d2 rfl, .d4 rfl⟩

private theorem eqD4D4 (ab : a = b) :
    ∃ z, New ps q a b a a z ∧ New ps q a b a z (q + 2) :=
  by subst b; exact ⟨q, .new, .d3 rfl⟩

include mem ha hb undef in
private theorem neq713 : ∀ {x y yx yxx}, New ps q a b y x yx → New ps q a b yx x yxx →
    ∃ z, New ps q a b y yxx z ∧ New ps q a b y z x := by
  intro x y yx yxx h k
  obtain ⟨r, rfl, rfl, rfl⟩ := h
  obtain ⟨s, hs, ht, hz⟩ := k
  cases r <;> cases s <;> simp only [Rule.x, Rule.y, Rule.z] at hs ht hz ⊢
  all_goals subst_vars
  all_goals first
    | apply eqOldOld <;> assumption
    | apply eqOldNew <;> grind [ps.law2]
    | apply eqNewD1 <;> assumption
    | apply eqD4D4 <;> assumption
    | grind (ematch := 10) [ps.fn, ps.law2, relevant_ne, u]

def extended : PS where
  R := New ps q a b
  fn := nfun ps q a b mem ha hb undef
  eq713 := neq713 ps q a b mem ha hb undef
  law2 := nlaw2 ps q a b mem ha hb undef
  law3 := nlaw3 ps q a b mem ha hb undef

structure BPS where
  base : PS
  bound : Nat
  mem : ∀ {x y z}, base.R x y z → x < bound ∧ y < bound ∧ z < bound

private theorem new_lt {ps : PS} {q a b x y z : Nat}
    (mem : ∀ {x y z}, ps.R x y z → x < q ∧ y < q ∧ z < q)
    (ha : a < q) (hb : b < q) (h : New ps q a b x y z) :
    x < 2 * q + 3 ∧ y < 2 * q + 3 ∧ z < 2 * q + 3 := by
  obtain ⟨r, rfl, rfl, rfl⟩ := h
  cases r <;> simp only [Rule.x, Rule.y, Rule.z] <;> grind [u]

open scoped Classical in
noncomputable def BPS.add (s : BPS) (a b : Nat) : BPS :=
  if h : ∃ z, s.base.R a b z then s else
    let q := max s.bound (max a b + 1)
    have sb : s.bound ≤ q := by dsimp [q]; grind
    have ha : a < q := by dsimp [q]; grind
    have hb : b < q := by dsimp [q]; grind
    have mem : ∀ {x y z}, s.base.R x y z → x < q ∧ y < q ∧ z < q := by
      intro x y z hr
      obtain ⟨hx, hy, hz⟩ := s.mem hr
      grind
    { base := extended s.base q a b mem ha hb (by simpa using h)
      bound := 2 * q + 3
      mem := fun hr => new_lt mem ha hb hr }

theorem BPS.add_covers (s : BPS) (a b : Nat) : ∃ c, (s.add a b).base.R a b c := by
  classical
  unfold add
  split
  · assumption
  · exact ⟨_, New.new⟩

theorem BPS.add_contains (s : BPS) (a b x y z : Nat) (h : s.base.R x y z) :
    (s.add a b).base.R x y z := by
  classical
  unfold add
  split
  · exact h
  · exact New.old h

noncomputable def BPS.row (s : BPS) (a : Nat) : Nat → BPS
  | 0 => s
  | n + 1 => (row s a n).add a n

theorem BPS.row_contains (s : BPS) (a n x y z : Nat) (h : s.base.R x y z) :
    (s.row a n).base.R x y z := by
  induction n with
  | zero => exact h
  | succ n ih => exact (s.row a n).add_contains a n x y z ih

theorem BPS.row_covers (s : BPS) (a b n : Nat) (hb : b < n) :
    ∃ c, (s.row a n).base.R a b c := by
  induction n with
  | zero => grind
  | succ n ih =>
    by_cases h : b = n
    · subst b
      exact (s.row a n).add_covers a n
    · obtain ⟨c, hc⟩ := ih (by grind)
      exact ⟨c, (s.row a n).add_contains a n a b c hc⟩

noncomputable def BPS.col (s : BPS) (b : Nat) : Nat → BPS
  | 0 => s
  | n + 1 => (col s b n).add n b

theorem BPS.col_contains (s : BPS) (b n x y z : Nat) (h : s.base.R x y z) :
    (s.col b n).base.R x y z := by
  induction n with
  | zero => exact h
  | succ n ih => exact (s.col b n).add_contains n b x y z ih

theorem BPS.col_covers (s : BPS) (a b n : Nat) (ha : a < n) :
    ∃ c, (s.col b n).base.R a b c := by
  induction n with
  | zero => grind
  | succ n ih =>
    by_cases h : a = n
    · subst a
      exact (s.col b n).add_covers n b
    · obtain ⟨c, hc⟩ := ih (by grind)
      exact ⟨c, (s.col b n).add_contains n b a b c hc⟩

noncomputable def BPS.seq (s : BPS) : Nat → BPS
  | 0 => s
  | n + 1 => ((seq s n).row n (n + 1)).col n n

theorem BPS.seq_contains_succ (s : BPS) (n x y z : Nat)
    (h : (s.seq n).base.R x y z) : (s.seq (n + 1)).base.R x y z := by
  have h' := (s.seq n).row_contains n (n + 1) x y z h
  exact ((s.seq n).row n (n + 1)).col_contains n n x y z h'

theorem BPS.seq_mono (s : BPS) (i j : Nat) (hij : i ≤ j) {x y z : Nat}
    (h : (s.seq i).base.R x y z) : (s.seq j).base.R x y z := by
  induction hij with
  | refl => exact h
  | @step j _ ih => exact s.seq_contains_succ j x y z ih

theorem BPS.seq_covers (s : BPS) (a b n : Nat) (ha : a < n) (hb : b < n) :
    ∃ c, (s.seq n).base.R a b c := by
  induction n with
  | zero => grind
  | succ n ih =>
    by_cases hA : a = n
    · subst a
      obtain ⟨c, hc⟩ := (s.seq n).row_covers n b (n + 1) (by grind)
      exact ⟨c, ((s.seq n).row n (n + 1)).col_contains n n n b c hc⟩
    · by_cases hB : b = n
      · subst b
        exact ((s.seq n).row n (n + 1)).col_covers a n n (by grind)
      · obtain ⟨c, hc⟩ := ih (by grind) (by grind)
        exact ⟨c, s.seq_contains_succ n a b c hc⟩

def BPS.compl (s : BPS) (a b c : Nat) : Prop := ∃ n, (s.seq n).base.R a b c

theorem BPS.compl_of_base (s : BPS) {a b c : Nat} (h : s.base.R a b c) :
    s.compl a b c := ⟨0, h⟩

theorem BPS.compl_exists (s : BPS) (a b : Nat) : ∃ c, s.compl a b c := by
  obtain ⟨c, hc⟩ := s.seq_covers a b (max a b + 1) (by grind) (by grind)
  exact ⟨c, max a b + 1, hc⟩

theorem BPS.compl_unique (s : BPS) {a b c d : Nat}
    (hc : s.compl a b c) (hd : s.compl a b d) : c = d := by
  obtain ⟨i, hi⟩ := hc
  obtain ⟨j, hj⟩ := hd
  let k := max i j
  exact (s.seq k).base.fn
    (s.seq_mono i k (by dsimp [k]; grind) hi)
    (s.seq_mono j k (by dsimp [k]; grind) hj)

theorem BPS.compl_eq713 (s : BPS) {x y yx yxx : Nat}
    (h : s.compl y x yx) (k : s.compl yx x yxx) :
    ∃ z, s.compl y yxx z ∧ s.compl y z x := by
  obtain ⟨i, hi⟩ := h
  obtain ⟨j, hj⟩ := k
  let n := max i j
  obtain ⟨z, hz, hx⟩ := (s.seq n).base.eq713
    (s.seq_mono i n (by dsimp [n]; grind) hi)
    (s.seq_mono j n (by dsimp [n]; grind) hj)
  exact ⟨z, ⟨n, hz⟩, ⟨n, hx⟩⟩

noncomputable def BPS.op (s : BPS) (a b : Nat) : Nat := (s.compl_exists a b).choose

theorem BPS.op_spec (s : BPS) (a b : Nat) : s.compl a b (s.op a b) :=
  (s.compl_exists a b).choose_spec

theorem BPS.op_eq_iff (s : BPS) (a b c : Nat) : s.op a b = c ↔ s.compl a b c := by
  constructor
  · rintro rfl
    exact s.op_spec a b
  · exact fun h => s.compl_unique (s.op_spec a b) h

theorem BPS.equation713 (s : BPS) (x y : Nat) :
    x = s.op y (s.op y (s.op (s.op y x) x)) := by
  symm
  rw [s.op_eq_iff]
  obtain ⟨z, hz, hx⟩ := s.compl_eq713 (s.op_spec y x) (s.op_spec (s.op y x) x)
  have zeq : z = s.op y (s.op (s.op y x) x) :=
    s.compl_unique hz (s.op_spec y (s.op (s.op y x) x))
  simpa [zeq] using hx

inductive SeedR : Nat → Nat → Nat → Prop where
  | r001 : SeedR 0 0 1
  | r013 : SeedR 0 1 3
  | r102 : SeedR 1 0 2
  | r023 : SeedR 0 2 3
  | r030 : SeedR 0 3 0

def seedPS : PS where
  R := SeedR
  fn := by intro a b c d h k; cases h <;> cases k <;> grind
  eq713 := by
    intro x y yx yxx h k
    cases h <;> cases k
    · exact ⟨3, .r023, .r030⟩
    · exact ⟨1, .r001, .r013⟩
  law2 := by intro x y h; cases h <;> grind
  law3 := by
    intro x xx h
    cases h
    exact ⟨2, .r102⟩

def seed : BPS where
  base := seedPS
  bound := 4
  mem := by intro x y z h; cases h <;> grind

theorem seed_op {a b c : Nat} (h : SeedR a b c) : seed.op a b = c :=
  (seed.op_eq_iff a b c).2 (seed.compl_of_base h)

noncomputable def opp (x y : Nat) : Nat := seed.op y x

theorem equation2856 (x y : Nat) : x = opp (opp (opp x (opp x y)) y) y :=
  seed.equation713 x y

theorem notEquation34579 :
    ¬(∀ x y, x = opp (opp (opp x y) (opp (opp x y) y)) y) := by
  intro h
  have bad := h 2 0
  simp only [opp, seed_op SeedR.r023, seed_op SeedR.r030, seed_op SeedR.r001] at bad
  contradiction

end Eq713Nat

open Eq713Nat

noncomputable def counterModel713 : Magma Nat := ⟨opp⟩

def certificate : Goal := ⟨Nat, counterModel713, equation2856, notEquation34579⟩

end submission

def submission : Goal := submission.certificate

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_2856_to_34579 : ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G := submission
#print axioms certificate_2856_to_34579
