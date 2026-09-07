-- Equation1076 → Equation60478
-- Recorded verdict: false
-- Premise: x = y ◇ ((x ◇ (x ◇ y)) ◇ y)
-- Conclusion: (x ◇ y) ◇ z = (x ◇ y) ◇ (z ◇ z)
-- Original submission SHA-256: e7597b8ea5562119a5b2498a34b2ced5056c365ca9d53c74af1afa5310c4e402
-- Aurora-accepted correction SHA-256: e8dfabab198243757e952568e20eae0d76e6833d4faba8dda306a6803eed12da
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x = y ◇ ((x ◇ (x ◇ y)) ◇ y)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), (x ◇ y) ◇ z = (x ◇ y) ◇ (z ◇ z)
abbrev Goal : Prop := ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G
end

-- Aurora-accepted corrected submission body
                   
                             

namespace submission

set_option maxHeartbeats 0

namespace Eq1076Nat

structure PS where
  R : Nat → Nat → Nat → Prop
  fn : ∀ {a b c d}, R a b c → R a b d → c = d
  law : ∀ {x y xy xxy}, R x y xy → R x xy xxy → ∃ u, R xxy y u ∧ R y u x
  ni : ∀ {x}, ¬ R x x x

def u (q d : Nat) := q + 1 + d
def v (q d : Nat) := 2 * q + 1 + d

inductive Rule (ps : PS) (q a b : Nat) where
  | old {x y z} : ps.R x y z → Rule ps q a b
  | new : Rule ps q a b
  | e1 {d} : ps.R a d b → Rule ps q a b
  | e2 {d} : ps.R a d b → Rule ps q a b
  | e31 {d e} : ps.R a d b → d ≠ e → ps.R d a e → Rule ps q a b
  | e32 {d e} : ps.R a d b → d ≠ e → ps.R d a e → Rule ps q a b
  | e41 {d} : ps.R a d b → ps.R d a d → Rule ps q a b
  | e42 {d} : ps.R a d b → ps.R d a d → Rule ps q a b

def Rule.x : Rule ps q a b → Nat
  | .old (x := x) _ => x | .new => a | .e1 _ => q | .e2 (d := d) _ => d
  | .e31 (d := d) _ _ _ => u q d | .e32 (e := e) _ _ _ => e
  | .e41 (d := d) _ _ => u q d | .e42 (d := d) _ _ => d

def Rule.y : Rule ps q a b → Nat
  | .old (y := y) _ => y | .new => b | .e1 (d := d) _ => d | .e2 (d := d) _ => u q d
  | .e31 (d := d) _ _ _ => v q d | .e32 (d := d) _ _ _ => u q d
  | .e41 _ _ => a | .e42 (d := d) _ _ => u q d

def Rule.z : Rule ps q a b → Nat
  | .old (z := z) _ => z | .new => q | .e1 (d := d) _ => u q d | .e2 _ => a
  | .e31 (d := d) _ _ _ => d | .e32 (d := d) _ _ _ => v q d
  | .e41 (d := d) _ _ => d | .e42 _ _ => a

def New (ps : PS) (q a b x y z : Nat) : Prop :=
  ∃ r : Rule ps q a b, r.x = x ∧ r.y = y ∧ r.z = z

theorem New.old {x y z} (h : ps.R x y z) : New ps q a b x y z :=
  ⟨.old h, rfl, rfl, rfl⟩
theorem New.new : New ps q a b a b q := ⟨.new, rfl, rfl, rfl⟩
theorem New.e1 {d} (h : ps.R a d b) : New ps q a b q d (u q d) :=
  ⟨.e1 h, rfl, rfl, rfl⟩
theorem New.e2 {d} (h : ps.R a d b) : New ps q a b d (u q d) a :=
  ⟨.e2 h, rfl, rfl, rfl⟩
theorem New.e31 {d e} (h : ps.R a d b) (hne : d ≠ e) (k : ps.R d a e) :
    New ps q a b (u q d) (v q d) d := ⟨.e31 h hne k, rfl, rfl, rfl⟩
theorem New.e32 {d e} (h : ps.R a d b) (hne : d ≠ e) (k : ps.R d a e) :
    New ps q a b e (u q d) (v q d) := ⟨.e32 h hne k, rfl, rfl, rfl⟩
theorem New.e41 {d} (h : ps.R a d b) (k : ps.R d a d) :
    New ps q a b (u q d) a d := ⟨.e41 h k, rfl, rfl, rfl⟩
theorem New.e42 {d} (h : ps.R a d b) (k : ps.R d a d) :
    New ps q a b d (u q d) a := ⟨.e42 h k, rfl, rfl, rfl⟩

attribute [grind =>] New.old New.e1 New.e2 New.e31 New.e32 New.e41 New.e42
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
    grind [ps.fn, ps.ni, u, v]

include mem ha hb undef in
private theorem nni : ∀ {x}, ¬ New ps q a b x x x := by
  intro x h
  obtain ⟨r, hx, hy, hz⟩ := h
  cases r <;> simp only [Rule.x, Rule.y, Rule.z] at hx hy hz <;> grind [ps.ni, u, v]

private theorem lawOldOld {x y xy xxy : Nat} (h : ps.R x y xy) (k : ps.R x xy xxy) :
    ∃ z, New ps q a b xxy y z ∧ New ps q a b y z x := by
  obtain ⟨z, hz, hx⟩ := ps.law h k
  exact ⟨z, .old hz, .old hx⟩

private theorem lawOldNew {d : Nat} (h : ps.R a d b) :
    ∃ z, New ps q a b q d z ∧ New ps q a b d z a :=
  ⟨u q d, .e1 h, .e2 h⟩

private theorem lawE2Old {d e : Nat} (h : ps.R a d b) (k : ps.R d a e) :
    ∃ z, New ps q a b e (u q d) z ∧ New ps q a b (u q d) z d := by
  by_cases de : d = e
  · subst e
    exact ⟨a, .e2 h, .e41 h k⟩
  · exact ⟨v q d, .e32 h de k, .e31 h de k⟩

include mem ha hb undef in
private theorem nlaw : ∀ {x y xy xxy}, New ps q a b x y xy → New ps q a b x xy xxy →
    ∃ z, New ps q a b xxy y z ∧ New ps q a b y z x := by
  intro x y xy xxy h k
  obtain ⟨r, rfl, rfl, rfl⟩ := h
  obtain ⟨s, hs, ht, hz⟩ := k
  cases r <;> cases s <;> simp only [Rule.x, Rule.y, Rule.z] at hs ht hz ⊢
  all_goals subst_vars
  all_goals first
    | apply lawOldOld <;> assumption
    | apply lawOldNew <;> assumption
    | apply lawE2Old <;> assumption
    | grind (ematch := 10) [ps.fn, ps.ni, u, v]

def extended : PS where
  R := New ps q a b
  fn := nfun ps q a b mem ha hb undef
  law := nlaw ps q a b mem ha hb undef
  ni := nni ps q a b mem ha hb undef

structure BPS where
  base : PS
  bound : Nat
  mem : ∀ {x y z}, base.R x y z → x < bound ∧ y < bound ∧ z < bound

private theorem new_lt {ps : PS} {q a b x y z : Nat}
    (mem : ∀ {x y z}, ps.R x y z → x < q ∧ y < q ∧ z < q)
    (ha : a < q) (hb : b < q) (h : New ps q a b x y z) :
    x < 3 * q + 1 ∧ y < 3 * q + 1 ∧ z < 3 * q + 1 := by
  obtain ⟨r, rfl, rfl, rfl⟩ := h
  cases r <;> simp only [Rule.x, Rule.y, Rule.z] <;> grind [u, v]

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
      bound := 3 * q + 1
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

def BPS.compl (s : BPS) (a b c : Nat) : Prop :=
  ∃ n, (s.seq n).base.R a b c

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
  have hi' := s.seq_mono i k (by dsimp [k]; grind) hi
  have hj' := s.seq_mono j k (by dsimp [k]; grind) hj
  exact (s.seq k).base.fn hi' hj'

theorem BPS.compl_law (s : BPS) {x y xy xxy : Nat}
    (h : s.compl x y xy) (k : s.compl x xy xxy) :
    ∃ z, s.compl xxy y z ∧ s.compl y z x := by
  obtain ⟨i, hi⟩ := h
  obtain ⟨j, hj⟩ := k
  let n := max i j
  obtain ⟨z, hz, hx⟩ := (s.seq n).base.law
    (s.seq_mono i n (by dsimp [n]; grind) hi)
    (s.seq_mono j n (by dsimp [n]; grind) hj)
  exact ⟨z, ⟨n, hz⟩, ⟨n, hx⟩⟩

noncomputable def BPS.op (s : BPS) (a b : Nat) : Nat :=
  (s.compl_exists a b).choose

theorem BPS.op_spec (s : BPS) (a b : Nat) : s.compl a b (s.op a b) :=
  (s.compl_exists a b).choose_spec

theorem BPS.op_eq_iff (s : BPS) (a b c : Nat) : s.op a b = c ↔ s.compl a b c := by
  constructor
  · rintro rfl
    exact s.op_spec a b
  · exact fun h => s.compl_unique (s.op_spec a b) h

theorem BPS.equation1076 (s : BPS) (x y : Nat) :
    x = s.op y (s.op (s.op x (s.op x y)) y) := by
  symm
  rw [s.op_eq_iff]
  obtain ⟨z, hz, hx⟩ := s.compl_law (s.op_spec x y) (s.op_spec x (s.op x y))
  have zeq : z = s.op (s.op x (s.op x y)) y :=
    s.compl_unique hz (s.op_spec (s.op x (s.op x y)) y)
  simpa [zeq] using hx

inductive SeedR : Nat → Nat → Nat → Prop where
  | r001 : SeedR 0 0 1
  | r012 : SeedR 0 1 2
  | r030 : SeedR 0 3 0
  | r101 : SeedR 1 0 1
  | r131 : SeedR 1 3 1
  | r203 : SeedR 2 0 3
  | r310 : SeedR 3 1 0

attribute [grind .] SeedR.r001 SeedR.r012 SeedR.r030 SeedR.r101 SeedR.r131 SeedR.r203 SeedR.r310

def seedPS : PS where
  R := SeedR
  fn := by intro a b c d h k; cases h <;> cases k <;> grind
  law := by
    intro x y xy xxy h k
    cases h <;> cases k
    · exact ⟨3, .r203, .r030⟩
    · exact ⟨1, .r131, .r310⟩
  ni := by intro x h; cases h <;> grind

def seed : BPS where
  base := seedPS
  bound := 4
  mem := by intro x y z h; cases h <;> grind

theorem seed_op {a b c : Nat} (h : SeedR a b c) : seed.op a b = c :=
  (seed.op_eq_iff a b c).2 (seed.compl_of_base h)

theorem counter :
    (∀ x y, x = seed.op y (seed.op (seed.op x (seed.op x y)) y)) ∧
    ¬(∀ x y z, seed.op (seed.op x y) z = seed.op (seed.op x y) (seed.op z z)) := by
  constructor
  · exact seed.equation1076
  · intro h
    have bad := h 0 3 0
    simp only [seed_op SeedR.r030, seed_op SeedR.r001, seed_op SeedR.r012] at bad
    contradiction

end Eq1076Nat

open Eq1076Nat

noncomputable def counterModel1076 : Magma Nat := ⟨seed.op⟩

def certificate : Goal := ⟨Nat, counterModel1076, seed.equation1076, counter.2⟩

end submission

def submission : Goal := submission.certificate

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_1076_to_60478 : ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G := submission
#print axioms certificate_1076_to_60478
