-- Equation118 → Equation44373
-- Recorded verdict: false
-- Premise: x = y ◇ ((x ◇ y) ◇ y)
-- Conclusion: x ◇ y = x ◇ ((x ◇ (y ◇ x)) ◇ x)
-- Original submission SHA-256: 2e75c0dc46047c6f1ec086278b2f55ae2a352b0b7237502c271ebe143d517df4
-- Aurora-accepted correction SHA-256: b77463a3685af77867eff35495e98cb4a39d9d0491593e8b484edbb6a8cb88c4
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x = y ◇ ((x ◇ y) ◇ y)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x ◇ y = x ◇ ((x ◇ (y ◇ x)) ◇ x)
abbrev Goal : Prop := ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G
end

-- Aurora-accepted corrected submission body
                   
                             

namespace submission

set_option maxHeartbeats 0

namespace Eq118Inductive

structure PS (G : Type) where
  R : G → G → G → Prop
  r0 : ∀ {a b c d}, R a b c → R a b d → c = d
  r1 : ∀ {a b c d}, R a b c → R c b d → R b d a
  r2 : ∀ {a b c}, R a b c → R b b a → R c b b
  r3 : ∀ {a b}, R a b b → R b a b
  r4 : ∀ {a b c}, R a a b → R b a c → R a b c
  r5 : ∀ {a b c}, R a a b → R a b c → R a c a
  r6 : ∀ {a b c}, R a a b → R a b c → R c a a
  r7 : ∀ {a b c d}, R a b c → R b b a → R d a b → R a c d
  r8 : ∀ {a b c d}, R a b c → R d b c → d = a
  r9 : ∀ {a b c}, R a a b → R c a a → R b a c
  r10 : ∀ {a b c}, R a a b → R a b c → R b a c

inductive New {G : Type} (ps : PS G) (a b c : G) : G → G → G → Prop where
  | old {x y z} : ps.R x y z → New ps a b c x y z
  | link : New ps a b c a b c
  | p2 {z} : ps.R z b a → New ps a b c b c z
  | p3 : ps.R b b a → New ps a b c c b b
  | p4 : ps.R b b a → New ps a b c b a c
  | p5 : ps.R a a b → New ps a b c a c a
  | p6 : ps.R a a b → New ps a b c c a a
  | p7 {z} : ps.R b b a → ps.R z a b → New ps a b c a c z
  | p8 {z} : a = b → ps.R z b b → New ps a b c c b z
  | p9 : ps.R a a b → New ps a b c b a c

attribute [grind] New.old New.link New.p2 New.p3 New.p4 New.p5 New.p6 New.p7 New.p8 New.p9

variable {G : Type} (ps : PS G) (a b c : G)
variable (ac : a ≠ c) (bc : c ≠ b)
variable (p3 : ∀ z, ¬ ps.R a b z)
variable (p4xy : ∀ x y, ¬ ps.R x y c)
variable (p4xz : ∀ x z, ¬ ps.R x c z)
variable (p4yz : ∀ y z, ¬ ps.R c y z)

include ac bc p3 p4xy p4xz p4yz in
private theorem nr0 : ∀ {x0 x1 x2 x3}, New ps a b c x0 x1 x2 → New ps a b c x0 x1 x3 → x2 = x3 := by
  intro x0 x1 x2 x3 h k
  cases h <;> cases k <;> grind [ps.r0, ps.r4, ps.r8, ps.r10]

include ac bc p3 p4xy p4xz p4yz in
private theorem nr1 : ∀ {x0 x1 x2 x3}, New ps a b c x0 x1 x2 → New ps a b c x2 x1 x3 → New ps a b c x1 x3 x0 := by
  intro x0 x1 x2 x3 h k
  cases h <;> cases k <;> grind [ps.r0, ps.r1, ps.r3, ps.r8]

include ac bc p3 p4xy p4xz p4yz in
private theorem nr2 : ∀ {x0 x1 x2}, New ps a b c x0 x1 x2 → New ps a b c x1 x1 x0 → New ps a b c x2 x1 x1 := by
  have h1 := @nr1 G ps a b c ac bc p3 p4xy p4xz p4yz
  intro x0 x1 x2 h k
  cases h <;> cases k <;> grind [ps.r2]

include ac bc p3 p4xy p4xz p4yz in
private theorem nr3 : ∀ {x0 x1}, New ps a b c x0 x1 x1 → New ps a b c x1 x0 x1 := by
  intro x0 x1 h
  cases h <;> grind [ps.r3]

include ac bc p3 p4xy p4xz p4yz in
private theorem nr4 : ∀ {x0 x1 x2}, New ps a b c x0 x0 x1 → New ps a b c x1 x0 x2 → New ps a b c x0 x1 x2 := by
  have h1 := @nr1 G ps a b c ac bc p3 p4xy p4xz p4yz
  have h2 := @nr2 G ps a b c ac bc p3 p4xy p4xz p4yz
  intro x0 x1 x2 h k
  cases h <;> cases k <;> grind [ps.r4]

include ac bc p3 p4xy p4xz p4yz in
private theorem nr5 : ∀ {x0 x1 x2}, New ps a b c x0 x0 x1 → New ps a b c x0 x1 x2 → New ps a b c x0 x2 x0 := by
  have h1 := @nr1 G ps a b c ac bc p3 p4xy p4xz p4yz
  intro x0 x1 x2 h k
  cases h <;> cases k <;> grind [ps.r3, ps.r5]

include ac bc p3 p4xy p4xz p4yz in
private theorem nr6 : ∀ {x0 x1 x2}, New ps a b c x0 x0 x1 → New ps a b c x0 x1 x2 → New ps a b c x2 x0 x0 := by
  have h1 := @nr1 G ps a b c ac bc p3 p4xy p4xz p4yz
  have h5 := @nr5 G ps a b c ac bc p3 p4xy p4xz p4yz
  intro x0 x1 x2 h k
  cases h <;> cases k <;> grind [ps.r6]

include ac bc p3 p4xy p4xz p4yz in
private theorem nr7 : ∀ {x0 x1 x2 x3}, New ps a b c x0 x1 x2 → New ps a b c x1 x1 x0 → New ps a b c x3 x0 x1 → New ps a b c x0 x2 x3 := by
  have h1 := @nr1 G ps a b c ac bc p3 p4xy p4xz p4yz
  have h4 := @nr4 G ps a b c ac bc p3 p4xy p4xz p4yz
  intro x0 x1 x2 x3 h k l
  grind

include ac bc p3 p4xy p4xz p4yz in
private theorem nr8 : ∀ {x0 x1 x2 x3}, New ps a b c x0 x1 x2 → New ps a b c x3 x1 x2 → x3 = x0 := by
  have h0 := @nr0 G ps a b c ac bc p3 p4xy p4xz p4yz
  have h1 := @nr1 G ps a b c ac bc p3 p4xy p4xz p4yz
  have h3 := @nr3 G ps a b c ac bc p3 p4xy p4xz p4yz
  intro x0 x1 x2 x3 h k
  have H := h
  have K := k
  cases h <;> cases k <;> grind (ematch := 6) [ps.r1, ps.r5, ps.r8, ps.r9]

include ac bc p3 p4xy p4xz p4yz in
private theorem nr9 : ∀ {x0 x1 x2}, New ps a b c x0 x0 x1 → New ps a b c x2 x0 x0 → New ps a b c x1 x0 x2 := by
  have h0 := @nr0 G ps a b c ac bc p3 p4xy p4xz p4yz
  have h3 := @nr3 G ps a b c ac bc p3 p4xy p4xz p4yz
  intro x0 x1 x2 h k
  have H := h
  have K := k
  cases h <;> cases k <;> grind (ematch := 6) [ps.r0, ps.r9]

include ac bc p3 p4xy p4xz p4yz in
private theorem nr10 : ∀ {x0 x1 x2}, New ps a b c x0 x0 x1 → New ps a b c x0 x1 x2 → New ps a b c x1 x0 x2 := by
  have h6 := @nr6 G ps a b c ac bc p3 p4xy p4xz p4yz
  have h9 := @nr9 G ps a b c ac bc p3 p4xy p4xz p4yz
  intro x0 x1 x2 h k
  grind

def extended : PS G := {
    R := New ps a b c
    r0 := nr0 ps a b c ac bc p3 p4xy p4xz p4yz
    r1 := nr1 ps a b c ac bc p3 p4xy p4xz p4yz
    r2 := nr2 ps a b c ac bc p3 p4xy p4xz p4yz
    r3 := nr3 ps a b c ac bc p3 p4xy p4xz p4yz
    r4 := nr4 ps a b c ac bc p3 p4xy p4xz p4yz
    r5 := nr5 ps a b c ac bc p3 p4xy p4xz p4yz
    r6 := nr6 ps a b c ac bc p3 p4xy p4xz p4yz
    r7 := nr7 ps a b c ac bc p3 p4xy p4xz p4yz
    r8 := nr8 ps a b c ac bc p3 p4xy p4xz p4yz
    r9 := nr9 ps a b c ac bc p3 p4xy p4xz p4yz
    r10 := nr10 ps a b c ac bc p3 p4xy p4xz p4yz
  }

include ac bc p3 p4xy p4xz p4yz in
theorem adjoin : ∃ next : PS G, next.R a b c ∧ ∀ x y z, ps.R x y z → next.R x y z :=
  ⟨extended ps a b c ac bc p3 p4xy p4xz p4yz, .link, fun _ _ _ h => .old h⟩

structure BPS where
  base : PS Nat
  bound : Nat
  mem : ∀ {x y z}, base.R x y z → x < bound ∧ y < bound ∧ z < bound

private theorem new_lt {q a b c x y z : Nat} (ps : PS Nat)
    (hm : ∀ {x y z}, ps.R x y z → x < q ∧ y < q ∧ z < q)
    (hq : q < c) (ha : a < c) (hb : b < c) (h : New ps a b c x y z) :
    x < c + 1 ∧ y < c + 1 ∧ z < c + 1 := by
  cases h <;> grind

open scoped Classical in
noncomputable def BPS.add (s : BPS) (a b : Nat) : BPS :=
  if h : ∃ z, s.base.R a b z then s else
    let c := s.bound + a + b + 1
    have hq : s.bound < c := by dsimp [c]; grind
    have ha : a < c := by dsimp [c]; grind
    have hb : b < c := by dsimp [c]; grind
    have ac : a ≠ c := by grind
    have bc : c ≠ b := by grind
    have f0 : ∀ z, ¬s.base.R a b z := by simpa using h
    have f1 : ∀ x y, ¬s.base.R x y c := by
      intro x y hr
      have := s.mem hr
      grind
    have f2 : ∀ x z, ¬s.base.R x c z := by
      intro x z hr
      have := s.mem hr
      grind
    have f3 : ∀ y z, ¬s.base.R c y z := by
      intro y z hr
      have := s.mem hr
      grind
    { base := extended s.base a b c ac bc f0 f1 f2 f3
      bound := c + 1
      mem := fun hr => new_lt s.base s.mem hq ha hb hr }

theorem BPS.add_covers (s : BPS) (a b : Nat) : ∃ c, (s.add a b).base.R a b c := by
  classical
  unfold add
  split
  · assumption
  · exact ⟨_, .link⟩

theorem BPS.add_contains (s : BPS) (a b x y z : Nat) (h : s.base.R x y z) :
    (s.add a b).base.R x y z := by
  classical
  unfold add
  split
  · exact h
  · exact .old h

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
  exact (s.seq k).base.r0 hi' hj'

theorem BPS.compl_r1 (s : BPS) {x0 x1 x2 x3 : Nat}
    (h : s.compl x0 x1 x2) (k : s.compl x2 x1 x3) : s.compl x1 x3 x0 := by
  obtain ⟨i, hi⟩ := h
  obtain ⟨j, hj⟩ := k
  let n := max i j
  refine ⟨n, (s.seq n).base.r1 (s.seq_mono i n (by dsimp [n]; grind) hi)
    (s.seq_mono j n (by dsimp [n]; grind) hj)⟩

noncomputable def BPS.fun (s : BPS) (a b : Nat) : Nat :=
  (s.compl_exists a b).choose

theorem BPS.fun_spec (s : BPS) (a b : Nat) : s.compl a b (s.fun a b) :=
  (s.compl_exists a b).choose_spec

theorem BPS.fun_eq_iff (s : BPS) (a b c : Nat) : s.fun a b = c ↔ s.compl a b c := by
  constructor
  · rintro rfl
    exact s.fun_spec a b
  · exact fun h => s.compl_unique (s.fun_spec a b) h

theorem BPS.equation118 (s : BPS) (x y : Nat) :
    x = s.fun y (s.fun (s.fun x y) y) := by
  symm
  rw [s.fun_eq_iff]
  exact s.compl_r1 (s.fun_spec x y) (s.fun_spec (s.fun x y) y)

inductive SeedR : Nat → Nat → Nat → Prop where
  | r000 : SeedR 0 0 0
  | r012 : SeedR 0 1 2
  | r120 : SeedR 1 2 0
  | r201 : SeedR 2 0 1

attribute [grind] SeedR.r000 SeedR.r012 SeedR.r120 SeedR.r201

def seedPS : PS Nat where
  R := SeedR
  r0 := by intro a b c d h k; cases h <;> cases k <;> grind
  r1 := by intro a b c d h k; cases h <;> cases k <;> grind
  r2 := by intro a b c h k; cases h <;> cases k <;> grind
  r3 := by intro a b h; cases h <;> grind
  r4 := by intro a b c h k; cases h <;> cases k <;> grind
  r5 := by intro a b c h k; cases h <;> cases k <;> grind
  r6 := by intro a b c h k; cases h <;> cases k <;> grind
  r7 := by intro a b c d h k l; cases h <;> cases k <;> cases l <;> grind
  r8 := by intro a b c d h k; cases h <;> cases k <;> grind
  r9 := by intro a b c h k; cases h <;> cases k <;> grind
  r10 := by intro a b c h k; cases h <;> cases k <;> grind

def seed : BPS where
  base := seedPS
  bound := 3
  mem := by intro x y z h; cases h <;> grind

theorem seed_fun {a b c : Nat} (h : SeedR a b c) : seed.fun a b = c :=
  (seed.fun_eq_iff a b c).2 (seed.compl_of_base h)

theorem counter52118 :
    (∀ x y, x = seed.fun y (seed.fun (seed.fun x y) y)) ∧
    ¬(∀ x y, seed.fun x x = seed.fun (seed.fun (seed.fun y (seed.fun x y)) y) x) := by
  constructor
  · exact seed.equation118
  · intro h
    have bad := h 0 1
    simp only [seed_fun SeedR.r000, seed_fun SeedR.r012,
      seed_fun SeedR.r120, seed_fun SeedR.r201] at bad
    contradiction

inductive SeedR44373 : Nat → Nat → Nat → Prop where
  | r012 : SeedR44373 0 1 2
  | r021 : SeedR44373 0 2 1
  | r102 : SeedR44373 1 0 2

attribute [grind] SeedR44373.r012 SeedR44373.r021 SeedR44373.r102

def seedPS44373 : PS Nat where
  R := SeedR44373
  r0 := by intro a b c d h k; cases h <;> cases k <;> grind
  r1 := by intro a b c d h k; cases h <;> cases k <;> grind
  r2 := by intro a b c h k; cases h <;> cases k <;> grind
  r3 := by intro a b h; cases h <;> grind
  r4 := by intro a b c h k; cases h <;> cases k <;> grind
  r5 := by intro a b c h k; cases h <;> cases k <;> grind
  r6 := by intro a b c h k; cases h <;> cases k <;> grind
  r7 := by intro a b c d h k l; cases h <;> cases k <;> cases l <;> grind
  r8 := by intro a b c d h k; cases h <;> cases k <;> grind
  r9 := by intro a b c h k; cases h <;> cases k <;> grind
  r10 := by intro a b c h k; cases h <;> cases k <;> grind

def seed44373 : BPS where
  base := seedPS44373
  bound := 3
  mem := by intro x y z h; cases h <;> grind

theorem seed_fun44373 {a b c : Nat} (h : SeedR44373 a b c) : seed44373.fun a b = c :=
  (seed44373.fun_eq_iff a b c).2 (seed44373.compl_of_base h)

theorem counter44373 :
    (∀ x y, x = seed44373.fun y (seed44373.fun (seed44373.fun x y) y)) ∧
    ¬(∀ x y, seed44373.fun x y =
      seed44373.fun x (seed44373.fun (seed44373.fun x (seed44373.fun y x)) x)) := by
  constructor
  · exact seed44373.equation118
  · intro h
    have bad := h 0 1
    simp only [seed_fun44373 SeedR44373.r012, seed_fun44373 SeedR44373.r021,
      seed_fun44373 SeedR44373.r102] at bad
    contradiction

end Eq118Inductive

open Eq118Inductive

noncomputable def counterModel44373 : Magma Nat := ⟨seed44373.fun⟩

def certificate : Goal :=
  ⟨Nat, counterModel44373, counter44373.1, counter44373.2⟩


end submission

def submission : Goal := submission.certificate

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_118_to_44373 : ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G := submission
#print axioms certificate_118_to_44373
