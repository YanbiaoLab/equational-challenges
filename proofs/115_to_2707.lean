-- Equation115 → Equation2707
-- Recorded verdict: false
-- Premise: x = y ◇ ((x ◇ x) ◇ y)
-- Conclusion: x = ((y ◇ x) ◇ (y ◇ x)) ◇ y
-- Original submission SHA-256: aed917edd93da567c504f1fcf2cffd9f58994f96f9d4b9a3783b8f65bbd2e407
-- Aurora-accepted correction SHA-256: 17114775421dd2dc957d7afa72d0d7eb5959d696619bcf3ec1d556a0090d23b2
-- Generator: equational-challenges standalone v2
-- All project definitions are embedded in this file.
import Mathlib.Tactic

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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x = y ◇ ((x ◇ x) ◇ y)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x = ((y ◇ x) ◇ (y ◇ x)) ◇ y
abbrev Goal : Prop := ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G
end

-- Aurora-accepted corrected submission body
                   
                     

set_option maxHeartbeats 0

namespace submission

inductive T where
  | leaf (n : Nat)
  | fork (x y : T)
  deriving DecidableEq

open T

def q1 : T → Option T
  | (fork (y₁) (((fork (((fork (x₁) (x₂)))) (y₂))))) =>
      if y₁ = y₂ ∧ x₁ = x₂ then some x₁ else none
  | _ => none

def q2 : T → Option T
  | (fork (((fork (((fork (y₁) (y₂)))) (((fork (x₁) (x₂))))))) (y₃)) =>
      if y₁ = y₂ ∧ x₁ = x₂ ∧ y₁ = y₃ then some x₁ else none
  | _ => none

def r (t : T) : T := (q2 t).getD ((q1 t).getD t)

def Normal : T → Prop
  | leaf _ => True
  | (fork (x) (y)) => Normal x ∧ Normal y ∧ r ((fork (x) (y))) = (fork (x) (y))

theorem q1_closed {x y z : T} (hx : Normal x) (hy : Normal y)
    (h : q1 ((fork (x) (y))) = some z) : Normal z := by
  cases y with
  | leaf n => simp [q1] at h
  | fork p y₂ =>
    cases p with
    | leaf n => simp [q1] at h
    | fork x₁ x₂ =>
      simp only [q1] at h
      split at h
      · injection h with hz
        subst z
        exact hy.1.1
      · contradiction

theorem q2_closed {x y z : T} (hx : Normal x) (hy : Normal y)
    (h : q2 ((fork (x) (y))) = some z) : Normal z := by
  cases x with
  | leaf n => simp [q2] at h
  | fork p q =>
    cases p with
    | leaf n => simp [q2] at h
    | fork y₁ y₂ =>
      cases q with
      | leaf n => simp [q2] at h
      | fork x₁ x₂ =>
        simp only [q2] at h
        split at h
        · injection h with hz
          subst z
          exact hx.2.1.1
        · contradiction

theorem closed {x y : T} (hx : Normal x) (hy : Normal y) :
    Normal (r ((fork (x) (y)))) := by
  cases h1 : q1 ((fork (x) (y))) with
  | some z =>
    cases h2 : q2 ((fork (x) (y))) with
    | some w => simpa only [r, h2, Option.getD] using q2_closed hx hy h2
    | none => simpa only [r, h2, h1, Option.getD] using q1_closed hx hy h1
  | none =>
    cases h2 : q2 ((fork (x) (y))) with
    | some z =>
      simpa only [r, h2, Option.getD] using q2_closed hx hy h2
    | none =>
      have hr : r ((fork (x) (y))) = (fork (x) (y)) := by
        simp only [r, h2, h1, Option.getD]
      rw [hr]
      exact ⟨hx, hy, hr⟩

def G := {t : T // Normal t}

instance : Magma G where
  op x y := ⟨r ((fork (x.1) (y.1))), closed x.2 y.2⟩

theorem fixed {x : T} (hx : Normal x) : r x = x := by
  cases x with
  | leaf n => rfl
  | fork x y => exact hx.2.2

@[simp] theorem eq1 (x y : T) : r ((fork (y) (((fork (((fork (x) (x)))) (y)))))) = x := by
  cases y with
  | leaf n => simp [r, q1, q2]
  | fork u v =>
    cases u <;> cases v <;> simp [r, q1, q2]
    split
    · rename_i h
      rcases h with ⟨_, _, hbad⟩
      subst_eqs
    · rfl

@[simp] theorem eq2 (x y : T) : r ((fork (((fork (((fork (y) (y)))) (((fork (x) (x))))))) (y))) = x := by
  simp [r, q1, q2]

theorem q1_inner_some {x y z : T} (h : q1 ((fork (((fork (x) (x)))) (y))) = some z) :
    y = (fork (((fork (z) (z)))) (((fork (x) (x))))) := by
  cases y with
  | leaf n => simp [q1] at h
  | fork p w =>
    cases p with
    | leaf n => simp [q1] at h
    | fork u v =>
      simp only [q1] at h
      split at h
      · injection h with hz
        subst z
        rename_i hc
        rcases hc with ⟨hxw, huv⟩
        subst w
        subst v
        rfl
      · contradiction

theorem q2_inner_some {x y z : T} (h : q2 ((fork (((fork (x) (x)))) (y))) = some z) :
    x = (fork (z) (z)) ∧ y = z := by
  cases x with
  | leaf n => simp [q2] at h
  | fork u v =>
    simp only [q2] at h
    split at h
    · injection h with hz
      subst z
      rename_i hc
      rcases hc with ⟨huv, _, huy⟩
      subst v
      subst y
      exact ⟨rfl, rfl⟩
    · contradiction

theorem comp2 {x y : T} (hx : Normal x) :
    r ((fork (y) (r ((fork (((fork (x) (x)))) (y)))))) = x := by
  cases h2 : q2 ((fork (((fork (x) (x)))) (y))) with
  | some z =>
    obtain ⟨ex, ey⟩ := q2_inner_some h2
    subst x
    subst y
    have hi : r ((fork (((fork (((fork (z) (z)))) (((fork (z) (z))))))) (z))) = z := by
      simp only [r, h2, Option.getD]
    rw [hi]
    exact fixed hx
  | none =>
    cases h1 : q1 ((fork (((fork (x) (x)))) (y))) with
    | some z =>
      have ey := q1_inner_some h1
      subst y
      have hi : r ((fork (((fork (x) (x)))) (((fork (((fork (z) (z)))) (((fork (x) (x))))))))) = z := by
        simp only [r, h2, h1, Option.getD]
      rw [hi]
      exact eq2 x z
    | none =>
      have hi : r ((fork (((fork (x) (x)))) (y))) = (fork (((fork (x) (x)))) (y)) := by
        simp only [r, h2, h1, Option.getD]
      rw [hi]
      exact eq1 x y

def sz : T → Nat
  | leaf _ => 1
  | (fork (x) (y)) => sz x + sz y + 1

theorem q1_xx_none (x : T) : q1 ((fork (x) (x))) = none := by
  cases x with
  | leaf n => rfl
  | fork u v =>
    cases u with
    | leaf n => rfl
    | fork a b =>
      simp only [q1]
      split
      · rename_i hc
        rcases hc with ⟨hbad, _⟩
        have hs := congrArg sz hbad
        simp [sz] at hs
        omega
      · rfl

theorem q2_xx_none (x : T) : q2 ((fork (x) (x))) = none := by
  cases x with
  | leaf n => rfl
  | fork u v =>
    cases u with
    | leaf n => rfl
    | fork a b =>
      cases v with
      | leaf n => rfl
      | fork c d =>
        simp only [q2]
        split
        · rename_i hc
          rcases hc with ⟨_, _, hbad⟩
          have hs := congrArg sz hbad
          simp [sz] at hs
          omega
        · rfl

@[simp] theorem r_xx (x : T) : r ((fork (x) (x))) = (fork (x) (x)) := by
  simp [r, q1_xx_none, q2_xx_none]

theorem comp3 {x y : T} (hx : Normal x) :
    r ((fork (y) (r ((fork (r ((fork (x) (x)))) (y)))))) = x := by
  rw [r_xx]
  exact comp2 hx

theorem source : EquationLHS G := by
  rintro ⟨x, hx⟩ ⟨y, hy⟩
  apply Subtype.ext
  change x = r ((fork (y) (r ((fork (r ((fork (x) (x)))) (y))))))
  exact (comp3 hx).symm

def a : G := ⟨leaf 0, trivial⟩
def b : G := ⟨leaf 1, trivial⟩

theorem target_false : ¬ EquationRHS G := by
  intro h
  have q := congrArg Subtype.val (h a b)
  simp [a, b, Magma.op, r, q1, q2] at q

end submission

def submission : Goal :=
  ⟨submission.G, submission.instMagmaG, submission.source, submission.target_false⟩

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_115_to_2707 : ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G := submission
#print axioms certificate_115_to_2707
