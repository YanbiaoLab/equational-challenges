-- Equation1437 → Equation54919
-- Recorded verdict: false
-- Premise: x = (x ◇ x) ◇ (y ◇ (z ◇ x))
-- Conclusion: x ◇ (y ◇ x) = x ◇ ((z ◇ w) ◇ x)
-- Original submission SHA-256: 53f87febef82692e07ce191f0a847d6d1f3badc72349d4a90046f90f76fe51c3
-- Aurora-accepted correction SHA-256: b676c0f692738e5cff745007847dd3ee93d68993fbaad171d5585dc1c6ed5508
-- Generator: equational-challenges standalone v2
-- All project definitions are embedded in this file.

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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (x ◇ x) ◇ (y ◇ (z ◇ x))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ (y ◇ x) = x ◇ ((z ◇ w) ◇ x)
abbrev Goal : Prop := ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G
end

-- Aurora-accepted corrected submission body
                   

namespace submission

namespace CM1437_54919

inductive C3 | z | o | t deriving DecidableEq

def next : C3 → C3
  | .z => .o
  | .o => .t
  | .t => .z

abbrev M := Nat × C3

def op (a b : M) : M :=
  (if a.2 = next (next b.2) then
      match a.1 with
      | 0 => b.1
      | n + 1 => n
    else a.1 + 1,
   next b.2)

theorem source (x y z : M) :
    x = op (op x x) (op y (op z x)) := by
  rcases x with ⟨n, s⟩
  cases s <;> rfl

def w : M := (0, .z)

theorem target_not :
    ¬ ∀ x y z w : M, op x (op y x) = op x (op (op z w) x) := by
  intro h
  have bad := congrArg Prod.fst (h w w w w)
  change 1 = 2 at bad
  have bad' : 0 = 1 := Nat.succ.inj bad
  exact Nat.noConfusion bad'

end CM1437_54919

def certificate : Goal := by
  refine ⟨CM1437_54919.M, ⟨CM1437_54919.op⟩, ?_, ?_⟩
  · exact CM1437_54919.source
  · exact CM1437_54919.target_not

end submission

def submission : Goal := submission.certificate

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_1437_to_54919 : ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G := submission
#print axioms certificate_1437_to_54919
