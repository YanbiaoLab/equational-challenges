-- Equation27508 → Equation24084
-- Recorded verdict: false
-- Premise: x = ((x ◇ (x ◇ x)) ◇ y) ◇ (z ◇ x)
-- Conclusion: x = ((x ◇ y) ◇ y) ◇ ((x ◇ z) ◇ x)
-- Original submission SHA-256: 667b52b9f60fee5f209a6d914e655601bcb71fb4e61e4b27b6ea73eed958eadb
-- Aurora-accepted correction SHA-256: c65f90f8427ccf67bf7194777125e1fb48ccb6f03375e2df5bb67dcd584065e0
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = ((x ◇ (x ◇ x)) ◇ y) ◇ (z ◇ x)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = ((x ◇ y) ◇ y) ◇ ((x ◇ z) ◇ x)
abbrev Goal : Prop := ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G
end

-- Aurora-accepted corrected submission body
                   

namespace submission

namespace CM27508_24084

inductive Base | b0 | b1 | b2 | b3 | b4 | b5
inductive C3 | z | o | t
abbrev M := Base × C3

def add : C3 → C3 → C3
  | .z, x => x
  | .o, .z => .o
  | .o, .o => .t
  | .o, .t => .z
  | .t, .z => .t
  | .t, .o => .z
  | .t, .t => .o

def bop : Base → Base → Base
  | .b0, .b0 => .b4 | .b0, .b1 => .b5 | .b0, .b2 => .b4
  | .b0, .b3 => .b5 | .b0, .b4 => .b4 | .b0, .b5 => .b5
  | .b1, .b0 => .b4 | .b1, .b1 => .b5 | .b1, .b2 => .b4
  | .b1, .b3 => .b5 | .b1, .b4 => .b4 | .b1, .b5 => .b5
  | .b2, .b0 => .b0 | .b2, .b1 => .b1 | .b2, .b2 => .b1
  | .b2, .b3 => .b0 | .b2, .b4 => .b0 | .b2, .b5 => .b1
  | .b3, .b0 => .b0 | .b3, .b1 => .b1 | .b3, .b2 => .b1
  | .b3, .b3 => .b0 | .b3, .b4 => .b0 | .b3, .b5 => .b1
  | .b4, .b0 => .b3 | .b4, .b1 => .b2 | .b4, .b2 => .b2
  | .b4, .b3 => .b3 | .b4, .b4 => .b2 | .b4, .b5 => .b3
  | .b5, .b0 => .b3 | .b5, .b1 => .b2 | .b5, .b2 => .b2
  | .b5, .b3 => .b3 | .b5, .b4 => .b2 | .b5, .b5 => .b3

def coc : Base → Base → C3
  | .b0, .b0 => .z | .b0, .b1 => .z | .b0, .b2 => .z
  | .b0, .b3 => .z | .b0, .b4 => .z | .b0, .b5 => .z
  | .b1, .b0 => .t | .b1, .b1 => .z | .b1, .b2 => .t
  | .b1, .b3 => .z | .b1, .b4 => .t | .b1, .b5 => .z
  | .b2, .b0 => .t | .b2, .b1 => .z | .b2, .b2 => .z
  | .b2, .b3 => .t | .b2, .b4 => .t | .b2, .b5 => .z
  | .b3, .b0 => .z | .b3, .b1 => .z | .b3, .b2 => .z
  | .b3, .b3 => .z | .b3, .b4 => .z | .b3, .b5 => .z
  | .b4, .b0 => .z | .b4, .b1 => .o | .b4, .b2 => .o
  | .b4, .b3 => .z | .b4, .b4 => .o | .b4, .b5 => .z
  | .b5, .b0 => .z | .b5, .b1 => .z | .b5, .b2 => .z
  | .b5, .b3 => .z | .b5, .b4 => .z | .b5, .b5 => .z

def op (x y : M) : M := (bop x.1 y.1, add (coc x.1 y.1) x.2)

theorem source (x y z : M) :
    x = op (op (op x (op x x)) y) (op z x) := by
  rcases x with ⟨xb, xu⟩
  rcases y with ⟨yb, yu⟩
  rcases z with ⟨zb, zu⟩
  cases xb <;> cases yb <;> cases zb <;> cases xu <;> rfl

def xw : M := (.b0, .z)
def yw : M := (.b1, .z)

theorem target_not :
    ¬ ∀ x y z : M, x = op (op (op x y) y) (op (op x z) x) := by
  intro h
  have bad := congrArg Prod.snd (h xw yw xw)
  exact C3.noConfusion bad

end CM27508_24084

def certificate : Goal := by
  refine ⟨CM27508_24084.M, ⟨CM27508_24084.op⟩, ?_, ?_⟩
  · exact CM27508_24084.source
  · exact CM27508_24084.target_not

end submission

def submission : Goal := submission.certificate

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_27508_to_24084 : ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G := submission
#print axioms certificate_27508_to_24084
