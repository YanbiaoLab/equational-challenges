-- Equation17976 → Equation17868
-- Recorded verdict: false
-- Premise: x = (x ◇ y) ◇ (z ◇ ((x ◇ x) ◇ x))
-- Conclusion: x = (x ◇ x) ◇ (y ◇ ((x ◇ y) ◇ x))
-- Original submission SHA-256: 749fdeeb59988797047642fa5ea5db3241023d51d4e68bc1c43559de5bce8c7d
-- Aurora-accepted correction SHA-256: c03ad1392dc7996a7c75230e76225216c12efa972b4de56482847920e8f60fae
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (x ◇ y) ◇ (z ◇ ((x ◇ x) ◇ x))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x = (x ◇ x) ◇ (y ◇ ((x ◇ y) ◇ x))
abbrev Goal : Prop := ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G
end

-- Aurora-accepted corrected submission body
                   

namespace submission

namespace CM17976_17868

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
  | .b0, .b0 => .b4 | .b0, .b1 => .b4 | .b0, .b2 => .b0
  | .b0, .b3 => .b0 | .b0, .b4 => .b3 | .b0, .b5 => .b3
  | .b1, .b0 => .b5 | .b1, .b1 => .b5 | .b1, .b2 => .b1
  | .b1, .b3 => .b1 | .b1, .b4 => .b2 | .b1, .b5 => .b2
  | .b2, .b0 => .b4 | .b2, .b1 => .b4 | .b2, .b2 => .b1
  | .b2, .b3 => .b1 | .b2, .b4 => .b2 | .b2, .b5 => .b2
  | .b3, .b0 => .b5 | .b3, .b1 => .b5 | .b3, .b2 => .b0
  | .b3, .b3 => .b0 | .b3, .b4 => .b3 | .b3, .b5 => .b3
  | .b4, .b0 => .b4 | .b4, .b1 => .b4 | .b4, .b2 => .b0
  | .b4, .b3 => .b0 | .b4, .b4 => .b2 | .b4, .b5 => .b2
  | .b5, .b0 => .b5 | .b5, .b1 => .b5 | .b5, .b2 => .b1
  | .b5, .b3 => .b1 | .b5, .b4 => .b3 | .b5, .b5 => .b3

def coc : Base → Base → C3
  | .b0, .b0 => .z | .b0, .b1 => .t | .b0, .b2 => .t
  | .b0, .b3 => .z | .b0, .b4 => .z | .b0, .b5 => .z
  | .b1, .b0 => .z | .b1, .b1 => .z | .b1, .b2 => .z
  | .b1, .b3 => .z | .b1, .b4 => .o | .b1, .b5 => .z
  | .b2, .b0 => .z | .b2, .b1 => .t | .b2, .b2 => .z
  | .b2, .b3 => .z | .b2, .b4 => .o | .b2, .b5 => .z
  | .b3, .b0 => .z | .b3, .b1 => .z | .b3, .b2 => .t
  | .b3, .b3 => .z | .b3, .b4 => .z | .b3, .b5 => .z
  | .b4, .b0 => .z | .b4, .b1 => .t | .b4, .b2 => .t
  | .b4, .b3 => .z | .b4, .b4 => .o | .b4, .b5 => .z
  | .b5, .b0 => .z | .b5, .b1 => .z | .b5, .b2 => .z
  | .b5, .b3 => .z | .b5, .b4 => .z | .b5, .b5 => .z

def op (x y : M) : M := (bop x.1 y.1, add (coc x.1 y.1) y.2)

theorem source (x y z : M) :
    x = op (op x y) (op z (op (op x x) x)) := by
  rcases x with ⟨xb, xu⟩
  rcases y with ⟨yb, yu⟩
  rcases z with ⟨zb, zu⟩
  cases xb <;> cases yb <;> cases zb <;> cases xu <;> rfl

def xw : M := (.b0, .z)
def yw : M := (.b4, .z)

theorem target_not :
    ¬ ∀ x y : M, x = op (op x x) (op y (op (op x y) x)) := by
  intro h
  have bad := congrArg Prod.snd (h xw yw)
  exact C3.noConfusion bad

end CM17976_17868

def certificate : Goal := by
  refine ⟨CM17976_17868.M, ⟨CM17976_17868.op⟩, ?_, ?_⟩
  · exact CM17976_17868.source
  · exact CM17976_17868.target_not

end submission

def submission : Goal := submission.certificate

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_17976_to_17868 : ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G := submission
#print axioms certificate_17976_to_17868
