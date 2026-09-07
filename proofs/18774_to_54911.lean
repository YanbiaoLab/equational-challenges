-- Equation18774 → Equation54911
-- Recorded verdict: false
-- Premise: x = (x ◇ x) ◇ ((y ◇ z) ◇ (w ◇ x))
-- Conclusion: x ◇ (y ◇ x) = x ◇ ((z ◇ y) ◇ x)
-- Original submission SHA-256: ee588f59f942a75343a2fc740a0bfe0721fae46c95cf0d498fd7f17ada6d7bfc
-- Aurora-accepted correction SHA-256: 1915ad729355b28bd41fd37a2539798909d4a76e6805f768d01784226d095269
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = (x ◇ x) ◇ ((y ◇ z) ◇ (w ◇ x))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ (y ◇ x) = x ◇ ((z ◇ y) ◇ x)
abbrev Goal : Prop := ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G
end

-- Aurora-accepted corrected submission body
                   

namespace submission

namespace CM18774_54911

inductive C3 | z | o | t deriving DecidableEq
def next : C3 → C3 | .z => .o | .o => .t | .t => .z
abbrev M := Nat × C3

def op (a b : M) : M :=
  (if a.2 = next (next b.2) then
      match a.1 with | 0 => b.1 | n + 1 => n
    else a.1 + 1,
   next b.2)

theorem base_source (x y z : M) :
    x = op (op x x) (op y (op z x)) := by
  rcases x with ⟨n, s⟩
  cases s <;> rfl

theorem source (x y z w : M) :
    x = op (op x x) (op (op y z) (op w x)) :=
  base_source x (op y z) w

def e : M := (0, .z)

theorem target_not :
    ¬ ∀ x y z : M, op x (op y x) = op x (op (op z y) x) := by
  intro h
  have bad := congrArg Prod.fst (h e e e)
  change 1 = 2 at bad
  have bad' : 0 = 1 := Nat.succ.inj bad
  exact Nat.noConfusion bad'

end CM18774_54911

def certificate : Goal := by
  refine ⟨CM18774_54911.M, ⟨CM18774_54911.op⟩, ?_, ?_⟩
  · exact CM18774_54911.source
  · exact CM18774_54911.target_not

end submission

def submission : Goal := submission.certificate

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_18774_to_54911 : ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G := submission
#print axioms certificate_18774_to_54911
