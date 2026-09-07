-- Equation31079 → Equation19719
-- Recorded verdict: true
-- Premise: x = (x * ((y * x) * (z * x))) * z
-- Conclusion: x = (x * y) * ((y * (z * y)) * z)
-- Original submission SHA-256: d8d9ab8509aa093816664f17205171d970414e6a98545779f254d4ac61007c6c
-- Generator: equational-challenges standalone v1
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (x ◇ ((y ◇ x) ◇ (z ◇ x))) ◇ z
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (x ◇ y) ◇ ((y ◇ (z ◇ y)) ◇ z)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (q0 q1 q2:G), ((q1 ◇ (q0 ◇ (q2 ◇ q1))) ◇ q2) = q1:=by
    intro q0 q1 q2
    exact ((congrArg (fun t => t ◇ q2) (congrArg (fun t => q1 ◇ t) (congrArg (fun t => t ◇ (q2 ◇ q1)) ((h q0 q0 q1).symm)))).symm).trans ((h q1 (q0 ◇ ((q0 ◇ q0) ◇ (q1 ◇ q0))) q2).symm)
  have apc1 : forall (q3 q4 q5:G), ((q4 ◇ q3) ◇ q5) = q4:=by
    intro q3 q4 q5
    exact ((congrArg (fun t => t ◇ q5) (congrArg (fun t => q4 ◇ t) (apc0 q3 q3 (q5 ◇ q4)))).symm).trans (apc0 (q3 ◇ (q3 ◇ ((q5 ◇ q4) ◇ q3))) q4 q5)
  exact (calc
    x = x:=rfl
    _ = ((x ◇ y) ◇ ((y ◇ (z ◇ y)) ◇ z)):=((congrArg (fun t => (x ◇ y) ◇ t) (apc1 (z ◇ y) y z)).trans (apc1 y x y)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_31079_to_19719 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_31079_to_19719
