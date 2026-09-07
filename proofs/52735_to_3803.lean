-- Equation52735 → Equation3803
-- Recorded verdict: true
-- Premise: x * y = ((z * (z * y)) * y) * z
-- Conclusion: x * y = (z * y) * (x * y)
-- Original submission SHA-256: 02191a11a008d504be83b20da46d871f950f0b7622ab97abcce335ae8a77273c
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = ((z ◇ (z ◇ y)) ◇ y) ◇ z
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = (z ◇ y) ◇ (x ◇ y)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (x y z:G), (y ◇ y) = (x ◇ y):=by
    intro x y z
    exact ((h x y z).trans ((h y y z).symm)).symm
  have apc1 : forall (q0 q1 q2:G), ((q1 ◇ q1) ◇ q2) = (q0 ◇ q1):=by
    intro q0 q1 q2
    exact ((congrArg (fun t => t ◇ q2) ((apc0 (q2 ◇ (q2 ◇ q1)) q1 q0).symm)).symm).trans ((h q0 q1 q2).symm)
  have apc2 : forall (q3 q4 q5 q6:G), ((q3 ◇ q5) ◇ q6) = (q4 ◇ q5):=by
    intro q3 q4 q5 q6
    exact ((congrArg (fun t => t ◇ q6) (apc0 q3 q5 q3)).symm).trans (apc1 q4 q5 q6)
  exact (apc2 z x y (x ◇ y)).symm

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_52735_to_3803 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_52735_to_3803
