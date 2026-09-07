-- Equation51569 → Equation59786
-- Recorded verdict: true
-- Premise: x * y = ((y * y) * (x * x)) * z
-- Conclusion: (x * y) * z = z * ((w * y) * z)
-- Original submission SHA-256: 336525b4f0f1dd15077131240d9294a99a7c600e7d29180e5cd0d70bc79c4118
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = ((y ◇ y) ◇ (x ◇ x)) ◇ z
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), (x ◇ y) ◇ z = z ◇ ((w ◇ y) ◇ z)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc0 : forall (q0 q1 q2:G), (q1 ◇ (q0 ◇ q0)) = ((q0 ◇ q0) ◇ q2):=by
    intro q0 q1 q2
    exact (((congrArg (fun t => t ◇ q2) ((h q0 q0 (q1 ◇ q1)).symm)).symm).trans ((h q1 (q0 ◇ q0) q2).symm)).symm
  have apc1 : forall (q3 q4 q5 q6:G), ((q3 ◇ q3) ◇ q4) = (q5 ◇ q6):=by
    intro q3 q4 q5 q6
    exact ((apc0 q3 ((q6 ◇ q6) ◇ (q5 ◇ q5)) q4).symm).trans ((h q5 q6 (q3 ◇ q3)).symm)
  exact ((apc1 ((x ◇ y) ◇ z) (z ◇ ((w ◇ y) ◇ z)) (x ◇ y) z).symm).trans (apc1 ((x ◇ y) ◇ z) (z ◇ ((w ◇ y) ◇ z)) z ((w ◇ y) ◇ z))

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_51569_to_59786 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_51569_to_59786
