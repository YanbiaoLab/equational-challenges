-- Equation21064 → Equation45393
-- Recorded verdict: true
-- Premise: x = (y ◇ z) ◇ (((y ◇ x) ◇ x) ◇ y)
-- Conclusion: x ◇ y = y ◇ (((x ◇ x) ◇ x) ◇ z)
-- Original submission SHA-256: 33ff5dd101fe2b37c956e126e20aae76552d5e910507cc900c76c2486d3432ac
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (y ◇ z) ◇ (((y ◇ x) ◇ x) ◇ y)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = y ◇ (((x ◇ x) ◇ x) ◇ z)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (q0 q1 q2 q3:G), (q0 ◇ ((((q1 ◇ q2) ◇ q3) ◇ q3) ◇ (q1 ◇ q2))) = q3:=by
    intro q0 q1 q2 q3
    exact ((congrArg (fun t => t ◇ ((((q1 ◇ q2) ◇ q3) ◇ q3) ◇ (q1 ◇ q2))) ((h q0 q1 q2).symm)).symm).trans ((h q3 (q1 ◇ q2) (((q1 ◇ q0) ◇ q0) ◇ q1)).symm)
  have apc2 : forall (q4 q5 q6:G), (q5 ◇ q4) = q6:=by
    intro q4 q5 q6
    exact ((congrArg (fun t => q5 ◇ t) (apc0 ((((((q4 ◇ q4) ◇ q4) ◇ q4) ◇ (q4 ◇ q4)) ◇ q6) ◇ q6) q4 q4 q4)).symm).trans (apc0 q5 (((q4 ◇ q4) ◇ q4) ◇ q4) (q4 ◇ q4) q6)
  exact (apc2 y x (x ◇ y)).trans ((apc2 (((x ◇ x) ◇ x) ◇ z) y (x ◇ y)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_21064_to_45393 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_21064_to_45393
