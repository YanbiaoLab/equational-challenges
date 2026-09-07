-- Equation51961 → Equation56173
-- Recorded verdict: true
-- Premise: x * y = ((z * w) * (y * u)) * w
-- Conclusion: x * (y * z) = (y * y) * (w * y)
-- Original submission SHA-256: 7ced93a5d2259c122b183ac61145ad92426bfbc9abeda1c47c558186ad7df967
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x ◇ y = ((z ◇ w) ◇ (y ◇ u)) ◇ w
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ (y ◇ z) = (y ◇ y) ◇ (w ◇ y)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc0 : forall (q0 q1 q2 q3 q4:G), ((q1 ◇ q2) ◇ (q2 ◇ q0)) = (q3 ◇ q4):=by
    intro q0 q1 q2 q3 q4
    exact ((congrArg (fun t => t ◇ (q2 ◇ q0)) ((h q1 q2 q0 (q4 ◇ q0) q0).symm)).symm).trans ((h q3 q4 (q0 ◇ (q4 ◇ q0)) (q2 ◇ q0) q0).symm)
  have apc2 : forall (q0 q1 q2 q3 q4:G), ((q3 ◇ q3) ◇ (q3 ◇ q3)) = ((q1 ◇ q2) ◇ (q2 ◇ q0)):=by
    intro q0 q1 q2 q3 q4
    exact ((apc0 q0 q1 q2 q3 q4).trans ((apc0 q3 q3 q3 q3 q4).symm)).symm
  have apc3 : forall (q5 q6 q7:G), ((q5 ◇ q5) ◇ (q5 ◇ q5)) = (q6 ◇ q7):=by
    intro q5 q6 q7
    exact (apc2 q5 q5 q5 q5 q5).trans (apc0 q5 q5 q5 q6 q7)
  exact ((apc3 (x ◇ (y ◇ z)) x (y ◇ z)).symm).trans (apc3 (x ◇ (y ◇ z)) (y ◇ y) (w ◇ y))

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_51961_to_56173 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_51961_to_56173
