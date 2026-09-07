-- Equation47491 → Equation50353
-- Recorded verdict: true
-- Premise: x * y = (z * z) * ((z * y) * w)
-- Conclusion: x * x = (y * ((x * x) * x)) * z
-- Original submission SHA-256: 0ea092c68181a926c90b7149eb3efead56eb7d3195230ce98b3e48bb91274e37
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = (z ◇ z) ◇ ((z ◇ y) ◇ w)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ x = (y ◇ ((x ◇ x) ◇ x)) ◇ z
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc2 : forall (q0 q1 q2 q3:G), ((q3 ◇ q3) ◇ (q0 ◇ q1)) = (q2 ◇ q3):=by
    intro q0 q1 q2 q3
    exact ((congrArg (fun t => (q3 ◇ q3) ◇ t) ((h q0 q1 q3 q0).symm)).symm).trans ((h q2 q3 q3 ((q3 ◇ q1) ◇ q0)).symm)
  have apc3 : forall (q4 q5 q6 q7:G), (q5 ◇ q6) = (q4 ◇ q7):=by
    intro q4 q5 q6 q7
    exact (((apc2 (q7 ◇ q6) q4 q4 q7).symm).trans ((h q5 q6 q7 q4).symm)).symm
  exact (apc3 (x ◇ x) x x ((y ◇ ((x ◇ x) ◇ x)) ◇ z)).trans ((apc3 (x ◇ x) (y ◇ ((x ◇ x) ◇ x)) z ((y ◇ ((x ◇ x) ◇ x)) ◇ z)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_47491_to_50353 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_47491_to_50353
