-- Equation29560 → Equation39620
-- Recorded verdict: true
-- Premise: x = (y ◇ (x ◇ (z ◇ (y ◇ w)))) ◇ w
-- Conclusion: x = (((y ◇ z) ◇ (z ◇ w)) ◇ z) ◇ z
-- Original submission SHA-256: a2aeb8c16dd7d9daef1c2597a43239d7bb21e217e483fabac41754eb0f012616
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = (y ◇ (x ◇ (z ◇ (y ◇ w)))) ◇ w
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = (((y ◇ z) ◇ (z ◇ w)) ◇ z) ◇ z
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc0 : forall (q0 q1 q2 q3:G), ((q3 ◇ (q2 ◇ q0)) ◇ q1) = q2:=by
    intro q0 q1 q2 q3
    exact ((congrArg (fun t => t ◇ q1) (congrArg (fun t => q3 ◇ t) (congrArg (fun t => q2 ◇ t) ((h q0 q0 q0 (q3 ◇ q1)).symm)))).symm).trans ((h q2 q3 (q0 ◇ (q0 ◇ (q0 ◇ (q0 ◇ (q3 ◇ q1))))) q1).symm)
  have apc1 : forall (q4 q5 q6:G), (q4 ◇ q5) = q6:=by
    intro q4 q5 q6
    exact ((congrArg (fun t => t ◇ q5) (apc0 q4 (q6 ◇ q4) q4 q4)).symm).trans (apc0 q4 q5 q6 (q4 ◇ (q4 ◇ q4)))
  exact ((apc1 x (z ◇ (y ◇ w)) x).symm).trans ((apc1 (((y ◇ z) ◇ (z ◇ w)) ◇ z) z (x ◇ (z ◇ (y ◇ w)))).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_29560_to_39620 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_29560_to_39620
