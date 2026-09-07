-- Equation43786 → Equation57487
-- Recorded verdict: true
-- Premise: x * y = y * ((z * w) * (u * u))
-- Conclusion: x * (x * y) = ((z * z) * w) * x
-- Original submission SHA-256: 4518d7872689bad642f18379b5f0750eafd3112d05ff5d2f81ae969d9a83373a
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x ◇ y = y ◇ ((z ◇ w) ◇ (u ◇ u))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ (x ◇ y) = ((z ◇ z) ◇ w) ◇ x
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc2 : forall (q0 q1 q2 q3 q4:G), (q3 ◇ (q0 ◇ (q4 ◇ q1))) = (q2 ◇ q3):=by
    intro q0 q1 q2 q3 q4
    exact ((congrArg (fun t => q3 ◇ t) ((h q0 (q4 ◇ q1) q0 q0 q0).symm)).symm).trans ((h q2 q3 q4 q1 (q0 ◇ q0)).symm)
  have apc3 : forall (q5 q6 q7 q8:G), (q8 ◇ (q5 ◇ q6)) = (q7 ◇ q8):=by
    intro q5 q6 q7 q8
    exact ((congrArg (fun t => q8 ◇ t) (apc2 q5 q5 q5 q6 q5)).symm).trans (apc2 q6 (q5 ◇ q5) q7 q8 q5)
  exact apc3 x y ((z ◇ z) ◇ w) x

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_43786_to_57487 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_43786_to_57487
