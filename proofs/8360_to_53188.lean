-- Equation8360 → Equation53188
-- Recorded verdict: true
-- Premise: x = x * (y * (((z * y) * w) * z))
-- Conclusion: x * y = (((x * y) * y) * z) * z
-- Original submission SHA-256: 142d28eb5af8b103b51ca1eb786a24aa92501e32c2aaab09a08c0f345e34c91b
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = x ◇ (y ◇ (((z ◇ y) ◇ w) ◇ z))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = (((x ◇ y) ◇ y) ◇ z) ◇ z
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (q0 q1 q2:G), (q0 ◇ (q1 ◇ ((q2 ◇ q1) ◇ q2))) = q0:=by
    intro q0 q1 q2
    exact ((congrArg (fun t => q0 ◇ t) (congrArg (fun t => q1 ◇ t) (congrArg (fun t => t ◇ q2) ((h (q2 ◇ q1) q0 q0 q0).symm)))).symm).trans ((h q0 q1 q2 (q0 ◇ (((q0 ◇ q0) ◇ q0) ◇ q0))).symm)
  have apc1 : forall (q3 q4 q5 q6:G), (q5 ◇ ((q3 ◇ ((q4 ◇ q3) ◇ q4)) ◇ (q6 ◇ q6))) = q5:=by
    intro q3 q4 q5 q6
    exact ((congrArg (fun t => q5 ◇ t) (congrArg (fun t => (q3 ◇ ((q4 ◇ q3) ◇ q4)) ◇ t) (congrArg (fun t => t ◇ q6) (apc0 q6 q3 q4)))).symm).trans (apc0 q5 (q3 ◇ ((q4 ◇ q3) ◇ q4)) q6)
  have apc2 : forall (q7 q8:G), (q7 ◇ q8) = q7:=by
    intro q7 q8
    exact ((congrArg (fun t => q7 ◇ t) (apc1 ((q7 ◇ q7) ◇ q8) q7 q8 q7)).symm).trans ((h q7 q8 (q7 ◇ q7) ((q7 ◇ ((q7 ◇ q7) ◇ q8)) ◇ q7)).symm)
  exact (calc
    (x ◇ y) = x:=apc2 x y
    _ = ((((x ◇ y) ◇ y) ◇ z) ◇ z):=((((congrArg (fun t => t ◇ z) (congrArg (fun t => t ◇ z) (congrArg (fun t => t ◇ y) (apc2 x y)))).trans (congrArg (fun t => t ◇ z) (congrArg (fun t => t ◇ z) (apc2 x y)))).trans (congrArg (fun t => t ◇ z) (apc2 x z))).trans (apc2 x z)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_8360_to_53188 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_8360_to_53188
