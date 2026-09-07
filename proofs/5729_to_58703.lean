-- Equation5729 → Equation58703
-- Recorded verdict: true
-- Premise: x = x * (y * (z * ((y * w) * z)))
-- Conclusion: (x * y) * z = x * (x * (y * z))
-- Original submission SHA-256: a19e97dab03275719a21f04ed1cc1c554520b82f07cebc370940f5142070d300
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = x ◇ (y ◇ (z ◇ ((y ◇ w) ◇ z)))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), (x ◇ y) ◇ z = x ◇ (x ◇ (y ◇ z))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (q0 q1 q2:G), (q0 ◇ (q1 ◇ (q2 ◇ (q1 ◇ q2)))) = q0:=by
    intro q0 q1 q2
    exact ((congrArg (fun t => q0 ◇ t) (congrArg (fun t => q1 ◇ t) (congrArg (fun t => q2 ◇ t) (congrArg (fun t => t ◇ q2) ((h q1 q0 q0 q0).symm))))).symm).trans ((h q0 q1 q2 (q0 ◇ (q0 ◇ ((q0 ◇ q0) ◇ q0)))).symm)
  have apc2 : forall (q3 q4 q5 q6:G), (q5 ◇ (q6 ◇ ((q3 ◇ (q4 ◇ (q3 ◇ q4))) ◇ q6))) = q5:=by
    intro q3 q4 q5 q6
    exact ((congrArg (fun t => q5 ◇ t) (congrArg (fun t => q6 ◇ t) (congrArg (fun t => (q3 ◇ (q4 ◇ (q3 ◇ q4))) ◇ t) (apc0 q6 q3 q4)))).symm).trans (apc0 q5 q6 (q3 ◇ (q4 ◇ (q3 ◇ q4))))
  have apc3 : forall (q7 q8:G), (q7 ◇ q8) = q7:=by
    intro q7 q8
    exact ((congrArg (fun t => q7 ◇ t) (apc2 q8 q7 q8 q7)).symm).trans ((h q7 q8 q7 (q7 ◇ (q8 ◇ q7))).symm)
  exact (calc
    ((x ◇ y) ◇ z) = x:=(congrArg (fun t => t ◇ z) (apc3 x y)).trans (apc3 x z)
    _ = (x ◇ (x ◇ (y ◇ z))):=(((congrArg (fun t => x ◇ t) (congrArg (fun t => x ◇ t) (apc3 y z))).trans (congrArg (fun t => x ◇ t) (apc3 x y))).trans (apc3 x x)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_5729_to_58703 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_5729_to_58703
