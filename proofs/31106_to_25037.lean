-- Equation31106 → Equation25037
-- Recorded verdict: true
-- Premise: x = (x * ((y * y) * (y * x))) * z
-- Conclusion: x = (x * (y * (z * z))) * (z * w)
-- Original submission SHA-256: ec6d704d67a058bb986feeabb3882fd0f57e066731832d652a4c6895edc10072
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (x ◇ ((y ◇ y) ◇ (y ◇ x))) ◇ z
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = (x ◇ (y ◇ (z ◇ z))) ◇ (z ◇ w)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc0 : forall (q0 q1 q2 q3:G), ((q2 ◇ (q0 ◇ ((q0 ◇ ((q1 ◇ q1) ◇ (q1 ◇ q0))) ◇ q2))) ◇ q3) = q2:=by
    intro q0 q1 q2 q3
    exact ((congrArg (fun t => t ◇ q3) (congrArg (fun t => q2 ◇ t) (congrArg (fun t => t ◇ ((q0 ◇ ((q1 ◇ q1) ◇ (q1 ◇ q0))) ◇ q2)) ((h q0 q1 (q0 ◇ ((q1 ◇ q1) ◇ (q1 ◇ q0)))).symm)))).symm).trans ((h q2 (q0 ◇ ((q1 ◇ q1) ◇ (q1 ◇ q0))) q3).symm)
  have apc2 : forall (q4 q5 q6:G), ((q5 ◇ q4) ◇ q6) = q5:=by
    intro q4 q5 q6
    exact ((congrArg (fun t => t ◇ q6) (congrArg (fun t => q5 ◇ t) ((h q4 q4 (((q4 ◇ ((q4 ◇ q4) ◇ (q4 ◇ q4))) ◇ ((q4 ◇ q4) ◇ (q4 ◇ (q4 ◇ ((q4 ◇ q4) ◇ (q4 ◇ q4)))))) ◇ q5)).symm))).symm).trans (apc0 (q4 ◇ ((q4 ◇ q4) ◇ (q4 ◇ q4))) q4 q5 q6)
  exact (calc
    x = x:=rfl
    _ = ((x ◇ (y ◇ (z ◇ z))) ◇ (z ◇ w)):=(apc2 (y ◇ (z ◇ z)) x (z ◇ w)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_31106_to_25037 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_31106_to_25037
