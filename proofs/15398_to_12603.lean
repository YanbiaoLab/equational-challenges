-- Equation15398 → Equation12603
-- Recorded verdict: true
-- Premise: x = x * (((y * (z * w)) * x) * z)
-- Conclusion: x = x * ((x * (y * (x * x))) * x)
-- Original submission SHA-256: 0d344c36ea9b65cc6c76c3d2e5da1269d24a54aad1c9c6624b7e15fe4f0a7ba3
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = x ◇ (((y ◇ (z ◇ w)) ◇ x) ◇ z)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x = x ◇ ((x ◇ (y ◇ (x ◇ x))) ◇ x)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y
  have apc0 : forall (q0 q1 q2:G), (q0 ◇ (((q1 ◇ q2) ◇ q0) ◇ q2)) = q0:=by
    intro q0 q1 q2
    exact ((congrArg (fun t => q0 ◇ t) (congrArg (fun t => t ◇ q2) (congrArg (fun t => t ◇ q0) (congrArg (fun t => q1 ◇ t) ((h q2 q0 q0 q0).symm))))).symm).trans ((h q0 q1 q2 (((q0 ◇ (q0 ◇ q0)) ◇ q2) ◇ q0)).symm)
  have apc1 : forall (q3 q4 q5 q6:G), (q5 ◇ ((q6 ◇ q5) ◇ ((q3 ◇ q4) ◇ q6))) = q5:=by
    intro q3 q4 q5 q6
    exact ((congrArg (fun t => q5 ◇ t) (congrArg (fun t => t ◇ ((q3 ◇ q4) ◇ q6)) (congrArg (fun t => t ◇ q5) (apc0 q6 q3 q4)))).symm).trans ((h q5 q6 ((q3 ◇ q4) ◇ q6) q4).symm)
  have apc2 : forall (q7 q8:G), (q7 ◇ (q8 ◇ q7)) = q7:=by
    intro q7 q8
    exact ((congrArg (fun t => q7 ◇ t) (apc0 (q8 ◇ q7) q7 q8)).symm).trans (apc1 (q7 ◇ q8) (q8 ◇ q7) q7 q8)
  exact (apc2 x (x ◇ (y ◇ (x ◇ x)))).symm

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_15398_to_12603 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_15398_to_12603
