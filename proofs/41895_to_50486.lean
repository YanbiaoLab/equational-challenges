-- Equation41895 → Equation50486
-- Recorded verdict: true
-- Premise: x * y = y * (x * (y * (x * z)))
-- Conclusion: x * x = (y * ((z * w) * z)) * x
-- Original submission SHA-256: a7dfdede83a3bd6aee66a3bc2a3953a6d815edffbc435a1cb4dde3f6c78ef7ee
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = y ◇ (x ◇ (y ◇ (x ◇ z)))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ x = (y ◇ ((z ◇ w) ◇ z)) ◇ x
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc0 : forall (q0 q1:G), (q1 ◇ (q1 ◇ q0)) = (q0 ◇ q1):=by
    intro q0 q1
    exact ((congrArg (fun t => q1 ◇ t) ((h q1 q0 q0).symm)).symm).trans ((h q0 q1 (q1 ◇ q0)).symm)
  have apc1 : forall (q2 q3:G), ((q3 ◇ q2) ◇ q2) = (q2 ◇ q2):=by
    intro q2 q3
    exact ((congrArg (fun t => t ◇ q2) (apc0 q3 q2)).symm).trans (((apc0 (q2 ◇ (q2 ◇ q3)) q2).symm).trans ((h q2 q2 q3).symm))
  have apc5 : forall (q4 q5:G), ((q4 ◇ q5) ◇ (q5 ◇ q5)) = (q5 ◇ (q4 ◇ q5)):=by
    intro q4 q5
    exact ((congrArg (fun t => (q4 ◇ q5) ◇ t) (apc1 q5 q4)).symm).trans (apc0 q5 (q4 ◇ q5))
  have apc14 : forall (q6 q7:G), ((q6 ◇ q6) ◇ (q7 ◇ (q6 ◇ q6))) = (q6 ◇ q6):=by
    intro q6 q7
    exact ((((((congrArg (fun t => (q7 ◇ (q6 ◇ q6)) ◇ t) (apc0 q6 q6)).trans (apc1 (q6 ◇ q6) q7)).trans (apc5 q6 q6)).trans (apc0 q6 q6)).symm).trans (((congrArg (fun t => (q7 ◇ (q6 ◇ q6)) ◇ t) (apc5 q6 q6)).symm).trans (apc5 q7 (q6 ◇ q6)))).symm
  have apc15 : forall (q8 q9:G), (q9 ◇ (q8 ◇ q8)) = (q8 ◇ q8):=by
    intro q8 q9
    exact (((apc14 q8 q9).symm).trans (((congrArg (fun t => (q8 ◇ q8) ◇ t) (congrArg (fun t => q9 ◇ t) (apc14 q8 q9))).symm).trans ((h q9 (q8 ◇ q8) (q8 ◇ q8)).symm))).symm
  have apc17 : forall (q10 q11 q12:G), (q11 ◇ q12) = (q10 ◇ q10):=by
    intro q10 q11 q12
    exact (((((congrArg (fun t => q12 ◇ t) (congrArg (fun t => q11 ◇ t) (apc15 q10 q12))).trans (congrArg (fun t => q12 ◇ t) (apc15 q10 q11))).trans (apc15 q10 q12)).symm).trans (((congrArg (fun t => q12 ◇ t) (congrArg (fun t => q11 ◇ t) (congrArg (fun t => q12 ◇ t) (apc15 q10 q11)))).symm).trans ((h q11 q12 (q10 ◇ q10)).symm))).symm
  exact (apc17 (x ◇ x) x x).trans ((apc17 (x ◇ x) (y ◇ ((z ◇ w) ◇ z)) x).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_41895_to_50486 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_41895_to_50486
