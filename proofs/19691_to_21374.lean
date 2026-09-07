-- Equation19691 → Equation21374
-- Recorded verdict: true
-- Premise: x = (x * y) * ((x * (z * w)) * w)
-- Conclusion: x = (x * (x * y)) * (x * (x * y))
-- Original submission SHA-256: 10591afaf0f036b76907c90f3a2a1a7bdd0e5280b249cea554748b3e2b7815f4
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = (x ◇ y) ◇ ((x ◇ (z ◇ w)) ◇ w)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x = (x ◇ (x ◇ y)) ◇ (x ◇ (x ◇ y))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y
  have apc0 : forall (q0 q1:G), ((q0 ◇ q1) ◇ q0) = q0:=by
    intro q0 q1
    exact ((congrArg (fun t => (q0 ◇ q1) ◇ t) ((h q0 (q0 ◇ ((q0 ◇ (q0 ◇ q0)) ◇ q0)) q0 q0).symm)).symm).trans ((h q0 q1 q0 ((q0 ◇ (q0 ◇ q0)) ◇ q0)).symm)
  have apc2 : forall (q2 q3:G), (q3 ◇ (q3 ◇ q2)) = (q3 ◇ q2):=by
    intro q2 q3
    exact ((congrArg (fun t => t ◇ (q3 ◇ q2)) (apc0 q3 q2)).symm).trans (apc0 (q3 ◇ q2) q3)
  have apc3 : forall (q4 q5 q6:G), ((q5 ◇ (q6 ◇ q4)) ◇ q4) = q5:=by
    intro q4 q5 q6
    exact ((apc2 q4 (q5 ◇ (q6 ◇ q4))).symm).trans ((h q5 (q6 ◇ q4) q6 q4).symm)
  have apc4 : forall (q7 q8 q9:G), ((q8 ◇ (q9 ◇ q7)) ◇ (q9 ◇ q7)) = q8:=by
    intro q7 q8 q9
    exact ((congrArg (fun t => t ◇ (q9 ◇ q7)) (congrArg (fun t => q8 ◇ t) (apc2 q7 q9))).symm).trans (apc3 (q9 ◇ q7) q8 q9)
  have apc5 : forall (q10 q11:G), ((q11 ◇ q10) ◇ (q11 ◇ q10)) = q11:=by
    intro q10 q11
    exact ((congrArg (fun t => t ◇ (q11 ◇ q10)) (apc2 q10 q11)).symm).trans (apc4 q10 q11 q11)
  exact (apc5 (x ◇ y) x).symm

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_19691_to_21374 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_19691_to_21374
