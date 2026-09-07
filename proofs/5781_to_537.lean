-- Equation5781 → Equation537
-- Recorded verdict: true
-- Premise: x = y ◇ (x ◇ (x ◇ ((x ◇ z) ◇ x)))
-- Conclusion: x = y ◇ (z ◇ (x ◇ (x ◇ x)))
-- Original submission SHA-256: 8591721f14309e2a81c6936c2f3263973087af53e443437b18c165ab6f7613c5
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = y ◇ (x ◇ (x ◇ ((x ◇ z) ◇ x)))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = y ◇ (z ◇ (x ◇ (x ◇ x)))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (q0 q1 q2:G), (q2 ◇ (q1 ◇ (q1 ◇ (q0 ◇ q1)))) = q1:=by
    intro q0 q1 q2
    exact ((congrArg (fun t => q2 ◇ t) (congrArg (fun t => q1 ◇ t) (congrArg (fun t => q1 ◇ t) (congrArg (fun t => t ◇ q1) ((h q0 q1 q0).symm))))).symm).trans ((h q1 q2 (q0 ◇ (q0 ◇ ((q0 ◇ q0) ◇ q0)))).symm)
  have apc1 : forall (q3 q4 q5:G), (q5 ◇ ((q4 ◇ (q3 ◇ q4)) ◇ q4)) = (q4 ◇ (q3 ◇ q4)):=by
    intro q3 q4 q5
    exact ((congrArg (fun t => q5 ◇ t) (congrArg (fun t => (q4 ◇ (q3 ◇ q4)) ◇ t) (apc0 q3 q4 (q4 ◇ (q3 ◇ q4))))).symm).trans (apc0 q4 (q4 ◇ (q3 ◇ q4)) q5)
  have apc2 : forall (q6 q7 q8 q9:G), ((q7 ◇ (q7 ◇ (q6 ◇ q7))) ◇ q7) = (q8 ◇ q7):=by
    intro q6 q7 q8 q9
    exact ((((congrArg (fun t => q8 ◇ t) (apc0 q6 q7 ((q7 ◇ (q7 ◇ (q6 ◇ q7))) ◇ (q9 ◇ (q7 ◇ (q7 ◇ (q6 ◇ q7))))))).symm).trans (apc1 q9 (q7 ◇ (q7 ◇ (q6 ◇ q7))) q8)).trans (congrArg (fun t => (q7 ◇ (q7 ◇ (q6 ◇ q7))) ◇ t) (apc0 q6 q7 q9))).symm
  have apc4 : forall (q6 q7 q9 q8:G), (q8 ◇ q7) = (q6 ◇ q7):=by
    intro q6 q7 q9 q8
    exact ((apc2 q6 q7 q8 q9).symm).trans (apc2 q6 q7 q6 q9)
  have apc5 : forall (q10 q11 q12 q13:G), (q13 ◇ (q10 ◇ (q12 ◇ (q11 ◇ q12)))) = q12:=by
    intro q10 q11 q12 q13
    exact ((congrArg (fun t => q13 ◇ t) (apc4 q10 (q12 ◇ (q11 ◇ q12)) q10 q12)).symm).trans (apc0 q11 q12 q13)
  exact (calc
    x = x:=rfl
    _ = (y ◇ (z ◇ (x ◇ (x ◇ x)))):=(apc5 z x x y).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_5781_to_537 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_5781_to_537
