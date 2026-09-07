-- Equation43032 → Equation60350
-- Recorded verdict: true
-- Premise: x * y = z * (y * ((z * z) * z))
-- Conclusion: (x * y) * y = (y * y) * (y * x)
-- Original submission SHA-256: bad1cda5e6aa4f527daf1e34993b513f8ec55575129ab8dc6f66e2ef9fd9e668
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = z ◇ (y ◇ ((z ◇ z) ◇ z))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), (x ◇ y) ◇ y = (y ◇ y) ◇ (y ◇ x)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y
  have apc0 : forall (q0 q1 q2:G), (q1 ◇ q2) = (q0 ◇ q2):=by
    intro q0 q1 q2
    exact ((h q0 q2 q0).trans ((h q1 q2 q0).symm)).symm
  have apc2 : forall (q3 q4 q5 q6:G), (q6 ◇ (q5 ◇ (q3 ◇ q6))) = (q4 ◇ q5):=by
    intro q3 q4 q5 q6
    exact ((congrArg (fun t => q6 ◇ t) (congrArg (fun t => q5 ◇ t) (apc0 q3 (q6 ◇ q6) q6))).symm).trans ((h q4 q5 q6).symm)
  have apc3 : forall (q7 q8 q9 q10 q11:G), (q10 ◇ (q9 ◇ (q7 ◇ q11))) = (q8 ◇ q9):=by
    intro q7 q8 q9 q10 q11
    exact (((apc2 q7 q8 q9 q11).symm).trans (apc0 q10 q11 (q9 ◇ (q7 ◇ q11)))).symm
  have apc4 : forall (q12 q13 q14 q15 q16:G), (q16 ◇ (q12 ◇ q13)) = (q14 ◇ q15):=by
    intro q12 q13 q14 q15 q16
    exact ((congrArg (fun t => q16 ◇ t) (apc2 q12 q12 q13 q15)).symm).trans (apc3 q13 q14 q15 q16 (q12 ◇ q15))
  have apc6 : forall (q17 q18 q19 q20:G), (q19 ◇ q20) = (q17 ◇ q18):=by
    intro q17 q18 q19 q20
    exact (((apc4 q17 q17 q17 q18 q17).symm).trans (apc4 q17 q17 q19 q20 q17)).symm
  exact (apc6 ((x ◇ y) ◇ y) ((y ◇ y) ◇ (y ◇ x)) (x ◇ y) y).trans ((apc6 ((x ◇ y) ◇ y) ((y ◇ y) ◇ (y ◇ x)) (y ◇ y) (y ◇ x)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_43032_to_60350 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_43032_to_60350
