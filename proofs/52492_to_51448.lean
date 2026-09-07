-- Equation52492 → Equation51448
-- Recorded verdict: true
-- Premise: x * y = ((y * (z * x)) * z) * w
-- Conclusion: x * y = ((x * y) * (z * w)) * x
-- Original submission SHA-256: 36f772267ff3c0f01bb439c63613a26e92d273160081b03994530212b6c0e2b5
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = ((y ◇ (z ◇ x)) ◇ z) ◇ w
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = ((x ◇ y) ◇ (z ◇ w)) ◇ x
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc0 : forall (q0 q1 q2 q3 q4 q5:G), (((q5 ◇ (q0 ◇ q1)) ◇ ((q1 ◇ (q2 ◇ q0)) ◇ q2)) ◇ q3) = (q4 ◇ q5):=by
    intro q0 q1 q2 q3 q4 q5
    exact ((congrArg (fun t => t ◇ q3) (congrArg (fun t => t ◇ ((q1 ◇ (q2 ◇ q0)) ◇ q2)) (congrArg (fun t => q5 ◇ t) ((h q0 q1 q2 q4).symm)))).symm).trans ((h q4 q5 ((q1 ◇ (q2 ◇ q0)) ◇ q2) q3).symm)
  have apc1 : forall (q0 q1 q2 q3 q4 q5:G), (q4 ◇ q5) = (q0 ◇ q5):=by
    intro q0 q1 q2 q3 q4 q5
    exact ((apc0 q0 q1 q2 q3 q4 q5).symm).trans (apc0 q0 q1 q2 q3 q0 q5)
  have apc2 : forall (q6 q7 q8 q9 q10 q11 q12:G), (((q12 ◇ (q7 ◇ q8)) ◇ (q6 ◇ q9)) ◇ q10) = (q11 ◇ q12):=by
    intro q6 q7 q8 q9 q10 q11 q12
    exact ((congrArg (fun t => t ◇ q10) (congrArg (fun t => (q12 ◇ (q7 ◇ q8)) ◇ t) (apc1 q6 q6 q6 q6 (q8 ◇ (q9 ◇ q7)) q9))).symm).trans (apc0 q7 q8 q9 q10 q11 q12)
  have apc3 : forall (q13 q14 q15 q16 q17 q18:G), ((q13 ◇ (q14 ◇ q15)) ◇ q16) = (q17 ◇ q18):=by
    intro q13 q14 q15 q16 q17 q18
    exact ((congrArg (fun t => t ◇ q16) (apc1 q13 q13 q13 q13 (q18 ◇ (q13 ◇ q13)) (q14 ◇ q15))).symm).trans (apc2 q14 q13 q13 q15 q16 q17 q18)
  have apc9 : forall (q13 q14 q15 q16 q17 q18:G), (q17 ◇ q18) = (q13 ◇ q13):=by
    intro q13 q14 q15 q16 q17 q18
    exact ((apc3 q13 q14 q15 q16 q17 q18).symm).trans (apc3 q13 q14 q15 q16 q13 q13)
  exact (apc9 (x ◇ y) (x ◇ y) (x ◇ y) (x ◇ y) x y).trans ((apc9 (x ◇ y) (x ◇ y) (x ◇ y) (x ◇ y) ((x ◇ y) ◇ (z ◇ w)) x).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_52492_to_51448 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_52492_to_51448
