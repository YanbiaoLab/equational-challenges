-- Equation53684 → Equation57840
-- Recorded verdict: true
-- Premise: x * y = (((z * w) * x) * w) * w
-- Conclusion: x * (y * z) = ((x * y) * x) * w
-- Original submission SHA-256: a5b32ec5353410212a96af2602df011765c48721e9b6ff6a61e5030a0a8fb3e3
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = (((z ◇ w) ◇ x) ◇ w) ◇ w
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ (y ◇ z) = ((x ◇ y) ◇ x) ◇ w
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc0 : forall (q0 q1 q2 q3:G), (((q0 ◇ q1) ◇ q2) ◇ q2) = (q2 ◇ q3):=by
    intro q0 q1 q2 q3
    exact ((congrArg (fun t => t ◇ q2) (congrArg (fun t => t ◇ q2) ((h q0 q1 q0 q2).symm))).symm).trans ((h q2 q3 ((q0 ◇ q2) ◇ q0) q2).symm)
  have apc2 : forall (q4 q5 q6 q7:G), ((q4 ◇ q5) ◇ q6) = (q6 ◇ q7):=by
    intro q4 q5 q6 q7
    exact ((congrArg (fun t => t ◇ q6) ((h q4 q5 q4 q6).symm)).symm).trans (apc0 ((q4 ◇ q6) ◇ q4) q6 q6 q7)
  have apc3 : forall (q8 q9 q10 q11:G), (((q10 ◇ q8) ◇ q9) ◇ q9) = (q10 ◇ q11):=by
    intro q8 q9 q10 q11
    exact ((congrArg (fun t => t ◇ q9) (congrArg (fun t => t ◇ q9) (apc2 q8 q9 q10 q8))).symm).trans ((h q10 q11 q8 q9).symm)
  have apc6 : forall (q1 q12 q3:G), ((q12 ◇ q1) ◇ q12) = (q12 ◇ q3):=by
    intro q1 q12 q3
    exact ((congrArg (fun t => t ◇ q12) ((h q12 q1 q1 q12).symm)).symm).trans ((h q12 q3 (q1 ◇ q12) q12).symm)
  have apc8 : forall (x y z w:G), (x ◇ y) = (x ◇ x):=by
    intro x y z w
    exact (h x y z w).trans ((h x x z w).symm)
  have apc17 : forall (q13 q14 q15 q16:G), ((q15 ◇ q14) ◇ q13) = (q15 ◇ q15):=by
    intro q13 q14 q15 q16
    exact (((apc6 (q15 ◇ q14) (q15 ◇ q14) q13).symm).trans (apc3 q14 (q15 ◇ q14) q15 q16)).trans (apc8 q15 q16 (q15 ◇ q16) (q15 ◇ q16))
  exact (calc
    (x ◇ (y ◇ z)) = (x ◇ x):=(congrArg (fun t => x ◇ t) (apc8 y z (y ◇ z) (y ◇ z))).trans (apc8 x (y ◇ y) (x ◇ (y ◇ y)) (x ◇ (y ◇ y)))
    _ = (((x ◇ y) ◇ x) ◇ w):=(((congrArg (fun t => t ◇ w) (congrArg (fun t => t ◇ x) (apc8 x y (x ◇ y) (x ◇ y)))).trans (congrArg (fun t => t ◇ w) (apc17 x x x ((x ◇ x) ◇ x)))).trans (apc17 w x x ((x ◇ x) ◇ w))).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_53684_to_57840 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_53684_to_57840
