-- Equation3649 → Equation45726
-- Recorded verdict: true
-- Premise: x * y = z * ((w * w) * y)
-- Conclusion: x * y = z * (((z * y) * w) * y)
-- Original submission SHA-256: fa2a3cfe0500302ee62d68f80014cab7a40383e9146cb904eb7483a42a02ff5e
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = z ◇ ((w ◇ w) ◇ y)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = z ◇ (((z ◇ y) ◇ w) ◇ y)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc0 : forall (q0 q1 q2 q3 q4:G), (q4 ◇ ((q0 ◇ q1) ◇ q3)) = (q2 ◇ q3):=by
    intro q0 q1 q2 q3 q4
    exact ((congrArg (fun t => q4 ◇ t) (congrArg (fun t => t ◇ q3) ((h q0 q1 ((q0 ◇ q0) ◇ q1) q0).symm))).symm).trans ((h q2 q3 q4 ((q0 ◇ q0) ◇ q1)).symm)
  have apc1 : forall (x y z w:G), (y ◇ y) = (x ◇ y):=by
    intro x y z w
    exact ((h x y z w).trans ((h y y z w).symm)).symm
  have apc2 : forall (q5 q6 q7 q8:G), (q8 ◇ ((q5 ◇ q6) ◇ q7)) = (q7 ◇ q7):=by
    intro q5 q6 q7 q8
    exact ((apc1 q5 q7 q5 q5).trans ((apc0 q5 q6 q5 q7 q8).symm)).symm
  have apc6 : forall (q9 q10 q11 q12:G), (q11 ◇ (q9 ◇ q10)) = (q10 ◇ q10):=by
    intro q9 q10 q11 q12
    exact (((congrArg (fun t => q11 ◇ t) ((h q9 q10 (q12 ◇ q12) q12).symm)).symm).trans (apc2 q12 q12 ((q12 ◇ q12) ◇ q10) q11)).trans (apc2 q12 q12 q10 ((q12 ◇ q12) ◇ q10))
  exact (calc
    (x ◇ y) = (y ◇ y):=(apc1 x y w w).symm
    _ = (z ◇ (((z ◇ y) ◇ w) ◇ y)):=(apc6 ((z ◇ y) ◇ w) y z w).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_3649_to_45726 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_3649_to_45726
