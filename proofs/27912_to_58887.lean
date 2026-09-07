-- Equation27912 → Equation58887
-- Recorded verdict: true
-- Premise: x = ((y * (y * y)) * z) * (y * x)
-- Conclusion: (x * y) * z = z * (z * (x * z))
-- Original submission SHA-256: 021f6a11fc578d48338a3ea292c647ddbc6f503f6d97b2122ce1334e53a635f8
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = ((y ◇ (y ◇ y)) ◇ z) ◇ (y ◇ x)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), (x ◇ y) ◇ z = z ◇ (z ◇ (x ◇ z))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (q0 q1 q2:G), (q0 ◇ ((q1 ◇ (q1 ◇ q1)) ◇ q2)) = q2:=by
    intro q0 q1 q2
    exact ((congrArg (fun t => t ◇ ((q1 ◇ (q1 ◇ q1)) ◇ q2)) ((h q0 q1 ((q1 ◇ (q1 ◇ q1)) ◇ (q1 ◇ (q1 ◇ q1)))).symm)).symm).trans ((h q2 (q1 ◇ (q1 ◇ q1)) (q1 ◇ q0)).symm)
  have apc1 : forall (q3 q4 q5:G), (q5 ◇ q3) = (q4 ◇ q3):=by
    intro q3 q4 q5
    exact ((congrArg (fun t => q5 ◇ t) ((h q3 q4 ((q4 ◇ (q4 ◇ q4)) ◇ (q4 ◇ (q4 ◇ q4)))).symm)).symm).trans (apc0 q5 (q4 ◇ (q4 ◇ q4)) (q4 ◇ q3))
  have apc2 : forall (q3 q4 q5:G), (q4 ◇ q3) = (q3 ◇ q3):=by
    intro q3 q4 q5
    exact ((apc1 q3 q4 q5).symm).trans (apc1 q3 q3 q5)
  have apc3 : forall (q6 q7 q8:G), (q6 ◇ (q7 ◇ q7)) = q7:=by
    intro q6 q7 q8
    exact ((congrArg (fun t => q6 ◇ t) (apc2 q7 q8 (q8 ◇ q7))).symm).trans (((congrArg (fun t => t ◇ (q8 ◇ q7)) (apc0 (q8 ◇ (q8 ◇ q8)) q6 q6)).symm).trans ((h q7 q8 ((q6 ◇ (q6 ◇ q6)) ◇ q6)).symm))
  have apc4 : forall (q9 q10 q11 q12:G), (q9 ◇ (q10 ◇ q11)) = q11:=by
    intro q9 q10 q11 q12
    exact ((congrArg (fun t => q9 ◇ t) (congrArg (fun t => t ◇ q11) (apc3 q12 q10 (q12 ◇ (q10 ◇ q10))))).symm).trans (((congrArg (fun t => q9 ◇ t) (congrArg (fun t => t ◇ q11) (apc1 (q10 ◇ q10) q12 q10))).symm).trans (apc0 q9 q10 q11))
  exact (calc
    ((x ◇ y) ◇ z) = (z ◇ z):=apc2 z (x ◇ y) ((x ◇ y) ◇ z)
    _ = (z ◇ (z ◇ (x ◇ z))):=(congrArg (fun t => z ◇ t) (apc4 z x z (z ◇ (x ◇ z)))).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_27912_to_58887 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_27912_to_58887
