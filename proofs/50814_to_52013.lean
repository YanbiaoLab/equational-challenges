-- Equation50814 → Equation52013
-- Recorded verdict: true
-- Premise: x * y = (z * ((x * x) * z)) * z
-- Conclusion: x * y = ((z * w) * (w * u)) * w
-- Original submission SHA-256: 60657a574583ae601f077438b7a2d24c74ec96de4c599715ec8966c2dd3e9494
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = (z ◇ ((x ◇ x) ◇ z)) ◇ z
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x ◇ y = ((z ◇ w) ◇ (w ◇ u)) ◇ w
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w u
  have apc0 : forall (q0 q1 q2:G), (q1 ◇ q2) = (q1 ◇ q0):=by
    intro q0 q1 q2
    exact ((h q1 q0 q0).trans ((h q1 q2 q0).symm)).symm
  have apc1 : forall (x y z:G), (x ◇ y) = (x ◇ x):=by
    intro x y z
    exact (h x y z).trans ((h x x z).symm)
  have apc2 : forall (q3 q4 q5 q6:G), ((q5 ◇ q3) ◇ q5) = (q4 ◇ q4):=by
    intro q3 q4 q5 q6
    exact (((congrArg (fun t => t ◇ q5) (apc0 q3 q5 ((q4 ◇ q4) ◇ q5))).symm).trans ((h q4 q6 q5).symm)).trans (apc1 q4 q6 (q4 ◇ q6))
  have apc8 : forall (q7 q8 q9:G), ((q8 ◇ q8) ◇ q8) = (q8 ◇ q7):=by
    intro q7 q8 q9
    exact ((congrArg (fun t => t ◇ q8) (apc1 q8 (q9 ◇ q9) (q8 ◇ (q9 ◇ q9)))).symm).trans (((congrArg (fun t => t ◇ q8) (congrArg (fun t => q8 ◇ t) (apc2 q8 q9 q8 q9))).symm).trans ((h q8 q7 q8).symm))
  have apc9 : forall (q10 q11 q12:G), (q12 ◇ q12) = (q11 ◇ q10):=by
    intro q10 q11 q12
    exact (((apc8 q10 q11 q10).symm).trans (apc2 q11 q12 q11 q10)).symm
  exact ((apc9 y x (x ◇ y)).symm).trans (apc9 w ((z ◇ w) ◇ (w ◇ u)) (x ◇ y))

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_50814_to_52013 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_50814_to_52013
