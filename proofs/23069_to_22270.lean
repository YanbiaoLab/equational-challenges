-- Equation23069 → Equation22270
-- Recorded verdict: true
-- Premise: x = (y * (z * w)) * ((w * u) * x)
-- Conclusion: x = (x * (x * y)) * ((z * x) * x)
-- Original submission SHA-256: 16a199afd0a0ce8bc4ea40a13717b0d5e80217e4403ada2ba53458415b9bf012
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x = (y ◇ (z ◇ w)) ◇ ((w ◇ u) ◇ x)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (x ◇ (x ◇ y)) ◇ ((z ◇ x) ◇ x)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (q0 q1 q2:G), (q1 ◇ ((q1 ◇ q0) ◇ q2)) = q2:=by
    intro q0 q1 q2
    exact ((congrArg (fun t => t ◇ ((q1 ◇ q0) ◇ q2)) ((h q1 q0 q0 q0 q0).symm)).symm).trans ((h q2 (q0 ◇ (q0 ◇ q0)) (q0 ◇ q0) q1 q0).symm)
  have apc1 : forall (q3 q4 q5 q6 q7:G), ((q6 ◇ (q7 ◇ q4)) ◇ (q3 ◇ q5)) = q5:=by
    intro q3 q4 q5 q6 q7
    exact ((congrArg (fun t => (q6 ◇ (q7 ◇ q4)) ◇ t) (congrArg (fun t => t ◇ q5) (apc0 q3 q4 q3))).symm).trans ((h q5 q6 q7 q4 ((q4 ◇ q3) ◇ q3)).symm)
  exact (calc
    x = x:=rfl
    _ = ((x ◇ (x ◇ y)) ◇ ((z ◇ x) ◇ x)):=(apc1 (z ◇ x) y x x x).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_23069_to_22270 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_23069_to_22270
