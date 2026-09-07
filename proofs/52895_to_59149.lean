-- Equation52895 → Equation59149
-- Recorded verdict: true
-- Premise: x * y = ((z * (w * u)) * x) * z
-- Conclusion: (x * x) * y = x * ((z * z) * x)
-- Original submission SHA-256: 31aa9180764862c1b1d435e8e48b5c269093e0a201eaad8aec700c2300adbd59
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x ◇ y = ((z ◇ (w ◇ u)) ◇ x) ◇ z
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), (x ◇ x) ◇ y = x ◇ ((z ◇ z) ◇ x)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (x y z w u:G), (x ◇ y) = (x ◇ x):=by
    intro x y z w u
    exact (h x y z w u).trans ((h x x z w u).symm)
  have apc9 : forall (q0 q1 q2 q3 q4 q5 q6:G), (((q2 ◇ q1) ◇ q0) ◇ (q3 ◇ q3)) = (q3 ◇ q3):=by
    intro q0 q1 q2 q3 q4 q5 q6
    exact ((congrArg (fun t => ((q2 ◇ q1) ◇ q0) ◇ t) (apc0 q3 (q4 ◇ q5) (q3 ◇ (q4 ◇ q5)) (q3 ◇ (q4 ◇ q5)) (q3 ◇ (q4 ◇ q5)))).symm).trans ((((congrArg (fun t => t ◇ (q3 ◇ (q4 ◇ q5))) ((h (q2 ◇ q1) q0 q3 q4 q5).symm)).symm).trans ((h q3 q6 (q3 ◇ (q4 ◇ q5)) q2 q1).symm)).trans (apc0 q3 q6 (q3 ◇ q6) (q3 ◇ q6) (q3 ◇ q6)))
  have apc13 : forall (q7 q8 q9:G), (q9 ◇ q9) = (q8 ◇ q7):=by
    intro q7 q8 q9
    exact ((h q8 q7 (q9 ◇ q9) q7 q7).trans (apc9 q8 (q7 ◇ q7) (q9 ◇ q9) q9 q7 q7 q7)).symm
  exact ((apc13 y (x ◇ x) ((x ◇ x) ◇ y)).symm).trans (apc13 ((z ◇ z) ◇ x) x ((x ◇ x) ◇ y))

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_52895_to_59149 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_52895_to_59149
