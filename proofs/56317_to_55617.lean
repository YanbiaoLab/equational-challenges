-- Equation56317 → Equation55617
-- Recorded verdict: true
-- Premise: x * (y * z) = (w * x) * (u * x)
-- Conclusion: x * (x * y) = (x * x) * (y * y)
-- Original submission SHA-256: d0bb81df44dd520029bcbae762ea432b31b015e0850e8e2ac766b963056893b2
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x ◇ (y ◇ z) = (w ◇ x) ◇ (u ◇ x)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x ◇ (x ◇ y) = (x ◇ x) ◇ (y ◇ y)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y
  have apc0 : forall (x y z w u:G), (x ◇ (y ◇ z)) = (x ◇ (x ◇ x)):=by
    intro x y z w u
    exact (h x y z w u).trans ((h x x x w u).symm)
  have apc2 : forall (q0 q1 q2 q3 q4 q5 q6:G), ((q1 ◇ (q1 ◇ q1)) ◇ (q2 ◇ (q0 ◇ q1))) = ((q0 ◇ q1) ◇ (q3 ◇ q4)):=by
    intro q0 q1 q2 q3 q4 q5 q6
    exact ((congrArg (fun t => t ◇ (q2 ◇ (q0 ◇ q1))) (apc0 q1 q5 q6 (q1 ◇ (q5 ◇ q6)) (q1 ◇ (q5 ◇ q6)))).symm).trans (((congrArg (fun t => t ◇ (q2 ◇ (q0 ◇ q1))) ((h q1 q5 q6 q0 q0).symm)).symm).trans ((h (q0 ◇ q1) q3 q4 (q0 ◇ q1) q2).symm))
  have apc4 : forall (q7 q8 q9 q10 q11:G), ((q9 ◇ q9) ◇ (q10 ◇ q11)) = ((q9 ◇ q9) ◇ (q7 ◇ q8)):=by
    intro q7 q8 q9 q10 q11
    exact (((apc2 q9 q9 q7 q7 q8 q7 q7).symm).trans ((h (q9 ◇ q9) q10 q11 q9 q7).symm)).symm
  have apc5 : forall (q12 q13 q14 q15 q16:G), ((q14 ◇ q14) ◇ (q12 ◇ q13)) = (q14 ◇ (q14 ◇ q14)):=by
    intro q12 q13 q14 q15 q16
    exact (((apc4 q12 q13 q14 q12 q14).symm).trans ((h q14 q15 q16 q14 q12).symm)).trans (apc0 q14 q15 q16 (q14 ◇ (q15 ◇ q16)) (q14 ◇ (q15 ◇ q16)))
  exact (calc
    (x ◇ (x ◇ y)) = (x ◇ (x ◇ x)):=apc0 x x y (x ◇ (x ◇ y)) (x ◇ (x ◇ y))
    _ = ((x ◇ x) ◇ (y ◇ y)):=(apc5 y y x ((x ◇ x) ◇ (y ◇ y)) ((x ◇ x) ◇ (y ◇ y))).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_56317_to_55617 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_56317_to_55617
