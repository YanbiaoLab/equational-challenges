-- Equation58849 → Equation61135
-- Recorded verdict: true
-- Premise: (x * y) * z = y * (w * (u * u))
-- Conclusion: (x * y) * x = (z * (z * x)) * y
-- Original submission SHA-256: 212bd3da54906b73a7257ef24e2524c4c4be492aba8b3258bffce1ba6656ecb1
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), (x ◇ y) ◇ z = y ◇ (w ◇ (u ◇ u))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), (x ◇ y) ◇ x = (z ◇ (z ◇ x)) ◇ y
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (x y z w u:G), ((y ◇ y) ◇ y) = ((x ◇ y) ◇ z):=by
    intro x y z w u
    exact ((h x y z w u).trans ((h y y y w u).symm)).symm
  have apc1 : forall (q0 q1 q2 q3:G), ((q2 ◇ (q0 ◇ q1)) ◇ q3) = ((q1 ◇ q1) ◇ q1):=by
    intro q0 q1 q2 q3
    exact ((apc0 q0 q1 (q0 ◇ (q0 ◇ q0)) q0 q0).trans ((h q2 (q0 ◇ q1) q3 q0 q0).symm)).symm
  have apc2 : forall (q4 q5 q6 q7 q8:G), ((q6 ◇ q7) ◇ q8) = ((q4 ◇ q7) ◇ q5):=by
    intro q4 q5 q6 q7 q8
    exact ((h q4 q7 q5 q4 q4).trans ((h q6 q7 q8 q4 q4).symm)).symm
  have apc3 : forall (q4 q5 q6 q7 q8:G), ((q6 ◇ q7) ◇ q6) = ((q4 ◇ q7) ◇ q5):=by
    intro q4 q5 q6 q7 q8
    exact (((apc2 q4 q5 q6 q7 q8).symm).trans (apc2 q6 q6 q6 q7 q8)).symm
  have apc7 : forall (q9 q10 q11 q12 q13 q14 q15:G), ((q12 ◇ q12) ◇ q12) = ((q9 ◇ q11) ◇ q10):=by
    intro q9 q10 q11 q12 q13 q14 q15
    exact ((((apc3 q9 q10 (q13 ◇ (q12 ◇ q12)) q11 q9).symm).trans ((h q14 ((q13 ◇ (q12 ◇ q12)) ◇ q11) q15 q13 q12).symm)).trans ((congrArg (fun t => t ◇ q15) (congrArg (fun t => q14 ◇ t) (apc1 q12 q12 q13 q11))).trans (apc1 (q12 ◇ q12) q12 q14 q15))).symm
  exact ((apc7 x x y ((x ◇ y) ◇ x) ((x ◇ y) ◇ x) ((x ◇ y) ◇ x) ((x ◇ y) ◇ x)).symm).trans (apc7 z y (z ◇ x) ((x ◇ y) ◇ x) ((x ◇ y) ◇ x) ((x ◇ y) ◇ x) ((x ◇ y) ◇ x))

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_58849_to_61135 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_58849_to_61135
