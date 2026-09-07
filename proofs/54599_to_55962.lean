-- Equation54599 → Equation55962
-- Recorded verdict: true
-- Premise: x * (y * z) = w * (z * (x * u))
-- Conclusion: x * (y * y) = (y * y) * (x * x)
-- Original submission SHA-256: 029f1482860fd7e633f3103947973a0f4cfc0ca653c420820c9d260c04cd9049
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x ◇ (y ◇ z) = w ◇ (z ◇ (x ◇ u))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x ◇ (y ◇ y) = (y ◇ y) ◇ (x ◇ x)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y
  have apc0 : forall (x y z w u:G), (x ◇ (y ◇ z)) = (x ◇ (x ◇ z)):=by
    intro x y z w u
    exact (h x y z w u).trans ((h x x z w u).symm)
  have apc10 : forall (q0 q1 q2 q3 q4 q5 q6:G), (q2 ◇ (q2 ◇ (q0 ◇ (q0 ◇ q1)))) = (q3 ◇ (q3 ◇ q4)):=by
    intro q0 q1 q2 q3 q4 q5 q6
    exact (((congrArg (fun t => q2 ◇ t) (congrArg (fun t => q4 ◇ t) (apc0 q0 q5 q1 (q0 ◇ (q5 ◇ q1)) (q0 ◇ (q5 ◇ q1))))).trans (apc0 q2 q4 (q0 ◇ (q0 ◇ q1)) (q2 ◇ (q4 ◇ (q0 ◇ (q0 ◇ q1)))) (q2 ◇ (q4 ◇ (q0 ◇ (q0 ◇ q1)))))).symm).trans ((((congrArg (fun t => q2 ◇ t) (congrArg (fun t => q4 ◇ t) ((h q0 q5 q1 q3 q0).symm))).symm).trans ((h q3 q6 q4 q2 (q1 ◇ (q0 ◇ q0))).symm)).trans (apc0 q3 q6 q4 (q3 ◇ (q6 ◇ q4)) (q3 ◇ (q6 ◇ q4))))
  have apc11 : forall (q7 q8 q9 q10 q11:G), (q10 ◇ (q10 ◇ q11)) = (q8 ◇ (q7 ◇ q9)):=by
    intro q7 q8 q9 q10 q11
    exact ((h q8 q7 q9 q9 (q8 ◇ q7)).trans (apc10 q8 q7 q9 q10 q11 q7 q7)).symm
  exact ((apc11 y x y x (x ◇ (y ◇ y))).symm).trans (apc11 x (y ◇ y) x x (x ◇ (y ◇ y)))

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_54599_to_55962 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_54599_to_55962
