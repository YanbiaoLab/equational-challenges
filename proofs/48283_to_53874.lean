-- Equation48283 → Equation53874
-- Recorded verdict: true
-- Premise: x * y = (z * (y * y)) * (w * u)
-- Conclusion: x * (x * y) = x * (y * (y * z))
-- Original submission SHA-256: 9108775e8247662e242348ef6a4198b8f63467224e100dbbc65de3726a82006d
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x ◇ y = (z ◇ (y ◇ y)) ◇ (w ◇ u)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ (x ◇ y) = x ◇ (y ◇ (y ◇ z))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (x y z w u:G), (y ◇ y) = (x ◇ y):=by
    intro x y z w u
    exact ((h x y z w u).trans ((h y y z w u).symm)).symm
  have apc1 : forall (q0 q1 q2 q3:G), (q0 ◇ (q1 ◇ (q3 ◇ q3))) = (q2 ◇ q3):=by
    intro q0 q1 q2 q3
    exact ((apc0 q0 (q1 ◇ (q3 ◇ q3)) q0 q0 q0).symm).trans ((h q2 q3 q1 q1 (q3 ◇ q3)).symm)
  have apc2 : forall (q4 q5 q6 q7:G), (q7 ◇ (q5 ◇ q5)) = (q6 ◇ (q4 ◇ q5)):=by
    intro q4 q5 q6 q7
    exact (((congrArg (fun t => q6 ◇ t) (apc1 q4 (q5 ◇ q5) q4 q5)).symm).trans (apc1 q6 q4 q7 (q5 ◇ q5))).symm
  have apc4 : forall (q4 q5 q6 q7:G), (q6 ◇ (q4 ◇ q5)) = (q5 ◇ (q5 ◇ q5)):=by
    intro q4 q5 q6 q7
    exact ((apc2 q4 q5 q6 q7).symm).trans (apc2 q5 q5 q5 q7)
  have apc17 : forall (q8 q9 q10 q11 q12 q13:G), (q8 ◇ (q8 ◇ q8)) = (q9 ◇ q10):=by
    intro q8 q9 q10 q11 q12 q13
    exact ((apc4 q11 q8 (q12 ◇ q13) ((q12 ◇ q13) ◇ (q11 ◇ q8))).symm).trans (((congrArg (fun t => t ◇ (q11 ◇ q8)) ((h q12 q13 q12 q10 q10).symm)).symm).trans ((h q9 q10 (q12 ◇ (q13 ◇ q13)) q11 q8).symm))
  exact ((apc17 (x ◇ (x ◇ y)) x (x ◇ y) (x ◇ (x ◇ y)) (x ◇ (x ◇ y)) (x ◇ (x ◇ y))).symm).trans (apc17 (x ◇ (x ◇ y)) x (y ◇ (y ◇ z)) (x ◇ (x ◇ y)) (x ◇ (x ◇ y)) (x ◇ (x ◇ y)))

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_48283_to_53874 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_48283_to_53874
