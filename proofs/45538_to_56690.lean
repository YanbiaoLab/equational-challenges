-- Equation45538 → Equation56690
-- Recorded verdict: true
-- Premise: x * y = y * (((z * w) * u) * z)
-- Conclusion: x * (y * x) = (y * (y * x)) * z
-- Original submission SHA-256: 333d38771cf3f1e52ce2604fbedb4b8891d59c038ed16aacb5d444d29e9458cf
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x ◇ y = y ◇ (((z ◇ w) ◇ u) ◇ z)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ (y ◇ x) = (y ◇ (y ◇ x)) ◇ z
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (x y z w u:G), (y ◇ y) = (x ◇ y):=by
    intro x y z w u
    exact ((h x y z w u).trans ((h y y z w u).symm)).symm
  have apc1 : forall (q0 q1 q2:G), (q1 ◇ (q2 ◇ q2)) = (q0 ◇ q1):=by
    intro q0 q1 q2
    exact ((congrArg (fun t => q1 ◇ t) ((apc0 ((q2 ◇ q0) ◇ q0) q2 q0 q0 q0).symm)).symm).trans ((h q0 q1 q2 q0 q0).symm)
  have apc2 : forall (q3 q4:G), (q4 ◇ (q3 ◇ q3)) = (q4 ◇ q4):=by
    intro q3 q4
    exact (apc1 q3 q4 q3).trans ((apc0 q3 q4 q3 q3 q3).symm)
  have apc4 : forall (q5 q6 q7:G), (q7 ◇ (q5 ◇ q6)) = (q7 ◇ q7):=by
    intro q5 q6 q7
    exact ((congrArg (fun t => q7 ◇ t) (apc0 q5 q6 q5 q5 q5)).symm).trans (apc2 q6 q7)
  have apc5 : forall (q8 q9 q10:G), (q9 ◇ q10) = (q8 ◇ q10):=by
    intro q8 q9 q10
    exact ((h q8 q10 q8 q8 q8).trans ((h q9 q10 q8 q8 q8).symm)).symm
  have apc6 : forall (q11 q12 q13 q14 q15 q16:G), (q12 ◇ q13) = (q11 ◇ q11):=by
    intro q11 q12 q13 q14 q15 q16
    exact (((apc4 ((q14 ◇ q15) ◇ q16) q14 q11).symm).trans (((apc5 q11 q13 (((q14 ◇ q15) ◇ q16) ◇ q14)).symm).trans ((h q12 q13 q14 q15 q16).symm))).symm
  exact (apc6 (x ◇ (y ◇ x)) x (y ◇ x) (x ◇ (y ◇ x)) (x ◇ (y ◇ x)) (x ◇ (y ◇ x))).trans ((apc6 (x ◇ (y ◇ x)) (y ◇ (y ◇ x)) z (x ◇ (y ◇ x)) (x ◇ (y ◇ x)) (x ◇ (y ◇ x))).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_45538_to_56690 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_45538_to_56690
