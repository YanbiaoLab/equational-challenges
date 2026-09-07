-- Equation47284 → Equation52921
-- Recorded verdict: true
-- Premise: x * y = (y * z) * ((w * z) * u)
-- Conclusion: x * y = ((z * (w * u)) * u) * u
-- Original submission SHA-256: 740a089cb61be3d88266253853b9479eb3d1fe5fb29b56a470b70da3571b34a5
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x ◇ y = (y ◇ z) ◇ ((w ◇ z) ◇ u)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x ◇ y = ((z ◇ (w ◇ u)) ◇ u) ◇ u
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w u
  have apc2 : forall (q0 q1 q2 q3 q4:G), ((q3 ◇ q4) ◇ (q0 ◇ q1)) = (q2 ◇ q3):=by
    intro q0 q1 q2 q3 q4
    exact ((congrArg (fun t => (q3 ◇ q4) ◇ t) ((h q0 q1 q4 q0 q0).symm)).symm).trans ((h q2 q3 q4 q1 ((q0 ◇ q4) ◇ q0)).symm)
  have apc3 : forall (q5 q6 q7 q8 q9 q10 q11:G), (((q5 ◇ q6) ◇ q11) ◇ (q9 ◇ q10)) = (q7 ◇ q8):=by
    intro q5 q6 q7 q8 q9 q10 q11
    exact (((apc2 q5 q6 q7 q8 q5).symm).trans ((apc2 q9 q10 (q8 ◇ q5) (q5 ◇ q6) q11).symm)).symm
  have apc4 : forall (q5 q6 q7 q8 q9 q10 q11:G), (q7 ◇ q8) = (q5 ◇ q5):=by
    intro q5 q6 q7 q8 q9 q10 q11
    exact ((apc3 q5 q6 q7 q8 q9 q10 q11).symm).trans (apc3 q5 q6 q5 q5 q9 q10 q11)
  exact (apc4 (x ◇ y) (x ◇ y) x y (x ◇ y) (x ◇ y) (x ◇ y)).trans ((apc4 (x ◇ y) (x ◇ y) ((z ◇ (w ◇ u)) ◇ u) u (x ◇ y) (x ◇ y) (x ◇ y)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_47284_to_52921 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_47284_to_52921
