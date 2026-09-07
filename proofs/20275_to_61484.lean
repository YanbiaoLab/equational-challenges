-- Equation20275 → Equation61484
-- Recorded verdict: true
-- Premise: x = (y * z) * ((z * (x * w)) * x)
-- Conclusion: (x * y) * z = (z * (x * x)) * z
-- Original submission SHA-256: 69f21f52a738f5be29939fe91e7e984388a627d9c27446df8052d69638cdea30
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = (y ◇ z) ◇ ((z ◇ (x ◇ w)) ◇ x)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), (x ◇ y) ◇ z = (z ◇ (x ◇ x)) ◇ z
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (q0 q1 q2 q3 q4:G), ((q3 ◇ q4) ◇ ((q4 ◇ q0) ◇ (q1 ◇ q2))) = (q1 ◇ q2):=by
    intro q0 q1 q2 q3 q4
    exact ((congrArg (fun t => (q3 ◇ q4) ◇ t) (congrArg (fun t => t ◇ (q1 ◇ q2)) (congrArg (fun t => q4 ◇ t) ((h q0 q1 q2 q0).symm)))).symm).trans ((h (q1 ◇ q2) q3 q4 ((q2 ◇ (q0 ◇ q0)) ◇ q0)).symm)
  have apc1 : forall (q5 q6 q7 q8 q9:G), ((q6 ◇ (q7 ◇ q5)) ◇ q7) = ((q8 ◇ q9) ◇ q7):=by
    intro q5 q6 q7 q8 q9
    exact (((congrArg (fun t => (q8 ◇ q9) ◇ t) ((h q7 q9 q6 q5).symm)).symm).trans (apc0 q6 (q6 ◇ (q7 ◇ q5)) q7 q8 q9)).symm
  exact ((apc1 ((x ◇ y) ◇ z) ((z ◇ (x ◇ x)) ◇ z) z x y).symm).trans (apc1 ((x ◇ y) ◇ z) ((z ◇ (x ◇ x)) ◇ z) z z (x ◇ x))

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_20275_to_61484 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_20275_to_61484
