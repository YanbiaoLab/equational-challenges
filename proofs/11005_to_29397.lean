-- Equation11005 → Equation29397
-- Recorded verdict: true
-- Premise: x = x * ((y * (z * z)) * (z * w))
-- Conclusion: x = (x * (y * (z * (y * x)))) * w
-- Original submission SHA-256: 95d7554e35d4aea9a4df507ca26b6c5be3b0c9dda968473bd34dbe60eab79e86
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = x ◇ ((y ◇ (z ◇ z)) ◇ (z ◇ w))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = (x ◇ (y ◇ (z ◇ (y ◇ x)))) ◇ w
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc0 : forall (q0 q1 q2:G), (q0 ◇ ((q1 ◇ (q2 ◇ q2)) ◇ q2)) = q0:=by
    intro q0 q1 q2
    exact ((congrArg (fun t => q0 ◇ t) (congrArg (fun t => (q1 ◇ (q2 ◇ q2)) ◇ t) ((h q2 q0 q0 q0).symm))).symm).trans ((h q0 q1 q2 ((q0 ◇ (q0 ◇ q0)) ◇ (q0 ◇ q0))).symm)
  have apc1 : forall (q3 q4 q5 q6:G), (q3 ◇ q4) = q3:=by
    intro q3 q4 q5 q6
    exact (((congrArg (fun t => q3 ◇ t) (congrArg (fun t => q4 ◇ t) (apc0 ((q5 ◇ (q6 ◇ q6)) ◇ q6) q5 q6))).trans (congrArg (fun t => q3 ◇ t) (apc0 q4 q5 q6))).symm).trans (((congrArg (fun t => q3 ◇ t) (apc0 (q4 ◇ (((q5 ◇ (q6 ◇ q6)) ◇ q6) ◇ ((q5 ◇ (q6 ◇ q6)) ◇ q6))) q5 q6)).symm).trans (apc0 q3 q4 ((q5 ◇ (q6 ◇ q6)) ◇ q6)))
  exact ((apc1 x (y ◇ (z ◇ (y ◇ x))) x x).symm).trans ((apc1 (x ◇ (y ◇ (z ◇ (y ◇ x)))) w x x).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_11005_to_29397 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_11005_to_29397
