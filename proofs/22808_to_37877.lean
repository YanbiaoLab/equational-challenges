-- Equation22808 → Equation37877
-- Recorded verdict: true
-- Premise: x = (y ◇ (z ◇ x)) ◇ ((w ◇ w) ◇ z)
-- Conclusion: x = ((y ◇ (z ◇ (z ◇ w))) ◇ u) ◇ w
-- Original submission SHA-256: 53468565069e376bdf9293d0249ba37fca2872d2cace7bb8f4993b6844044bd8
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = (y ◇ (z ◇ x)) ◇ ((w ◇ w) ◇ z)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x = ((y ◇ (z ◇ (z ◇ w))) ◇ u) ◇ w
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w u
  have apc0 : forall (q0 q1 q2 q3 q4:G), ((q4 ◇ (((q0 ◇ q0) ◇ q2) ◇ q3)) ◇ q1) = q3:=by
    intro q0 q1 q2 q3 q4
    exact ((congrArg (fun t => (q4 ◇ (((q0 ◇ q0) ◇ q2) ◇ q3)) ◇ t) ((h q1 (q2 ◇ q1) q2 q0).symm)).symm).trans ((h q3 q4 ((q0 ◇ q0) ◇ q2) (q2 ◇ q1)).symm)
  have apc3 : forall (q5 q6 q7:G), (q5 ◇ q6) = q7:=by
    intro q5 q6 q7
    exact ((congrArg (fun t => t ◇ q6) (apc0 q5 (((q5 ◇ q5) ◇ q5) ◇ q7) q5 q5 q5)).symm).trans (apc0 q5 q6 q5 q7 (q5 ◇ (((q5 ◇ q5) ◇ q5) ◇ q5)))
  exact ((apc3 z x x).symm).trans ((apc3 ((y ◇ (z ◇ (z ◇ w))) ◇ u) w (z ◇ x)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_22808_to_37877 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_22808_to_37877
