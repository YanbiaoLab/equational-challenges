-- Equation21315 → Equation22290
-- Recorded verdict: true
-- Premise: x = (y * z) * (((w * w) * u) * x)
-- Conclusion: x = (x * (y * x)) * ((x * y) * x)
-- Original submission SHA-256: 20cbc4f401b87f7eccd8de44f950f24122b6621e12ecb7434b77dc21345d2039
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x = (y ◇ z) ◇ (((w ◇ w) ◇ u) ◇ x)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x = (x ◇ (y ◇ x)) ◇ ((x ◇ y) ◇ x)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y
  have apc0 : forall (q0 q1 q2 q3 q4:G), ((q3 ◇ q4) ◇ ((q0 ◇ q1) ◇ q2)) = q2:=by
    intro q0 q1 q2 q3 q4
    exact ((congrArg (fun t => (q3 ◇ q4) ◇ t) (congrArg (fun t => t ◇ q2) (congrArg (fun t => t ◇ q1) ((h q0 ((q0 ◇ q0) ◇ q0) q0 q0 q0).symm)))).symm).trans ((h q2 q3 q4 (((q0 ◇ q0) ◇ q0) ◇ q0) q1).symm)
  have apc1 : forall (q5 q6 q7 q8:G), (q5 ◇ ((q6 ◇ q7) ◇ q8)) = q8:=by
    intro q5 q6 q7 q8
    exact ((congrArg (fun t => t ◇ ((q6 ◇ q7) ◇ q8)) (apc0 q5 q5 q5 q5 q5)).symm).trans (apc0 q6 q7 q8 (q5 ◇ q5) ((q5 ◇ q5) ◇ q5))
  exact (calc
    x = x:=rfl
    _ = ((x ◇ (y ◇ x)) ◇ ((x ◇ y) ◇ x)):=(apc1 (x ◇ (y ◇ x)) x y x).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_21315_to_22290 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_21315_to_22290
