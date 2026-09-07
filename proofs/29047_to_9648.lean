-- Equation29047 → Equation9648
-- Recorded verdict: true
-- Premise: x = (((y * z) * z) * x) * (w * z)
-- Conclusion: x = y * ((z * x) * (w * (z * z)))
-- Original submission SHA-256: cbc9ed1e27ba3dc732085759adb76629759f564f7cabb67bebfe560660a37ebb
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = (((y ◇ z) ◇ z) ◇ x) ◇ (w ◇ z)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = y ◇ ((z ◇ x) ◇ (w ◇ (z ◇ z)))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc0 : forall (q0 q1 q2:G), (q2 ◇ (q1 ◇ q2)) = (q0 ◇ q2):=by
    intro q0 q1 q2
    exact ((congrArg (fun t => t ◇ (q1 ◇ q2)) ((h q2 q0 q2 q0).symm)).symm).trans ((h (q0 ◇ q2) (q0 ◇ q2) q2 q1).symm)
  have apc1 : forall (q0 q1 q2:G), (q1 ◇ q2) = (q0 ◇ q2):=by
    intro q0 q1 q2
    exact (((apc0 q0 q1 q2).symm).trans (apc0 q1 q1 q2)).symm
  have apc2 : forall (q3 q4 q5 q6:G), (q3 ◇ (q4 ◇ q6)) = q5:=by
    intro q3 q4 q5 q6
    exact ((apc1 q3 (((q3 ◇ q6) ◇ q6) ◇ q5) (q4 ◇ q6)).symm).trans ((h q5 q3 q6 q4).symm)
  have apc3 : forall (q3 q5 q4 q6:G), q5 = q3:=by
    intro q3 q5 q4 q6
    exact ((apc2 q3 q4 q5 q6).symm).trans (apc2 q3 q4 q3 q6)
  exact (apc3 x x x x).trans ((apc3 x (y ◇ ((z ◇ x) ◇ (w ◇ (z ◇ z)))) x x).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_29047_to_9648 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_29047_to_9648
