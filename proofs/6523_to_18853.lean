-- Equation6523 → Equation18853
-- Recorded verdict: true
-- Premise: x = x * (y * ((x * z) * (x * z)))
-- Conclusion: x = (x * y) * ((z * x) * (x * x))
-- Original submission SHA-256: 5bf908300e465c6a76f9afaf6b04d007c229191ed5f8e2ea3ec1fa781bbec933
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = x ◇ (y ◇ ((x ◇ z) ◇ (x ◇ z)))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (x ◇ y) ◇ ((z ◇ x) ◇ (x ◇ x))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (q0 q1:G), ((q1 ◇ q0) ◇ q1) = (q1 ◇ q0):=by
    intro q0 q1
    exact ((congrArg (fun t => (q1 ◇ q0) ◇ t) ((h q1 ((q1 ◇ q0) ◇ (q1 ◇ q0)) q0).symm)).symm).trans ((h (q1 ◇ q0) q1 (q1 ◇ q0)).symm)
  have apc1 : forall (q2 q3:G), ((q3 ◇ q2) ◇ (q3 ◇ q2)) = (q3 ◇ q2):=by
    intro q2 q3
    exact (((congrArg (fun t => t ◇ (q3 ◇ q2)) (apc0 q2 q3)).symm).trans (apc0 q3 (q3 ◇ q2))).trans (apc0 q2 q3)
  have apc2 : forall (q4 q5 q6:G), (q4 ◇ (q5 ◇ (q4 ◇ q6))) = q4:=by
    intro q4 q5 q6
    exact ((congrArg (fun t => q4 ◇ t) (congrArg (fun t => q5 ◇ t) (apc1 q6 q4))).symm).trans ((h q4 q5 q6).symm)
  have apc7 : forall (q7 q8:G), (q7 ◇ q8) = q7:=by
    intro q7 q8
    exact ((congrArg (fun t => q7 ◇ t) (apc2 q8 q7 q7)).symm).trans (apc2 q7 q8 (q8 ◇ q7))
  exact ((apc7 x y).symm).trans ((apc7 (x ◇ y) ((z ◇ x) ◇ (x ◇ x))).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_6523_to_18853 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_6523_to_18853
