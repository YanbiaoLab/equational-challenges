-- Equation26515 → Equation3258
-- Recorded verdict: true
-- Premise: x = (y * ((z * w) * y)) * (z * x)
-- Conclusion: x * x = x * (y * (x * x))
-- Original submission SHA-256: c4d30b84431e05bd8906c60e3757587eda5d3a1dcb4100a713bfe5b6d6a7ceee
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = (y ◇ ((z ◇ w) ◇ y)) ◇ (z ◇ x)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x ◇ x = x ◇ (y ◇ (x ◇ x))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y
  have apc0 : forall (q0 q1 q2 q3:G), (((q1 ◇ q0) ◇ q0) ◇ (q3 ◇ q2)) = q2:=by
    intro q0 q1 q2 q3
    exact ((congrArg (fun t => t ◇ (q3 ◇ q2)) (congrArg (fun t => (q1 ◇ q0) ◇ t) ((h q0 q3 q1 q0).symm))).symm).trans ((h q2 (q1 ◇ q0) q3 ((q1 ◇ q0) ◇ q3)).symm)
  have apc1 : forall (q4 q5 q6:G), (q4 ◇ (q6 ◇ q5)) = q5:=by
    intro q4 q5 q6
    exact ((congrArg (fun t => t ◇ (q6 ◇ q5)) (apc0 (q4 ◇ q4) q4 q4 q4)).symm).trans (apc0 (q4 ◇ q4) (q4 ◇ (q4 ◇ q4)) q5 q6)
  exact (apc1 x (x ◇ x) y).symm

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_26515_to_3258 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_26515_to_3258
