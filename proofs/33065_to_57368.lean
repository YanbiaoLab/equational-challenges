-- Equation33065 → Equation57368
-- Recorded verdict: true
-- Premise: x = (y * (((x * z) * y) * w)) * x
-- Conclusion: x * (x * y) = ((x * x) * x) * y
-- Original submission SHA-256: 62d63fdd5cf6389faacb72974631741340d2c05e511f31d4d5b9252bc86a2b53
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = (y ◇ (((x ◇ z) ◇ y) ◇ w)) ◇ x
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x ◇ (x ◇ y) = ((x ◇ x) ◇ x) ◇ y
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y
  have apc0 : forall (q0 q1 q2:G), ((q2 ◇ (q2 ◇ q0)) ◇ q1) = q1:=by
    intro q0 q1 q2
    exact ((congrArg (fun t => t ◇ q1) (congrArg (fun t => q2 ◇ t) (congrArg (fun t => t ◇ q0) ((h q2 q1 q0 q0).symm)))).symm).trans ((h q1 q2 (((q2 ◇ q0) ◇ q1) ◇ q0) q0).symm)
  have apc1 : forall (q3 q4 q5 q6:G), (q3 ◇ q4) = q4:=by
    intro q3 q4 q5 q6
    exact ((congrArg (fun t => t ◇ q4) (apc0 q5 q3 q6)).symm).trans (((congrArg (fun t => t ◇ q4) (apc0 q5 ((q6 ◇ (q6 ◇ q5)) ◇ q3) q6)).symm).trans (apc0 q3 q4 (q6 ◇ (q6 ◇ q5))))
  exact (calc
    (x ◇ (x ◇ y)) = y:=(congrArg (fun t => x ◇ t) (apc1 x y (x ◇ y) (x ◇ y))).trans (apc1 x y (x ◇ y) (x ◇ y))
    _ = (((x ◇ x) ◇ x) ◇ y):=(((congrArg (fun t => t ◇ y) (congrArg (fun t => t ◇ x) (apc1 x x (x ◇ x) (x ◇ x)))).trans (congrArg (fun t => t ◇ y) (apc1 x x (x ◇ x) (x ◇ x)))).trans (apc1 x y (x ◇ y) (x ◇ y))).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_33065_to_57368 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_33065_to_57368
