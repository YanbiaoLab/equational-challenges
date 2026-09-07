-- Equation18658 → Equation21978
-- Recorded verdict: true
-- Premise: x = (y * z) * (w * ((z * u) * x))
-- Conclusion: x = (y * (z * y)) * (z * (y * x))
-- Original submission SHA-256: bf86267921a4332809435ebeb02200177dc2eae363b103f5f6d375030cc23622
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x = (y ◇ z) ◇ (w ◇ ((z ◇ u) ◇ x))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (y ◇ (z ◇ y)) ◇ (z ◇ (y ◇ x))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (q0 q1 q2 q3 q4 q5:G), ((q5 ◇ (q1 ◇ q2)) ◇ (q3 ◇ (q0 ◇ q4))) = q4:=by
    intro q0 q1 q2 q3 q4 q5
    exact ((congrArg (fun t => (q5 ◇ (q1 ◇ q2)) ◇ t) (congrArg (fun t => q3 ◇ t) (congrArg (fun t => t ◇ q4) ((h q0 q1 q2 q0 q0).symm)))).symm).trans ((h q4 q5 (q1 ◇ q2) q3 (q0 ◇ ((q2 ◇ q0) ◇ q0))).symm)
  have apc1 : forall (q6 q7 q8 q9 q10:G), ((q10 ◇ q6) ◇ (q8 ◇ (q7 ◇ q9))) = q9:=by
    intro q6 q7 q8 q9 q10
    exact ((congrArg (fun t => t ◇ (q8 ◇ (q7 ◇ q9))) (congrArg (fun t => q10 ◇ t) (apc0 q6 q6 q6 q6 q6 q6))).symm).trans (apc0 q7 (q6 ◇ (q6 ◇ q6)) (q6 ◇ (q6 ◇ q6)) q8 q9 q10)
  exact (calc
    x = x:=rfl
    _ = ((y ◇ (z ◇ y)) ◇ (z ◇ (y ◇ x))):=(apc1 (z ◇ y) y z x y).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_18658_to_21978 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_18658_to_21978
