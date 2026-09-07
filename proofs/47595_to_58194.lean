-- Equation47595 → Equation58194
-- Recorded verdict: true
-- Premise: x * y = (z * w) * ((z * w) * y)
-- Conclusion: (x * x) * x = x * (x * (y * x))
-- Original submission SHA-256: b2c889b0b43fbf31f8ff335b6aa75b7f0e960fdf3238ec7ee6198596bc4e29fd
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = (z ◇ w) ◇ ((z ◇ w) ◇ y)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), (x ◇ x) ◇ x = x ◇ (x ◇ (y ◇ x))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y
  have apc0 : forall (x y z w:G), (y ◇ y) = (x ◇ y):=by
    intro x y z w
    exact ((h x y z w).trans ((h y y z w).symm)).symm
  have apc2 : forall (q0 q1 q2 q3:G), ((q3 ◇ q0) ◇ (q2 ◇ q2)) = (q1 ◇ q2):=by
    intro q0 q1 q2 q3
    exact ((congrArg (fun t => (q3 ◇ q0) ◇ t) ((apc0 (q3 ◇ q0) q2 q0 q0).symm)).symm).trans ((h q1 q2 q3 q0).symm)
  have apc3 : forall (q4 q5 q6:G), (q6 ◇ (q4 ◇ q4)) = (q5 ◇ q4):=by
    intro q4 q5 q6
    exact (((apc2 q4 q5 q4 q4).symm).trans (apc0 q6 (q4 ◇ q4) q4 q4)).symm
  have apc9 : forall (q7 q8 q9 q10:G), (q10 ◇ (q7 ◇ q8)) = (q9 ◇ q8):=by
    intro q7 q8 q9 q10
    exact ((congrArg (fun t => q10 ◇ t) (apc0 q7 q8 q7 q7)).symm).trans (apc3 q8 q9 q10)
  exact ((apc9 y x (x ◇ x) ((x ◇ x) ◇ x)).symm).trans ((apc9 x (y ◇ x) ((x ◇ x) ◇ x) x).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_47595_to_58194 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_47595_to_58194
