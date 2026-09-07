-- Equation43011 → Equation56920
-- Recorded verdict: true
-- Premise: x * y = z * (y * ((y * y) * z))
-- Conclusion: x * (y * y) = (z * (w * x)) * w
-- Original submission SHA-256: 9203480182607433fcf169a0d57feee84a09797fbfd149b064d92a3b86665398
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = z ◇ (y ◇ ((y ◇ y) ◇ z))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ (y ◇ y) = (z ◇ (w ◇ x)) ◇ w
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc0 : forall (x y z:G), (y ◇ y) = (x ◇ y):=by
    intro x y z
    exact ((h x y z).trans ((h y y z).symm)).symm
  have apc1 : forall (q0 q1 q2:G), (q1 ◇ q2) = (q0 ◇ q2):=by
    intro q0 q1 q2
    exact ((h q0 q2 q0).trans ((h q1 q2 q0).symm)).symm
  have apc2 : forall (q3 q4 q5:G), (q5 ◇ (q4 ◇ (q5 ◇ q5))) = (q3 ◇ q4):=by
    intro q3 q4 q5
    exact ((congrArg (fun t => q5 ◇ t) (congrArg (fun t => q4 ◇ t) ((apc0 (q4 ◇ q4) q5 q3).symm))).symm).trans ((h q3 q4 q5).symm)
  have apc6 : forall (q6 q7 q8 q9:G), (q9 ◇ (q6 ◇ (q9 ◇ q9))) = (q7 ◇ q8):=by
    intro q6 q7 q8 q9
    exact ((congrArg (fun t => q9 ◇ t) (apc1 q6 q8 (q9 ◇ q9))).symm).trans (apc2 q7 q8 q9)
  exact ((apc6 ((z ◇ (w ◇ x)) ◇ w) x (y ◇ y) (x ◇ (y ◇ y))).symm).trans (apc6 ((z ◇ (w ◇ x)) ◇ w) (z ◇ (w ◇ x)) w (x ◇ (y ◇ y)))

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_43011_to_56920 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_43011_to_56920
