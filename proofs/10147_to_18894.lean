-- Equation10147 → Equation18894
-- Recorded verdict: true
-- Premise: x = x * ((y * z) * ((w * z) * w))
-- Conclusion: x = (x * y) * ((z * z) * (y * w))
-- Original submission SHA-256: 01a9e109b33aa53ed78920b54c8392843d6b43a7cef1031934994b46d917f444
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = x ◇ ((y ◇ z) ◇ ((w ◇ z) ◇ w))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = (x ◇ y) ◇ ((z ◇ z) ◇ (y ◇ w))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc0 : forall (q0 q1 q2:G), (q0 ◇ (q1 ◇ q2)) = q0:=by
    intro q0 q1 q2
    exact ((congrArg (fun t => q0 ◇ t) ((h (q1 ◇ q2) ((q0 ◇ q2) ◇ q0) q2 q0).symm)).symm).trans ((h q0 q1 q2 ((q0 ◇ q2) ◇ q0)).symm)
  have apc1 : forall (q3 q4 q5 q6 q7:G), (q3 ◇ q4) = q3:=by
    intro q3 q4 q5 q6 q7
    exact (((congrArg (fun t => q3 ◇ t) (congrArg (fun t => q4 ◇ t) (congrArg (fun t => t ◇ q5) (apc0 q5 q6 q7)))).trans (congrArg (fun t => q3 ◇ t) (apc0 q4 q5 q5))).symm).trans (((congrArg (fun t => q3 ◇ t) (congrArg (fun t => t ◇ ((q5 ◇ (q6 ◇ q7)) ◇ q5)) (apc0 q4 q6 q7))).symm).trans ((h q3 q4 (q6 ◇ q7) q5).symm))
  exact ((apc1 x y x x x).symm).trans ((apc1 (x ◇ y) ((z ◇ z) ◇ (y ◇ w)) x x x).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_10147_to_18894 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_10147_to_18894
