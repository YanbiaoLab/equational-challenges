-- Equation52903 → Equation62140
-- Recorded verdict: true
-- Premise: x * y = ((z * (w * u)) * y) * u
-- Conclusion: (x * y) * y = ((z * x) * w) * x
-- Original submission SHA-256: b5d31c437f9bd6c4843b54f7c234eb0ac32f6d7affccff2bc84f08af86553921
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x ◇ y = ((z ◇ (w ◇ u)) ◇ y) ◇ u
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), (x ◇ y) ◇ y = ((z ◇ x) ◇ w) ◇ x
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc0 : forall (q0 q1 q2 q3 q4:G), (((q0 ◇ q1) ◇ q4) ◇ q2) = (q3 ◇ q4):=by
    intro q0 q1 q2 q3 q4
    exact ((congrArg (fun t => t ◇ q2) (congrArg (fun t => t ◇ q4) ((h q0 q1 q0 q0 (q0 ◇ q2)).symm))).symm).trans ((h q3 q4 ((q0 ◇ (q0 ◇ (q0 ◇ q2))) ◇ q1) q0 q2).symm)
  have apc2 : forall (q0 q1 q2 q3 q4:G), (((q3 ◇ q3) ◇ q4) ◇ q3) = (((q0 ◇ q1) ◇ q4) ◇ q2):=by
    intro q0 q1 q2 q3 q4
    exact ((apc0 q0 q1 q2 q3 q4).trans ((apc0 q3 q3 q3 q3 q4).symm)).symm
  have apc3 : forall (q5 q6 q7 q8 q9:G), (((q8 ◇ q8) ◇ q9) ◇ q8) = ((q5 ◇ q6) ◇ q7):=by
    intro q5 q6 q7 q8 q9
    exact (((congrArg (fun t => t ◇ q7) (apc0 q5 q5 q9 q5 q6)).symm).trans ((apc2 (q5 ◇ q5) q6 q7 q8 q9).symm)).symm
  exact ((apc3 x y y ((x ◇ y) ◇ y) (((z ◇ x) ◇ w) ◇ x)).symm).trans (apc3 (z ◇ x) w x ((x ◇ y) ◇ y) (((z ◇ x) ◇ w) ◇ x))

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_52903_to_62140 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_52903_to_62140
