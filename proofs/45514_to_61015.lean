-- Equation45514 → Equation61015
-- Recorded verdict: true
-- Premise: x * y = y * (((z * z) * w) * w)
-- Conclusion: (x * x) * y = (z * (w * w)) * x
-- Original submission SHA-256: 74f23ced4f7aaec680d7703eacde63c790fd3ed2f3422929385931e7171d6519
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = y ◇ (((z ◇ z) ◇ w) ◇ w)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), (x ◇ x) ◇ y = (z ◇ (w ◇ w)) ◇ x
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc0 : forall (x y z w:G), (y ◇ y) = (x ◇ y):=by
    intro x y z w
    exact ((h x y z w).trans ((h y y z w).symm)).symm
  have apc2 : forall (q0 q1 q2:G), (q2 ◇ (q0 ◇ q0)) = (q1 ◇ q2):=by
    intro q0 q1 q2
    exact ((congrArg (fun t => q2 ◇ t) ((apc0 ((q0 ◇ q0) ◇ q0) q0 q0 q0).symm)).symm).trans ((h q1 q2 q0 q0).symm)
  have apc3 : forall (q3 q4 q5:G), ((q3 ◇ q3) ◇ (q3 ◇ q3)) = (q4 ◇ q5):=by
    intro q3 q4 q5
    exact (((apc2 q3 q4 q5).symm).trans ((apc0 q5 (q3 ◇ q3) q3 q3).symm)).symm
  exact ((apc3 ((x ◇ x) ◇ y) (x ◇ x) y).symm).trans (apc3 ((x ◇ x) ◇ y) (z ◇ (w ◇ w)) x)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_45514_to_61015 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_45514_to_61015
