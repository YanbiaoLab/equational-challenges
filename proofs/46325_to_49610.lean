-- Equation46325 → Equation49610
-- Recorded verdict: true
-- Premise: x * y = (y * y) * (z * (x * x))
-- Conclusion: x * x = (y * (z * (w * z))) * y
-- Original submission SHA-256: 42be9b4ecfff5e77f68aedbdba970750fc44839e9f75db8446fc0c803c2b4b44
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = (y ◇ y) ◇ (z ◇ (x ◇ x))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ x = (y ◇ (z ◇ (w ◇ z))) ◇ y
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc0 : forall (q0 q1 q2:G), ((q2 ◇ q2) ◇ (q0 ◇ q1)) = ((q0 ◇ q0) ◇ q2):=by
    intro q0 q1 q2
    exact ((congrArg (fun t => (q2 ◇ q2) ◇ t) ((h q0 q1 (q0 ◇ q0)).symm)).symm).trans ((h (q0 ◇ q0) q2 (q1 ◇ q1)).symm)
  have apc1 : forall (x y z q0 q1 q2:G), ((z ◇ z) ◇ y) = (x ◇ y):=by
    intro x y z q0 q1 q2
    exact ((h x y z).trans (apc0 z (x ◇ x) y)).symm
  have apc5 : forall (q3 q4 q5 q6:G), ((q6 ◇ q6) ◇ q3) = (q4 ◇ q5):=by
    intro q3 q4 q5 q6
    exact ((apc0 q6 (q4 ◇ q4) q3).symm).trans ((apc1 (q5 ◇ q5) (q6 ◇ (q4 ◇ q4)) q3 q3 q3 q3).trans ((h q4 q5 q6).symm))
  have apc6 : forall (q3 q4 q5 q6:G), (q4 ◇ q5) = (q3 ◇ q3):=by
    intro q3 q4 q5 q6
    exact ((apc5 q3 q4 q5 q3).symm).trans (apc5 q3 q3 q3 q3)
  exact (apc6 (x ◇ x) x x (x ◇ x)).trans ((apc6 (x ◇ x) (y ◇ (z ◇ (w ◇ z))) y (x ◇ x)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_46325_to_49610 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_46325_to_49610
