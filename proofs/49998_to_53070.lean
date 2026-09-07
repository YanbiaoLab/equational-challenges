-- Equation49998 → Equation53070
-- Recorded verdict: true
-- Premise: x * y = (z * (x * (w * u))) * x
-- Conclusion: x * x = (((y * z) * x) * w) * z
-- Original submission SHA-256: 5490bde1c6f81b1599c1ff98ee9850a007c7ad75aecc2f3b238ed89cf1b6a87d
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x ◇ y = (z ◇ (x ◇ (w ◇ u))) ◇ x
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ x = (((y ◇ z) ◇ x) ◇ w) ◇ z
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc0 : forall (x y z w u:G), (x ◇ y) = (x ◇ x):=by
    intro x y z w u
    exact (h x y z w u).trans ((h x x z w u).symm)
  have apc4 : forall (q0 q1 q2 q3 q4:G), ((q1 ◇ q1) ◇ (q1 ◇ q1)) = (q2 ◇ q0):=by
    intro q0 q1 q2 q3 q4
    exact (((h q2 q0 q1 q3 q4).trans (apc0 (q1 ◇ (q2 ◇ (q3 ◇ q4))) q2 q4 q4 q4)).trans ((((congrArg (fun t => t ◇ (q1 ◇ (q2 ◇ (q3 ◇ q4)))) (congrArg (fun t => q1 ◇ t) (apc0 q2 (q3 ◇ q4) (q2 ◇ (q3 ◇ q4)) (q2 ◇ (q3 ◇ q4)) (q2 ◇ (q3 ◇ q4))))).trans (congrArg (fun t => (q1 ◇ (q2 ◇ q2)) ◇ t) (congrArg (fun t => q1 ◇ t) (apc0 q2 (q3 ◇ q4) (q2 ◇ (q3 ◇ q4)) (q2 ◇ (q3 ◇ q4)) (q2 ◇ (q3 ◇ q4)))))).trans (congrArg (fun t => t ◇ (q1 ◇ (q2 ◇ q2))) (apc0 q1 (q2 ◇ q2) (q1 ◇ (q2 ◇ q2)) (q1 ◇ (q2 ◇ q2)) (q1 ◇ (q2 ◇ q2))))).trans (congrArg (fun t => (q1 ◇ q1) ◇ t) (apc0 q1 (q2 ◇ q2) (q1 ◇ (q2 ◇ q2)) (q1 ◇ (q2 ◇ q2)) (q1 ◇ (q2 ◇ q2)))))).symm
  exact ((apc4 x (x ◇ x) x (x ◇ x) (x ◇ x)).symm).trans (apc4 z (x ◇ x) (((y ◇ z) ◇ x) ◇ w) (x ◇ x) (x ◇ x))

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_49998_to_53070 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_49998_to_53070
