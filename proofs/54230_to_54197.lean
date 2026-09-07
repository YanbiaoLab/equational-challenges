-- Equation54230 → Equation54197
-- Recorded verdict: true
-- Premise: x ◇ (y ◇ y) = y ◇ (z ◇ (w ◇ x))
-- Conclusion: x ◇ (y ◇ y) = x ◇ (z ◇ (w ◇ u))
-- Original submission SHA-256: 264466f207a25c139c9121c6ea34d1d94df451f6338ca15a7ee264cefd63b3fe
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ (y ◇ y) = y ◇ (z ◇ (w ◇ x))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x ◇ (y ◇ y) = x ◇ (z ◇ (w ◇ u))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w u
  have p0 : forall (x y z w:G), (y ◇ (z ◇ (w ◇ x))) = (y ◇ (x ◇ (x ◇ x))):=by
    intro x y z w
    exact ((h x y z w).symm).trans (h x y x x)
  have p1 : forall (q0 q1 q2 q3:G), (q2 ◇ (q1 ◇ (q3 ◇ q3))) = ((q0 ◇ q1) ◇ (q2 ◇ q2)):=by
    intro q0 q1 q2 q3
    exact ((congrArg (fun t => q2 ◇ t) ((h q1 q3 q0 q0).symm)).symm).trans ((h (q0 ◇ q1) q2 q3 q0).symm)
  have p2 : forall (q0 q1 q2 q3:G), ((q0 ◇ q3) ◇ (q2 ◇ q2)) = (q1 ◇ (q2 ◇ q2)):=by
    intro q0 q1 q2 q3
    exact ((p1 q0 q3 q2 q1).symm).trans ((h q1 q2 q3 q1).symm)
  have p3 : forall (q0 q1 q2 q3:G), (q1 ◇ (q2 ◇ q2)) = (q0 ◇ (q2 ◇ q2)):=by
    intro q0 q1 q2 q3
    exact ((p2 q0 q1 q2 q3).symm).trans (p2 q0 q0 q2 q3)
  have p4 : forall (x y z w:G), (y ◇ (x ◇ (x ◇ x))) = (x ◇ (y ◇ y)):=by
    intro x y z w
    exact ((h x y x x).trans (p0 x y x x)).symm
  have p5 : forall (q0 q1 q2:G), ((q0 ◇ q2) ◇ (q1 ◇ q1)) = (q2 ◇ (q1 ◇ q1)):=by
    intro q0 q1 q2
    exact (((p4 q2 q1 q0 q0).symm).trans (p1 q0 q2 q1 q2)).symm
  have p6 : forall (q0 q1 q2:G), (q0 ◇ (q2 ◇ q2)) = (q0 ◇ (q1 ◇ q1)):=by
    intro q0 q1 q2
    exact ((p4 q0 q2 (q2 ◇ (q0 ◇ (q0 ◇ q0))) (q2 ◇ (q0 ◇ (q0 ◇ q0)))).symm).trans ((((congrArg (fun t => q2 ◇ t) (p5 q0 q0 q0)).symm).trans (p3 q1 q2 (q0 ◇ q0) q0)).trans ((congrArg (fun t => q1 ◇ t) (p5 q0 q0 q0)).trans (p4 q0 q1 (q1 ◇ (q0 ◇ (q0 ◇ q0))) (q1 ◇ (q0 ◇ (q0 ◇ q0))))))
  have p7 : forall (q0 q1 q2:G), (q0 ◇ (q1 ◇ q1)) = (q0 ◇ (q0 ◇ q0)):=by
    intro q0 q1 q2
    exact ((p6 q0 q1 q2).symm).trans (p6 q0 q0 q2)
  have p8 : forall (q0 q1 q2 q3:G), (q2 ◇ (q0 ◇ q0)) = (q1 ◇ (q1 ◇ q1)):=by
    intro q0 q1 q2 q3
    exact (((p6 q2 q0 q3).symm).trans (p3 q1 q2 q3 q0)).trans (p7 q1 q3 (q1 ◇ (q3 ◇ q3)))
  have p9 : forall (q0 q1 q2 q3:G), (q3 ◇ (q2 ◇ q2)) = (q1 ◇ (q0 ◇ q0)):=by
    intro q0 q1 q2 q3
    exact ((p8 q0 q0 q1 q0).trans ((p8 q2 q0 q3 q0).symm)).symm
  exact (calc
    (x ◇ (y ◇ y)) = (u ◇ (x ◇ x)):=p9 x u y x
    _ = (x ◇ (z ◇ (w ◇ u))):=((h u x z w).symm).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_54230_to_54197 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_54230_to_54197
