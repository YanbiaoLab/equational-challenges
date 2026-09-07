-- Equation50908 → Equation49345
-- Recorded verdict: true
-- Premise: x * y = (z * ((y * y) * z)) * z
-- Conclusion: x * y = ((z * w) * z) * (z * z)
-- Original submission SHA-256: 9e827cdc10aadfab765ea49fd09331c542c53553d985066d29b3df06591a7ba9
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = (z ◇ ((y ◇ y) ◇ z)) ◇ z
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = ((z ◇ w) ◇ z) ◇ (z ◇ z)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc0 : forall (x y z:G), (y ◇ y) = (x ◇ y):=by
    intro x y z
    exact ((h x y z).trans ((h y y z).symm)).symm
  have apc1 : forall (q0 q1 q2:G), (((q2 ◇ q2) ◇ (q0 ◇ (q2 ◇ q2))) ◇ (q2 ◇ q2)) = (q1 ◇ q2):=by
    intro q0 q1 q2
    exact ((congrArg (fun t => t ◇ (q2 ◇ q2)) (congrArg (fun t => (q2 ◇ q2) ◇ t) (apc0 q0 (q2 ◇ q2) q0))).symm).trans ((h q1 q2 (q2 ◇ q2)).symm)
  have apc2 : forall (q3 q4:G), ((q4 ◇ q4) ◇ (q4 ◇ q4)) = (q3 ◇ q4):=by
    intro q3 q4
    exact (((apc1 q3 q3 q4).symm).trans ((apc0 ((q4 ◇ q4) ◇ (q3 ◇ (q4 ◇ q4))) (q4 ◇ q4) q3).symm)).symm
  have apc3 : forall (q5 q6 q7:G), ((q7 ◇ q7) ◇ (q7 ◇ q7)) = (q5 ◇ q6):=by
    intro q5 q6 q7
    exact (apc2 (q7 ◇ ((q6 ◇ q6) ◇ q7)) q7).trans ((h q5 q6 q7).symm)
  exact ((apc3 x y (x ◇ y)).symm).trans (apc3 ((z ◇ w) ◇ z) (z ◇ z) (x ◇ y))

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_50908_to_49345 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_50908_to_49345
