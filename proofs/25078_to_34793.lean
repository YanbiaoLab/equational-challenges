-- Equation25078 → Equation34793
-- Recorded verdict: true
-- Premise: x = (y ◇ (x ◇ (x ◇ x))) ◇ (z ◇ w)
-- Conclusion: x = ((y ◇ x) ◇ ((z ◇ x) ◇ x)) ◇ w
-- Original submission SHA-256: 519a8cbee72081ca25150b6422227150121f566c8a209d07578cb450837aa829
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = (y ◇ (x ◇ (x ◇ x))) ◇ (z ◇ w)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = ((y ◇ x) ◇ ((z ◇ x) ◇ x)) ◇ w
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc0 : forall (q0 q1 q2:G), ((q2 ◇ (q1 ◇ (q1 ◇ q1))) ◇ q0) = q1:=by
    intro q0 q1 q2
    exact ((congrArg (fun t => (q2 ◇ (q1 ◇ (q1 ◇ q1))) ◇ t) ((h q0 q0 q0 q0).symm)).symm).trans ((h q1 q2 (q0 ◇ (q0 ◇ (q0 ◇ q0))) (q0 ◇ q0)).symm)
  have apc1 : forall (q3 q4 q5:G), (q3 ◇ q4) = q5:=by
    intro q3 q4 q5
    exact ((congrArg (fun t => t ◇ q4) (apc0 (q5 ◇ (q5 ◇ q5)) q3 q3)).symm).trans (apc0 q4 q5 (q3 ◇ (q3 ◇ (q3 ◇ q3))))
  exact ((apc1 x x x).symm).trans ((apc1 ((y ◇ x) ◇ ((z ◇ x) ◇ x)) w (x ◇ x)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_25078_to_34793 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_25078_to_34793
