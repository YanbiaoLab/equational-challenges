-- Equation1765 → Equation22081
-- Recorded verdict: true
-- Premise: x = (y ◇ z) ◇ ((x ◇ z) ◇ z)
-- Conclusion: x = (y ◇ (z ◇ z)) ◇ (w ◇ (z ◇ w))
-- Original submission SHA-256: 4336abd98daa5781e120881f8c8b5d899b2788f22aef8aac5b7c1b663b95e9bb
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (y ◇ z) ◇ ((x ◇ z) ◇ z)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = (y ◇ (z ◇ z)) ◇ (w ◇ (z ◇ w))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc2 : forall (q0 q1 q2:G), (q0 ◇ ((q2 ◇ ((q0 ◇ q1) ◇ q1)) ◇ ((q0 ◇ q1) ◇ q1))) = q2:=by
    intro q0 q1 q2
    exact ((congrArg (fun t => t ◇ ((q2 ◇ ((q0 ◇ q1) ◇ q1)) ◇ ((q0 ◇ q1) ◇ q1))) ((h q0 q0 q1).symm)).symm).trans ((h q2 (q0 ◇ q1) ((q0 ◇ q1) ◇ q1)).symm)
  have apc3 : forall (q3 q4 q5:G), (q4 ◇ (q4 ◇ ((q4 ◇ q5) ◇ q5))) = (q3 ◇ q5):=by
    intro q3 q4 q5
    exact ((congrArg (fun t => q4 ◇ t) (congrArg (fun t => t ◇ ((q4 ◇ q5) ◇ q5)) ((h q4 q3 q5).symm))).symm).trans (apc2 q4 q5 (q3 ◇ q5))
  have apc4 : forall (q3 q4 q5:G), (q4 ◇ q5) = (q3 ◇ q5):=by
    intro q3 q4 q5
    exact (((apc3 q3 q4 q5).symm).trans (apc3 q4 q4 q5)).symm
  have apc6 : forall (q6 q7 q8 q9:G), q7 = q6:=by
    intro q6 q7 q8 q9
    exact (((apc2 q8 q9 q6).symm).trans (((congrArg (fun t => q8 ◇ t) (congrArg (fun t => t ◇ ((q8 ◇ q9) ◇ q9)) (apc4 q6 q7 ((q8 ◇ q9) ◇ q9)))).symm).trans (apc2 q8 q9 q7))).symm
  exact (apc6 x x x x).trans ((apc6 x ((y ◇ (z ◇ z)) ◇ (w ◇ (z ◇ w))) x x).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_1765_to_22081 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_1765_to_22081
