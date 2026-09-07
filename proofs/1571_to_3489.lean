-- Equation1571 → Equation3489
-- Recorded verdict: true
-- Premise: x = (y ◇ z) ◇ (y ◇ (x ◇ z))
-- Conclusion: x ◇ x = y ◇ ((y ◇ z) ◇ z)
-- Original submission SHA-256: 6ef484ec12c2bf555285553710d19f820e896cc912da1fff361c0353f2da3ee3
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (y ◇ z) ◇ (y ◇ (x ◇ z))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ x = y ◇ ((y ◇ z) ◇ z)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have p0 : forall (q0 q1 q2 q3:G), (q0 ◇ ((q1 ◇ q2) ◇ (q3 ◇ (q1 ◇ (q0 ◇ q2))))) = q3:=by
    intro q0 q1 q2 q3
    exact ((congrArg (fun t => t ◇ ((q1 ◇ q2) ◇ (q3 ◇ (q1 ◇ (q0 ◇ q2))))) ((h q0 q1 q2).symm)).symm).trans ((h q3 (q1 ◇ q2) (q1 ◇ (q0 ◇ q2))).symm)
  have p1 : forall (q4 q5 q6:G), (q4 ◇ ((q5 ◇ q6) ◇ q4)) = (q5 ◇ q6):=by
    intro q4 q5 q6
    exact ((congrArg (fun t => q4 ◇ t) (congrArg (fun t => (q5 ◇ q6) ◇ t) ((h q4 q5 q6).symm))).symm).trans (p0 q4 q5 q6 (q5 ◇ q6))
  have p2 : forall (q7 q8 q9:G), ((q9 ◇ q9) ◇ (q7 ◇ q8)) = (q7 ◇ q8):=by
    intro q7 q8 q9
    exact ((congrArg (fun t => (q9 ◇ q9) ◇ t) (p1 q9 q7 q8)).symm).trans ((h (q7 ◇ q8) q9 q9).symm)
  have p3 : forall (q10 q11:G), (q11 ◇ (q10 ◇ q11)) = q10:=by
    intro q10 q11
    exact ((p2 q11 (q10 ◇ q11) q11).symm).trans ((h q10 q11 q11).symm)
  have p4 : forall (q12 q13:G), (q12 ◇ (q13 ◇ q13)) = q12:=by
    intro q12 q13
    exact (((p3 q12 (q13 ◇ q13)).symm).trans (p2 q12 (q13 ◇ q13) q13)).symm
  have p5 : forall (q14 q15:G), ((q14 ◇ q15) ◇ q15) = q14:=by
    intro q14 q15
    exact ((p4 ((q14 ◇ q15) ◇ q15) (q14 ◇ q15)).symm).trans ((h q14 (q14 ◇ q15) q15).symm)
  exact ((p4 (x ◇ x) y).symm).trans (((congrArg (fun t => y ◇ t) (p5 y z)).trans ((p2 y y x).symm)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_1571_to_3489 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_1571_to_3489
