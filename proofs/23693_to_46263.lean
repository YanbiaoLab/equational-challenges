-- Equation23693 → Equation46263
-- Recorded verdict: true
-- Premise: x = ((y ◇ z) ◇ x) ◇ (w ◇ (u ◇ v))
-- Conclusion: x ◇ y = (x ◇ z) ◇ (w ◇ (u ◇ y))
-- Original submission SHA-256: c1b6afc11ee78903d65aee61cd7f4b6700f61b03f019f1171019aafd62b05a23
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G) (v : G), x = ((y ◇ z) ◇ x) ◇ (w ◇ (u ◇ v))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x ◇ y = (x ◇ z) ◇ (w ◇ (u ◇ y))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w u
  have apc0 : forall (q0 q1 q2 q3 q4:G), ((q0 ◇ q4) ◇ (q3 ◇ (q1 ◇ q2))) = q4:=by
    intro q0 q1 q2 q3 q4
    exact ((congrArg (fun t => t ◇ (q3 ◇ (q1 ◇ q2))) (congrArg (fun t => t ◇ q4) ((h q0 q0 q0 q0 q0 q0).symm))).symm).trans ((h q4 ((q0 ◇ q0) ◇ q0) (q0 ◇ (q0 ◇ q0)) q3 q1 q2).symm)
  have apc1 : forall (q5 q6 q7 q8:G), ((q6 ◇ q8) ◇ (q7 ◇ q5)) = q8:=by
    intro q5 q6 q7 q8
    exact ((congrArg (fun t => (q6 ◇ q8) ◇ t) (congrArg (fun t => q7 ◇ t) (apc0 q5 q5 q5 q5 q5))).symm).trans (apc0 q6 (q5 ◇ q5) (q5 ◇ (q5 ◇ q5)) q7 q8)
  have apc2 : forall (q9 q10 q11 q12 q13 q14:G), (q14 ◇ (q13 ◇ (q11 ◇ q12))) = (q10 ◇ q9):=by
    intro q9 q10 q11 q12 q13 q14
    exact ((congrArg (fun t => t ◇ (q13 ◇ (q11 ◇ q12))) (apc1 q9 q9 q10 q14)).symm).trans ((h (q10 ◇ q9) q9 q14 q13 q11 q12).symm)
  have apc6 : forall (q15 q16 q17:G), (q16 ◇ q15) = q17:=by
    intro q15 q16 q17
    exact ((apc2 q15 q16 q15 q15 q15 (q15 ◇ q17)).symm).trans (apc1 (q15 ◇ q15) q15 q15 q17)
  exact (apc6 y x (x ◇ y)).trans ((apc6 (w ◇ (u ◇ y)) (x ◇ z) (x ◇ y)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_23693_to_46263 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_23693_to_46263
