-- Equation42493 → Equation54198
-- Recorded verdict: true
-- Premise: x ◇ x = y ◇ (x ◇ ((z ◇ w) ◇ w))
-- Conclusion: x ◇ (y ◇ y) = y ◇ (x ◇ (x ◇ x))
-- Original submission SHA-256: 8e89b3c189baa07767836da85caec8bf0774cf3d0b1326c3b84f5cd2a35ae339
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ x = y ◇ (x ◇ ((z ◇ w) ◇ w))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x ◇ (y ◇ y) = y ◇ (x ◇ (x ◇ x))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y
  have p0 : forall (q0 q1 q2:G), (q2 ◇ (q1 ◇ (q0 ◇ q0))) = (q1 ◇ q1):=by
    intro q0 q1 q2
    exact ((congrArg (fun t => q2 ◇ t) (congrArg (fun t => q1 ◇ t) ((h q0 (q0 ◇ (q0 ◇ ((q0 ◇ q0) ◇ q0))) q0 q0).symm))).symm).trans ((h q1 q2 q0 (q0 ◇ ((q0 ◇ q0) ◇ q0))).symm)
  have p1 : forall (q3 q4 q5:G), ((q3 ◇ q3) ◇ (q3 ◇ q3)) = (q4 ◇ q4):=by
    intro q3 q4 q5
    exact ((p0 q3 (q3 ◇ q3) q5).symm).trans (((congrArg (fun t => q5 ◇ t) (p0 q3 (q3 ◇ q3) q4)).symm).trans (p0 (q3 ◇ q3) q4 q5))
  have p2 : forall (q3 q4 q5:G), (q4 ◇ q4) = (q3 ◇ q3):=by
    intro q3 q4 q5
    exact ((p1 q3 q4 q5).symm).trans (p1 q3 q3 q5)
  have p3 : forall (q6 q7 q8:G), ((q7 ◇ q7) ◇ (q7 ◇ q7)) = (q8 ◇ (q6 ◇ q6)):=by
    intro q6 q7 q8
    exact (((congrArg (fun t => q8 ◇ t) (p1 q7 q6 q6)).symm).trans (p0 q7 (q7 ◇ q7) q8)).symm
  have p4 : forall (q9 q10 q11:G), (q10 ◇ (q9 ◇ q9)) = (q11 ◇ q11):=by
    intro q9 q10 q11
    exact ((p3 q9 q9 q10).symm).trans (p2 q11 (q9 ◇ q9) q9)
  have p5 : forall (q12 q13 q14 q15:G), (q15 ◇ (q14 ◇ q14)) = (q13 ◇ (q12 ◇ q12)):=by
    intro q12 q13 q14 q15
    exact (((p3 q12 q12 q13).symm).trans (p3 q14 q12 q15)).symm
  exact (p5 y y y x).trans ((congrArg (fun t => y ◇ t) (p4 x x y)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_42493_to_54198 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_42493_to_54198
