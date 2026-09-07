-- Equation14648 → Equation28571
-- Recorded verdict: true
-- Premise: x = y * (((x * z) * (y * w)) * x)
-- Conclusion: x = (((x * y) * z) * w) * (u * x)
-- Original submission SHA-256: a1946e7ccb578a167f06c17139d715cc31653fb92bbda0bb97518d6966f43f2d
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = y ◇ (((x ◇ z) ◇ (y ◇ w)) ◇ x)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x = (((x ◇ y) ◇ z) ◇ w) ◇ (u ◇ x)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w u
  have apc0 : forall (q0 q1 q2 q3 q4:G), (((q2 ◇ q1) ◇ ((q3 ◇ q4) ◇ q0)) ◇ (q2 ◇ q3)) = q3:=by
    intro q0 q1 q2 q3 q4
    exact ((congrArg (fun t => ((q2 ◇ q1) ◇ ((q3 ◇ q4) ◇ q0)) ◇ t) (congrArg (fun t => t ◇ q3) ((h q2 (q3 ◇ q4) q1 q0).symm))).symm).trans ((h q3 ((q2 ◇ q1) ◇ ((q3 ◇ q4) ◇ q0)) q4 q2).symm)
  have apc1 : forall (q5 q6 q7 q8:G), (((q7 ◇ q6) ◇ q5) ◇ (q7 ◇ q8)) = q8:=by
    intro q5 q6 q7 q8
    exact ((congrArg (fun t => t ◇ (q7 ◇ q8)) (congrArg (fun t => (q7 ◇ q6) ◇ t) ((h q5 (q8 ◇ q5) q5 q5).symm))).symm).trans (apc0 (((q5 ◇ q5) ◇ ((q8 ◇ q5) ◇ q5)) ◇ q5) q6 q7 q8 q5)
  have apc3 : forall (q9 q10 q11:G), (q9 ◇ (q10 ◇ q11)) = q11:=by
    intro q9 q10 q11
    exact ((congrArg (fun t => t ◇ (q10 ◇ q11)) ((h q9 (q10 ◇ q9) q9 q9).symm)).symm).trans (apc1 (((q9 ◇ q9) ◇ ((q10 ◇ q9) ◇ q9)) ◇ q9) q9 q10 q11)
  exact (calc
    x = x:=rfl
    _ = ((((x ◇ y) ◇ z) ◇ w) ◇ (u ◇ x)):=(apc3 (((x ◇ y) ◇ z) ◇ w) u x).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_14648_to_28571 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_14648_to_28571
