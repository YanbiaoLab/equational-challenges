-- Equation10370 → Equation24054
-- Recorded verdict: true
-- Premise: x = y * ((y * y) * ((z * x) * z))
-- Conclusion: x = ((x * y) * x) * ((y * y) * x)
-- Original submission SHA-256: 269f0e0176af72c179f729777ab04fc411140ccc6982935bdc55fcd4accb4350
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = y ◇ ((y ◇ y) ◇ ((z ◇ x) ◇ z))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x = ((x ◇ y) ◇ x) ◇ ((y ◇ y) ◇ x)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y
  have apc0 : forall (q0 q1 q2 q3:G), (q2 ◇ ((q2 ◇ q2) ◇ (q0 ◇ q3))) = ((q3 ◇ q3) ◇ ((q1 ◇ q0) ◇ q1)):=by
    intro q0 q1 q2 q3
    exact ((congrArg (fun t => q2 ◇ t) (congrArg (fun t => (q2 ◇ q2) ◇ t) (congrArg (fun t => t ◇ q3) ((h q0 q3 q1).symm)))).symm).trans ((h ((q3 ◇ q3) ◇ ((q1 ◇ q0) ◇ q1)) q2 q3).symm)
  have apc1 : forall (q4 q5 q6:G), ((q6 ◇ q6) ◇ ((q4 ◇ (q6 ◇ q5)) ◇ q4)) = q5:=by
    intro q4 q5 q6
    exact ((apc0 (q6 ◇ q5) q4 q4 q6).symm).trans ((h q5 q4 q6).symm)
  have apc2 : forall (q7 q8:G), ((q8 ◇ q8) ◇ ((q7 ◇ q8) ◇ q7)) = q8:=by
    intro q7 q8
    exact (((apc1 (q8 ◇ q8) q8 q8).symm).trans (apc0 q8 q7 (q8 ◇ q8) q8)).symm
  have apc3 : forall (q9:G), (q9 ◇ q9) = q9:=by
    intro q9
    exact ((congrArg (fun t => q9 ◇ t) (apc2 q9 q9)).symm).trans ((h q9 q9 q9).symm)
  have apc4 : forall (q7 q8 q9:G), (q8 ◇ ((q7 ◇ q8) ◇ q7)) = q8:=by
    intro q7 q8 q9
    exact ((congrArg (fun t => t ◇ ((q7 ◇ q8) ◇ q7)) (apc3 q8)).symm).trans (apc2 q7 q8)
  have apc6 : forall (q10 q11:G), (q11 ◇ (q11 ◇ q10)) = q10:=by
    intro q10 q11
    exact (((congrArg (fun t => q11 ◇ t) (congrArg (fun t => (q11 ◇ q11) ◇ t) (apc3 q10))).trans (congrArg (fun t => q11 ◇ t) (congrArg (fun t => t ◇ q10) (apc3 q11)))).symm).trans (((congrArg (fun t => q11 ◇ t) (congrArg (fun t => (q11 ◇ q11) ◇ t) (congrArg (fun t => t ◇ q10) (apc3 q10)))).symm).trans ((h q10 q11 q10).symm))
  have apc7 : forall (q12 q13:G), ((q13 ◇ q12) ◇ q13) = q12:=by
    intro q12 q13
    exact ((apc4 ((q13 ◇ q12) ◇ q13) ((q13 ◇ q12) ◇ q13) q12).symm).trans ((h q12 ((q13 ◇ q12) ◇ q13) q13).symm)
  exact (calc
    x = x:=rfl
    _ = (((x ◇ y) ◇ x) ◇ ((y ◇ y) ◇ x)):=(((congrArg (fun t => ((x ◇ y) ◇ x) ◇ t) (congrArg (fun t => t ◇ x) (apc3 y))).trans (congrArg (fun t => t ◇ (y ◇ x)) (apc7 y x))).trans (apc6 x y)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_10370_to_24054 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_10370_to_24054
