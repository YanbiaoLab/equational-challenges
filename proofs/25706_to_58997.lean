-- Equation25706 → Equation58997
-- Recorded verdict: true
-- Premise: x = (y * (z * (w * u))) * (x * x)
-- Conclusion: (x * y) * z = w * (z * (w * z))
-- Original submission SHA-256: c7ccdb3db7663b380a3b31a6c77fbddd8e27f26d455ddadc69c004a851d1b4ac
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G) (u : G), x = (y ◇ (z ◇ (w ◇ u))) ◇ (x ◇ x)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), (x ◇ y) ◇ z = w ◇ (z ◇ (w ◇ z))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc0 : forall (q0 q1 q2:G), ((q1 ◇ q0) ◇ (q2 ◇ q2)) = q2:=by
    intro q0 q1 q2
    exact ((congrArg (fun t => t ◇ (q2 ◇ q2)) ((h (q1 ◇ q0) q0 q0 q0 q0).symm)).symm).trans ((h q2 (q0 ◇ (q0 ◇ (q0 ◇ q0))) (q1 ◇ q0) q1 q0).symm)
  have apc1 : forall (q3 q4 q5:G), ((q5 ◇ q4) ◇ q3) = (q3 ◇ q3):=by
    intro q3 q4 q5
    exact ((congrArg (fun t => (q5 ◇ q4) ◇ t) (apc0 q3 q3 q3)).symm).trans (apc0 q4 q5 (q3 ◇ q3))
  have apc2 : forall (q6 q7:G), (q6 ◇ (q7 ◇ q7)) = q7:=by
    intro q6 q7
    exact ((congrArg (fun t => t ◇ (q7 ◇ q7)) (apc0 q6 q6 q6)).symm).trans (apc0 (q6 ◇ q6) (q6 ◇ q6) q7)
  have apc3 : forall (q8 q9:G), (q9 ◇ q9) = (q8 ◇ q9):=by
    intro q8 q9
    exact (((congrArg (fun t => t ◇ q9) (apc0 q8 q8 q8)).symm).trans (apc1 q9 (q8 ◇ q8) (q8 ◇ q8))).symm
  have apc6 : forall (q10 q11 q12:G), (q11 ◇ (q10 ◇ q12)) = q12:=by
    intro q10 q11 q12
    exact ((congrArg (fun t => q11 ◇ t) (apc3 q10 q12)).symm).trans (apc2 q11 q12)
  have apc7 : forall (q13 q14 q15:G), (q14 ◇ q15) = (q13 ◇ q15):=by
    intro q13 q14 q15
    exact (((apc3 q13 q15).symm).trans (apc3 q14 q15)).symm
  exact (calc
    ((x ◇ y) ◇ z) = (w ◇ z):=apc7 w (x ◇ y) z
    _ = (w ◇ (z ◇ (w ◇ z))):=(apc6 z w (w ◇ z)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_25706_to_58997 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_25706_to_58997
