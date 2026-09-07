-- Equation18006 → Equation25060
-- Recorded verdict: true
-- Premise: x = (x * y) * (z * ((y * w) * y))
-- Conclusion: x = (x * (y * (z * w))) * (w * z)
-- Original submission SHA-256: 7c130e6fcde6d0ac678d8842aed1b6a0ca5a8cf1dc16499a666d8130eee12db8
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = (x ◇ y) ◇ (z ◇ ((y ◇ w) ◇ y))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = (x ◇ (y ◇ (z ◇ w))) ◇ (w ◇ z)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc0 : forall (q0 q1 q2 q3:G), ((q2 ◇ (q0 ◇ q1)) ◇ (q3 ◇ (q0 ◇ (q0 ◇ q1)))) = q2:=by
    intro q0 q1 q2 q3
    exact ((congrArg (fun t => (q2 ◇ (q0 ◇ q1)) ◇ t) (congrArg (fun t => q3 ◇ t) (congrArg (fun t => t ◇ (q0 ◇ q1)) ((h q0 q1 q0 q0).symm)))).symm).trans ((h q2 (q0 ◇ q1) q3 (q0 ◇ ((q1 ◇ q0) ◇ q1))).symm)
  have apc1 : forall (q4 q5 q6 q7:G), ((q7 ◇ (q6 ◇ (q6 ◇ q4))) ◇ q5) = q7:=by
    intro q4 q5 q6 q7
    exact ((congrArg (fun t => (q7 ◇ (q6 ◇ (q6 ◇ q4))) ◇ t) (apc0 q6 q4 q5 q6)).symm).trans (apc0 q6 (q6 ◇ q4) q7 (q5 ◇ (q6 ◇ q4)))
  have apc3 : forall (q8 q9 q10 q11:G), ((q11 ◇ (q9 ◇ q10)) ◇ q8) = q11:=by
    intro q8 q9 q10 q11
    exact ((congrArg (fun t => (q11 ◇ (q9 ◇ q10)) ◇ t) (apc1 q8 (q9 ◇ (q9 ◇ q10)) q8 q8)).symm).trans (apc0 q9 q10 q11 (q8 ◇ (q8 ◇ (q8 ◇ q8))))
  exact (calc
    x = x:=rfl
    _ = ((x ◇ (y ◇ (z ◇ w))) ◇ (w ◇ z)):=(apc3 (w ◇ z) y (z ◇ w) x).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_18006_to_25060 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_18006_to_25060
