-- Equation27937 → Equation13118
-- Recorded verdict: true
-- Premise: x = ((y * (y * z)) * x) * (w * x)
-- Conclusion: x = y * ((z * (x * (y * z))) * x)
-- Original submission SHA-256: 8495c80654d2faaa11e09f0c42dea8fbdaa9ca7f7997e9159af4d6853680b492
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = ((y ◇ (y ◇ z)) ◇ x) ◇ (w ◇ x)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = y ◇ ((z ◇ (x ◇ (y ◇ z))) ◇ x)
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (q0 q1 q2:G), ((q2 ◇ q1) ◇ (q0 ◇ q1)) = q1:=by
    intro q0 q1 q2
    exact ((congrArg (fun t => t ◇ (q0 ◇ q1)) (congrArg (fun t => t ◇ q1) ((h q2 q0 q0 ((q0 ◇ (q0 ◇ q0)) ◇ q2)).symm))).symm).trans ((h q1 ((q0 ◇ (q0 ◇ q0)) ◇ q2) q2 q0).symm)
  have apc1 : forall (q3 q4 q5:G), (q4 ◇ (q5 ◇ (q3 ◇ q4))) = (q3 ◇ q4):=by
    intro q3 q4 q5
    exact ((congrArg (fun t => t ◇ (q5 ◇ (q3 ◇ q4))) (apc0 q3 q4 q3)).symm).trans (apc0 q5 (q3 ◇ q4) (q3 ◇ q4))
  have apc2 : forall (q6 q7 q8:G), (q7 ◇ (q6 ◇ q8)) = q8:=by
    intro q6 q7 q8
    exact (((apc0 q6 q8 q6).symm).trans (((congrArg (fun t => (q6 ◇ q8) ◇ t) (apc1 q6 q8 q7)).symm).trans (apc1 q7 (q6 ◇ q8) q8))).symm
  exact (calc
    x = x:=rfl
    _ = (y ◇ ((z ◇ (x ◇ (y ◇ z))) ◇ x)):=((congrArg (fun t => y ◇ t) (congrArg (fun t => t ◇ x) (congrArg (fun t => z ◇ t) (apc2 y x z)))).trans (apc2 (z ◇ z) y x)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_27937_to_13118 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_27937_to_13118
