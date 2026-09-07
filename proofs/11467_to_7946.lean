-- Equation11467 → Equation7946
-- Recorded verdict: true
-- Premise: x = y * ((z * (y * w)) * (x * x))
-- Conclusion: x = y * (z * ((y * (z * y)) * x))
-- Original submission SHA-256: 7df078116012c2abd9f03840cc098c7589dba9044d3d48dce3d737cb7d208ef6
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = y ◇ ((z ◇ (y ◇ w)) ◇ (x ◇ x))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = y ◇ (z ◇ ((y ◇ (z ◇ y)) ◇ x))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc0 : forall (q0 q1 q2 q3:G), (q2 ◇ ((q3 ◇ q0) ◇ (q1 ◇ q1))) = q1:=by
    intro q0 q1 q2 q3
    exact ((congrArg (fun t => q2 ◇ t) (congrArg (fun t => t ◇ (q1 ◇ q1)) (congrArg (fun t => q3 ◇ t) ((h q0 q2 q0 q0).symm)))).symm).trans ((h q1 q2 q3 ((q0 ◇ (q2 ◇ q0)) ◇ (q0 ◇ q0))).symm)
  have apc1 : forall (q4 q5 q6:G), (q6 ◇ (q4 ◇ (q5 ◇ q5))) = q5:=by
    intro q4 q5 q6
    exact ((congrArg (fun t => q6 ◇ t) (congrArg (fun t => t ◇ (q5 ◇ q5)) ((h q4 q4 q4 q4).symm))).symm).trans (apc0 ((q4 ◇ (q4 ◇ q4)) ◇ (q4 ◇ q4)) q5 q6 q4)
  have apc2 : forall (q7 q8:G), (q8 ◇ q7) = (q7 ◇ q7):=by
    intro q7 q8
    exact ((congrArg (fun t => q8 ◇ t) (apc0 q7 q7 (q7 ◇ (q8 ◇ q7)) q7)).symm).trans ((h (q7 ◇ q7) q8 q7 q7).symm)
  exact (calc
    x = x:=rfl
    _ = (y ◇ (z ◇ ((y ◇ (z ◇ y)) ◇ x))):=(((congrArg (fun t => y ◇ t) (congrArg (fun t => z ◇ t) (congrArg (fun t => t ◇ x) (congrArg (fun t => y ◇ t) (apc2 y z))))).trans (congrArg (fun t => y ◇ t) (congrArg (fun t => z ◇ t) (apc2 x (y ◇ (y ◇ y)))))).trans (apc1 z x y)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_11467_to_7946 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_11467_to_7946
