-- Equation8424 → Equation29646
-- Recorded verdict: true
-- Premise: x = y ◇ (x ◇ (((x ◇ y) ◇ z) ◇ z))
-- Conclusion: x = (y ◇ (y ◇ (y ◇ (x ◇ y)))) ◇ y
-- Original submission SHA-256: 81d1ffa8586afed9e7ffffe1051395584a54af3fe61645255764af63a5572ca0
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = y ◇ (x ◇ (((x ◇ y) ◇ z) ◇ z))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x = (y ◇ (y ◇ (y ◇ (x ◇ y)))) ◇ y
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y
  have apc1 : forall (q0 q1 q2 q3:G), (q3 ◇ (q2 ◇ (q0 ◇ (q0 ◇ (((q0 ◇ (q2 ◇ q3)) ◇ q1) ◇ q1))))) = q2:=by
    intro q0 q1 q2 q3
    exact ((congrArg (fun t => q3 ◇ t) (congrArg (fun t => q2 ◇ t) (congrArg (fun t => t ◇ (q0 ◇ (((q0 ◇ (q2 ◇ q3)) ◇ q1) ◇ q1))) ((h q0 (q2 ◇ q3) q1).symm)))).symm).trans ((h q2 q3 (q0 ◇ (((q0 ◇ (q2 ◇ q3)) ◇ q1) ◇ q1))).symm)
  have apc2 : forall (q4 q5:G), (q5 ◇ (q4 ◇ (q4 ◇ q5))) = q4:=by
    intro q4 q5
    exact ((congrArg (fun t => q5 ◇ t) (congrArg (fun t => q4 ◇ t) ((h (q4 ◇ q5) (q4 ◇ q5) q4).symm))).symm).trans (apc1 (q4 ◇ q5) q4 q4 q5)
  have apc5 : forall (q6 q7:G), ((q6 ◇ (q6 ◇ q7)) ◇ (q7 ◇ q6)) = q7:=by
    intro q6 q7
    exact ((congrArg (fun t => (q6 ◇ (q6 ◇ q7)) ◇ t) (congrArg (fun t => q7 ◇ t) (apc2 q6 q7))).symm).trans (apc2 q7 (q6 ◇ (q6 ◇ q7)))
  have apc6 : forall (q8 q9:G), ((q9 ◇ q8) ◇ q8) = q9:=by
    intro q8 q9
    exact ((congrArg (fun t => (q9 ◇ q8) ◇ t) (apc2 q8 q9)).symm).trans (((congrArg (fun t => (q9 ◇ q8) ◇ t) (congrArg (fun t => q9 ◇ t) (congrArg (fun t => t ◇ (q8 ◇ q9)) (apc5 q9 q8)))).symm).trans ((h q9 (q9 ◇ q8) (q8 ◇ q9)).symm))
  have apc9 : forall (q10 q11:G), (q10 ◇ (q10 ◇ (q10 ◇ q11))) = q11:=by
    intro q10 q11
    exact ((congrArg (fun t => t ◇ (q10 ◇ (q10 ◇ q11))) (apc2 q10 q11)).symm).trans (apc6 (q10 ◇ (q10 ◇ q11)) q11)
  exact (calc
    x = x:=rfl
    _ = ((y ◇ (y ◇ (y ◇ (x ◇ y)))) ◇ y):=((congrArg (fun t => t ◇ y) (apc9 y (x ◇ y))).trans (apc6 y x)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_8424_to_29646 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_8424_to_29646
