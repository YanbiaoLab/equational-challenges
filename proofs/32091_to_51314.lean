-- Equation32091 → Equation51314
-- Recorded verdict: true
-- Premise: x = (y ◇ ((x ◇ (x ◇ x)) ◇ z)) ◇ x
-- Conclusion: x ◇ x = ((y ◇ z) ◇ (x ◇ w)) ◇ x
-- Original submission SHA-256: 7c053262a8a8faeb892ab532ff0d8c9c9471d23d8de847a26c42fd6eb6ad49ad
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (y ◇ ((x ◇ (x ◇ x)) ◇ z)) ◇ x
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ x = ((y ◇ z) ◇ (x ◇ w)) ◇ x
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have apc0 : forall (q0 q1:G), (((q0 ◇ (q0 ◇ q0)) ◇ q1) ◇ q0) = q0:=by
    intro q0 q1
    exact ((congrArg (fun t => t ◇ q0) ((h ((q0 ◇ (q0 ◇ q0)) ◇ q1) q0 q0).symm)).symm).trans ((h q0 (q0 ◇ ((((q0 ◇ (q0 ◇ q0)) ◇ q1) ◇ (((q0 ◇ (q0 ◇ q0)) ◇ q1) ◇ ((q0 ◇ (q0 ◇ q0)) ◇ q1))) ◇ q0)) q1).symm)
  have apc1 : forall (q2 q1:G), ((q2 ◇ q1) ◇ (q1 ◇ (q1 ◇ q1))) = (q1 ◇ (q1 ◇ q1)):=by
    intro q2 q1
    exact ((congrArg (fun t => t ◇ (q1 ◇ (q1 ◇ q1))) (congrArg (fun t => q2 ◇ t) ((h q1 (q1 ◇ (q1 ◇ q1)) (q1 ◇ (q1 ◇ q1))).symm))).symm).trans ((h (q1 ◇ (q1 ◇ q1)) q2 q1).symm)
  have apc2 : forall (q3:G), (((q3 ◇ q3) ◇ ((q3 ◇ q3) ◇ (q3 ◇ q3))) ◇ q3) = q3:=by
    intro q3
    exact ((congrArg (fun t => t ◇ q3) (apc1 q3 (q3 ◇ q3))).symm).trans (apc0 q3 ((q3 ◇ q3) ◇ ((q3 ◇ q3) ◇ (q3 ◇ q3))))
  have apc3 : forall (q4:G), (q4 ◇ (q4 ◇ q4)) = (q4 ◇ q4):=by
    intro q4
    exact ((congrArg (fun t => t ◇ (q4 ◇ q4)) (apc2 q4)).symm).trans (apc0 (q4 ◇ q4) q4)
  have apc6 : forall (q0 q1 q4:G), (((q0 ◇ q0) ◇ q1) ◇ q0) = q0:=by
    intro q0 q1 q4
    exact ((congrArg (fun t => t ◇ q0) (congrArg (fun t => t ◇ q1) (apc3 q0))).symm).trans (apc0 q0 q1)
  have apc7 : forall (q5 q6:G), ((q5 ◇ q6) ◇ (q6 ◇ q6)) = (q6 ◇ q6):=by
    intro q5 q6
    exact ((congrArg (fun t => t ◇ (q6 ◇ q6)) (congrArg (fun t => q5 ◇ t) (apc2 q6))).symm).trans ((h (q6 ◇ q6) q5 q6).symm)
  have apc11 : forall (q7:G), ((q7 ◇ q7) ◇ q7) = q7:=by
    intro q7
    exact ((congrArg (fun t => t ◇ q7) (apc7 q7 q7)).symm).trans (apc6 q7 (q7 ◇ q7) q7)
  have apc12 : forall (q8:G), (q8 ◇ q8) = q8:=by
    intro q8
    exact ((congrArg (fun t => t ◇ q8) (apc11 q8)).symm).trans (apc6 q8 q8 q8)
  have apc13 : forall (q9 q10 q11:G), ((q10 ◇ (q9 ◇ q11)) ◇ q9) = q9:=by
    intro q9 q10 q11
    exact ((congrArg (fun t => t ◇ q9) (congrArg (fun t => q10 ◇ t) (congrArg (fun t => t ◇ q11) (apc12 q9)))).symm).trans (((congrArg (fun t => t ◇ q9) (congrArg (fun t => q10 ◇ t) (congrArg (fun t => t ◇ q11) (congrArg (fun t => q9 ◇ t) (apc12 q9))))).symm).trans ((h q9 q10 q11).symm))
  exact (calc
    (x ◇ x) = x:=apc12 x
    _ = (((y ◇ z) ◇ (x ◇ w)) ◇ x):=(apc13 x (y ◇ z) w).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_32091_to_51314 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_32091_to_51314
