-- Equation35197 → Equation49820
-- Recorded verdict: true
-- Premise: x = ((y * z) * ((z * y) * z)) * x
-- Conclusion: x * y = (y * (y * (x * z))) * y
-- Original submission SHA-256: fe23021608f37cb86c47f4ec326488a75623ca1c3e817496c05b9815b3fb457b
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = ((y ◇ z) ◇ ((z ◇ y) ◇ z)) ◇ x
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = (y ◇ (y ◇ (x ◇ z))) ◇ y
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have apc2 : forall (x y z:G), (((y ◇ z) ◇ ((z ◇ y) ◇ z)) ◇ x) = (((x ◇ x) ◇ ((x ◇ x) ◇ x)) ◇ x):=by
    intro x y z
    exact ((h x y z).symm).trans (h x x x)
  have apc3 : forall (q0:G), (((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ q0)) ◇ q0) = q0:=by
    intro q0
    exact ((apc2 q0 q0 q0).symm).trans ((h q0 q0 q0).symm)
  have apc7 : forall (q1 q2:G), (((q2 ◇ ((q2 ◇ q2) ◇ ((q2 ◇ q2) ◇ q2))) ◇ (q2 ◇ ((q2 ◇ q2) ◇ ((q2 ◇ q2) ◇ q2)))) ◇ q1) = q1:=by
    intro q1 q2
    exact ((congrArg (fun t => t ◇ q1) (congrArg (fun t => (q2 ◇ ((q2 ◇ q2) ◇ ((q2 ◇ q2) ◇ q2))) ◇ t) (congrArg (fun t => t ◇ ((q2 ◇ q2) ◇ ((q2 ◇ q2) ◇ q2))) (apc3 q2)))).symm).trans ((h q1 q2 ((q2 ◇ q2) ◇ ((q2 ◇ q2) ◇ q2))).symm)
  have apc8 : forall (q3 q4:G), ((q3 ◇ ((q3 ◇ q3) ◇ ((q3 ◇ q3) ◇ q3))) ◇ q4) = q4:=by
    intro q3 q4
    exact ((congrArg (fun t => t ◇ q4) (apc7 (q3 ◇ ((q3 ◇ q3) ◇ ((q3 ◇ q3) ◇ q3))) q3)).symm).trans (((congrArg (fun t => t ◇ q4) (apc7 (((q3 ◇ ((q3 ◇ q3) ◇ ((q3 ◇ q3) ◇ q3))) ◇ (q3 ◇ ((q3 ◇ q3) ◇ ((q3 ◇ q3) ◇ q3)))) ◇ (q3 ◇ ((q3 ◇ q3) ◇ ((q3 ◇ q3) ◇ q3)))) q3)).symm).trans ((h q4 (q3 ◇ ((q3 ◇ q3) ◇ ((q3 ◇ q3) ◇ q3))) (q3 ◇ ((q3 ◇ q3) ◇ ((q3 ◇ q3) ◇ q3)))).symm))
  have apc9 : forall (q5 q6:G), ((q6 ◇ q6) ◇ q5) = q5:=by
    intro q5 q6
    exact ((congrArg (fun t => t ◇ q5) (congrArg (fun t => t ◇ q6) (apc3 q6))).symm).trans (((congrArg (fun t => t ◇ q5) (congrArg (fun t => (((q6 ◇ q6) ◇ ((q6 ◇ q6) ◇ q6)) ◇ q6) ◇ t) (apc8 q6 q6))).symm).trans ((h q5 ((q6 ◇ q6) ◇ ((q6 ◇ q6) ◇ q6)) q6).symm))
  have apc10 : forall (q7 q8:G), (q8 ◇ q7) = q7:=by
    intro q7 q8
    exact ((congrArg (fun t => t ◇ q7) (apc9 q8 q8)).symm).trans (((congrArg (fun t => t ◇ q7) (apc9 ((q8 ◇ q8) ◇ q8) q8)).symm).trans ((h q7 q8 q8).symm))
  exact (apc10 y x).trans ((apc10 y (y ◇ (y ◇ (x ◇ z)))).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_35197_to_49820 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_35197_to_49820
