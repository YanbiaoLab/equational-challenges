-- Equation543 → Equation3297
-- Recorded verdict: true
-- Premise: x = y ◇ (z ◇ (x ◇ (y ◇ z)))
-- Conclusion: x ◇ x = y ◇ (z ◇ (z ◇ y))
-- Original submission SHA-256: e15b2b1d67f579e34badf087fe939cc54419264e2d2d59a1183c88facd46d9da
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = y ◇ (z ◇ (x ◇ (y ◇ z)))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ x = y ◇ (z ◇ (z ◇ y))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have p0 : forall (x y z:G), (y ◇ (z ◇ (x ◇ (y ◇ z)))) = (x ◇ (x ◇ (x ◇ (x ◇ x)))):=by
    intro x y z
    exact ((h x y z).symm).trans (h x x x)
  have p1 : forall (q0:G), (q0 ◇ (q0 ◇ (q0 ◇ (q0 ◇ q0)))) = q0:=by
    intro q0
    exact ((p0 q0 q0 q0).symm).trans ((h q0 q0 q0).symm)
  have p2 : forall (q1 q2:G), (q2 ◇ ((q2 ◇ (q2 ◇ (q2 ◇ q2))) ◇ (q1 ◇ q2))) = q1:=by
    intro q1 q2
    exact ((congrArg (fun t => q2 ◇ t) (congrArg (fun t => (q2 ◇ (q2 ◇ (q2 ◇ q2))) ◇ t) (congrArg (fun t => q1 ◇ t) (p1 q2)))).symm).trans ((h q1 q2 (q2 ◇ (q2 ◇ (q2 ◇ q2)))).symm)
  have p3 : forall (q3 q4:G), (q4 ◇ (q4 ◇ (q4 ◇ q4))) = (q3 ◇ q3):=by
    intro q3 q4
    exact (((congrArg (fun t => q3 ◇ t) (p2 q3 q4)).symm).trans ((h (q4 ◇ (q4 ◇ (q4 ◇ q4))) q3 q4).symm)).symm
  have p4 : forall (q3 q4:G), (q4 ◇ q4) = (q3 ◇ q3):=by
    intro q3 q4
    exact (((p3 q3 q4).symm).trans (p3 q4 q4)).symm
  have p5 : forall (q5 q6 q7:G), (q6 ◇ (q7 ◇ (q5 ◇ q5))) = (q6 ◇ q7):=by
    intro q5 q6 q7
    exact ((congrArg (fun t => q6 ◇ t) (congrArg (fun t => q7 ◇ t) (p4 q5 (q6 ◇ q7)))).symm).trans ((h (q6 ◇ q7) q6 q7).symm)
  have p6 : forall (q8 q9:G), (q9 ◇ (q9 ◇ q8)) = q8:=by
    intro q8 q9
    exact ((congrArg (fun t => q9 ◇ t) (p5 q9 q9 q8)).symm).trans ((h q8 q9 q9).symm)
  exact (p4 y x).trans ((congrArg (fun t => y ◇ t) (p6 y z)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_543_to_3297 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_543_to_3297
