-- Equation4918 → Equation4930
-- Recorded verdict: true
-- Premise: x = y ◇ (x ◇ (x ◇ (z ◇ (x ◇ x))))
-- Conclusion: x = y ◇ (x ◇ (x ◇ (z ◇ (w ◇ x))))
-- Original submission SHA-256: f341b47b0cacb73838c43b328679c5bdba2b5c051d37c67eaccd02720338ed80
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = y ◇ (x ◇ (x ◇ (z ◇ (x ◇ x))))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = y ◇ (x ◇ (x ◇ (z ◇ (w ◇ x))))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have p0 : forall (q0 q1 q2 q3:G), (q2 ◇ ((q0 ◇ (q0 ◇ (q1 ◇ (q0 ◇ q0)))) ◇ ((q0 ◇ (q0 ◇ (q1 ◇ (q0 ◇ q0)))) ◇ (q3 ◇ q0)))) = (q0 ◇ (q0 ◇ (q1 ◇ (q0 ◇ q0)))):=by
    intro q0 q1 q2 q3
    exact ((congrArg (fun t => q2 ◇ t) (congrArg (fun t => (q0 ◇ (q0 ◇ (q1 ◇ (q0 ◇ q0)))) ◇ t) (congrArg (fun t => (q0 ◇ (q0 ◇ (q1 ◇ (q0 ◇ q0)))) ◇ t) (congrArg (fun t => q3 ◇ t) ((h q0 (q0 ◇ (q0 ◇ (q1 ◇ (q0 ◇ q0)))) q1).symm))))).symm).trans ((h (q0 ◇ (q0 ◇ (q1 ◇ (q0 ◇ q0)))) q2 q3).symm)
  have p1 : forall (q0 q1 q2 q3:G), (q2 ◇ (((q3 ◇ (q0 ◇ (q3 ◇ q3))) ◇ ((q3 ◇ (q0 ◇ (q3 ◇ q3))) ◇ (q1 ◇ ((q3 ◇ (q0 ◇ (q3 ◇ q3))) ◇ (q3 ◇ (q0 ◇ (q3 ◇ q3))))))) ◇ q3)) = ((q3 ◇ (q0 ◇ (q3 ◇ q3))) ◇ ((q3 ◇ (q0 ◇ (q3 ◇ q3))) ◇ (q1 ◇ ((q3 ◇ (q0 ◇ (q3 ◇ q3))) ◇ (q3 ◇ (q0 ◇ (q3 ◇ q3))))))):=by
    intro q0 q1 q2 q3
    exact ((congrArg (fun t => q2 ◇ t) (congrArg (fun t => ((q3 ◇ (q0 ◇ (q3 ◇ q3))) ◇ ((q3 ◇ (q0 ◇ (q3 ◇ q3))) ◇ (q1 ◇ ((q3 ◇ (q0 ◇ (q3 ◇ q3))) ◇ (q3 ◇ (q0 ◇ (q3 ◇ q3))))))) ◇ t) ((h q3 ((q3 ◇ (q0 ◇ (q3 ◇ q3))) ◇ ((q3 ◇ (q0 ◇ (q3 ◇ q3))) ◇ (q1 ◇ ((q3 ◇ (q0 ◇ (q3 ◇ q3))) ◇ (q3 ◇ (q0 ◇ (q3 ◇ q3))))))) q0).symm))).symm).trans (p0 (q3 ◇ (q0 ◇ (q3 ◇ q3))) q1 q2 q3)
  have p2 : forall (q0 q1 q2 q3 q4:G), (q4 ◇ ((q2 ◇ (q2 ◇ (q3 ◇ (q2 ◇ q2)))) ◇ ((q2 ◇ (q0 ◇ (q2 ◇ q2))) ◇ ((q2 ◇ (q0 ◇ (q2 ◇ q2))) ◇ (q1 ◇ ((q2 ◇ (q0 ◇ (q2 ◇ q2))) ◇ (q2 ◇ (q0 ◇ (q2 ◇ q2))))))))) = (q2 ◇ (q2 ◇ (q3 ◇ (q2 ◇ q2)))):=by
    intro q0 q1 q2 q3 q4
    exact ((congrArg (fun t => q4 ◇ t) (congrArg (fun t => (q2 ◇ (q2 ◇ (q3 ◇ (q2 ◇ q2)))) ◇ t) (p1 q0 q1 (q2 ◇ (q2 ◇ (q3 ◇ (q2 ◇ q2)))) q2))).symm).trans (p0 q2 q3 q4 ((q2 ◇ (q0 ◇ (q2 ◇ q2))) ◇ ((q2 ◇ (q0 ◇ (q2 ◇ q2))) ◇ (q1 ◇ ((q2 ◇ (q0 ◇ (q2 ◇ q2))) ◇ (q2 ◇ (q0 ◇ (q2 ◇ q2))))))))
  have p3 : forall (q0 q1 q2 q3:G), (q3 ◇ (q1 ◇ (q0 ◇ (q1 ◇ q1)))) = (q1 ◇ (q1 ◇ (q2 ◇ (q1 ◇ q1)))):=by
    intro q0 q1 q2 q3
    exact ((congrArg (fun t => q3 ◇ t) ((h (q1 ◇ (q0 ◇ (q1 ◇ q1))) (q1 ◇ (q1 ◇ (q2 ◇ (q1 ◇ q1)))) q0).symm)).symm).trans (p2 q0 q0 q1 q2 q3)
  have p4 : forall (q0 q1 q2 q3:G), (q3 ◇ (q1 ◇ (q2 ◇ (q0 ◇ (q2 ◇ q2))))) = q2:=by
    intro q0 q1 q2 q3
    exact ((congrArg (fun t => q3 ◇ t) ((p3 q0 q2 q0 q1).symm)).symm).trans ((h q2 q3 q0).symm)
  have p5 : forall (q0 q1:G), (q1 ◇ q1) = (q0 ◇ q1):=by
    intro q0 q1
    exact (((congrArg (fun t => q0 ◇ t) (p4 (q1 ◇ q1) (q1 ◇ q1) q1 (q1 ◇ q1))).symm).trans ((h (q1 ◇ q1) q0 q1).symm)).symm
  have p6 : forall (q0 q1 q2 q3:G), (q2 ◇ (q1 ◇ (q1 ◇ (q3 ◇ (q0 ◇ q1))))) = q1:=by
    intro q0 q1 q2 q3
    exact ((congrArg (fun t => q2 ◇ t) (congrArg (fun t => q1 ◇ t) (congrArg (fun t => q1 ◇ t) (congrArg (fun t => q3 ◇ t) (p5 q0 q1))))).symm).trans ((h q1 q2 q3).symm)
  exact (calc
    x = x:=rfl
    _ = (y ◇ (x ◇ (x ◇ (z ◇ (w ◇ x))))):=(p6 w x y z).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_4918_to_4930 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_4918_to_4930
