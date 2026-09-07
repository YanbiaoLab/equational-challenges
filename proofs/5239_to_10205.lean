-- Equation5239 → Equation10205
-- Recorded verdict: true
-- Premise: x = y ◇ (z ◇ (x ◇ (z ◇ (y ◇ y))))
-- Conclusion: x = y ◇ ((x ◇ y) ◇ ((x ◇ z) ◇ z))
-- Original submission SHA-256: 47c90998141bbe49ca288da3bcd460f66163ebb30c19c1823e6ef1acad0be00d
-- Generator: equational-challenges standalone v1
-- All project definitions are embedded in this file.
import Mathlib.Tactic

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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = y ◇ (z ◇ (x ◇ (z ◇ (y ◇ y))))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = y ◇ ((x ◇ y) ◇ ((x ◇ z) ◇ z))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have cg : ∀ (f:G → G) {a b:G}, a = b → f a = f b:=by
    intro f a b p
    exact congrArg f p
  have apc0 : forall (q0:G), ((q0 ◇ q0) ◇ q0) = (q0 ◇ q0):=by
    intro q0
    exact ((cg (fun t => (q0 ◇ q0) ◇ t) ((h q0 q0 (q0 ◇ q0)).symm)).symm).trans ((h (q0 ◇ q0) (q0 ◇ q0) q0).symm)
  have apc1 : forall (q1 q0:G), ((q0 ◇ (q1 ◇ q1)) ◇ (q0 ◇ (q0 ◇ (q1 ◇ q1)))) = q1:=by
    intro q1 q0
    exact ((cg (fun t => (q0 ◇ (q1 ◇ q1)) ◇ t) (cg (fun t => q0 ◇ t) ((h (q0 ◇ (q1 ◇ q1)) q1 q0).symm))).symm).trans ((h q1 (q0 ◇ (q1 ◇ q1)) q0).symm)
  have apc2 : forall (q2 q3:G), (q3 ◇ (((q3 ◇ q3) ◇ (q3 ◇ q3)) ◇ (q2 ◇ ((q3 ◇ q3) ◇ (q3 ◇ q3))))) = q2:=by
    intro q2 q3
    exact ((cg (fun t => q3 ◇ t) (cg (fun t => ((q3 ◇ q3) ◇ (q3 ◇ q3)) ◇ t) (cg (fun t => q2 ◇ t) (apc0 (q3 ◇ q3))))).symm).trans ((h q2 q3 ((q3 ◇ q3) ◇ (q3 ◇ q3))).symm)
  have apc3 : forall (q4:G), ((q4 ◇ q4) ◇ (q4 ◇ q4)) = (q4 ◇ q4):=by
    intro q4
    exact (((apc0 q4).symm).trans (((cg (fun t => (q4 ◇ q4) ◇ t) (apc2 q4 q4)).symm).trans ((h ((q4 ◇ q4) ◇ (q4 ◇ q4)) (q4 ◇ q4) q4).symm))).symm
  have apc4 : forall (q5:G), (q5 ◇ q5) = q5:=by
    intro q5
    exact ((((cg (fun t => (q5 ◇ q5) ◇ t) (cg (fun t => (q5 ◇ q5) ◇ t) (apc3 q5))).trans (cg (fun t => (q5 ◇ q5) ◇ t) (apc3 q5))).trans (apc3 q5)).symm).trans (((cg (fun t => t ◇ ((q5 ◇ q5) ◇ ((q5 ◇ q5) ◇ (q5 ◇ q5)))) (apc3 q5)).symm).trans (apc1 q5 (q5 ◇ q5)))
  have apc5 : forall (x y z:G), (y ◇ (z ◇ (x ◇ (z ◇ y)))) = x:=by
    intro x y z
    exact ((cg (fun t => y ◇ t) (cg (fun t => z ◇ t) (cg (fun t => x ◇ t) (cg (fun t => z ◇ t) (apc4 y))))).symm).trans ((((h x y z).symm).trans (h x x x)).trans (((((cg (fun t => x ◇ t) (cg (fun t => x ◇ t) (cg (fun t => x ◇ t) (cg (fun t => x ◇ t) (apc4 x))))).trans (cg (fun t => x ◇ t) (cg (fun t => x ◇ t) (cg (fun t => x ◇ t) (apc4 x))))).trans (cg (fun t => x ◇ t) (cg (fun t => x ◇ t) (apc4 x)))).trans (cg (fun t => x ◇ t) (apc4 x))).trans (apc4 x)))
  have apc7 : forall (q6 q7:G), (q6 ◇ (q7 ◇ (q7 ◇ q6))) = (q7 ◇ q6):=by
    intro q6 q7
    exact ((cg (fun t => q6 ◇ t) (cg (fun t => q7 ◇ t) (cg (fun t => q7 ◇ t) (apc4 q6)))).symm).trans ((((cg (fun t => q6 ◇ t) (cg (fun t => q7 ◇ t) (apc4 (q7 ◇ (q6 ◇ q6))))).symm).trans ((h (q7 ◇ (q6 ◇ q6)) q6 q7).symm)).trans (cg (fun t => q7 ◇ t) (apc4 q6)))
  have apc10 : forall (q8 q9:G), ((q8 ◇ q9) ◇ q9) = q8:=by
    intro q8 q9
    exact ((cg (fun t => (q8 ◇ q9) ◇ t) (apc5 q9 q9 q8)).symm).trans (apc5 q8 (q8 ◇ q9) q9)
  have apc13 : forall (q10 q11:G), (q11 ◇ ((q10 ◇ q11) ◇ q10)) = q10:=by
    intro q10 q11
    exact (((cg (fun t => q11 ◇ t) (cg (fun t => (q10 ◇ q11) ◇ t) (apc10 q10 q11))).symm).trans (apc7 q11 (q10 ◇ q11))).trans (apc10 q10 q11)
  exact (calc
    x = x:=rfl
    _ = (y ◇ ((x ◇ y) ◇ ((x ◇ z) ◇ z))):=((cg (fun t => y ◇ t) (cg (fun t => (x ◇ y) ◇ t) (apc10 x z))).trans (apc13 x y)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_5239_to_10205 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_5239_to_10205
