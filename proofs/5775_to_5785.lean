-- Equation5775 → Equation5785
-- Recorded verdict: true
-- Premise: x = y ◇ (x ◇ (x ◇ ((x ◇ x) ◇ x)))
-- Conclusion: x = y ◇ (x ◇ (x ◇ ((y ◇ x) ◇ x)))
-- Original submission SHA-256: 33c94696b7308778b961fe310866aa2d5127592df29184a5c88214f11c162d1d
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x = y ◇ (x ◇ (x ◇ ((x ◇ x) ◇ x)))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x = y ◇ (x ◇ (x ◇ ((y ◇ x) ◇ x)))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y
  have cg : ∀ (f:G → G) {a b:G}, a = b → f a = f b:=by
    intro f a b p
    exact congrArg f p
  have p0 : forall (q0 q1:G), (q1 ◇ ((q0 ◇ (q0 ◇ ((q0 ◇ q0) ◇ q0))) ◇ ((q0 ◇ (q0 ◇ ((q0 ◇ q0) ◇ q0))) ◇ q0))) = (q0 ◇ (q0 ◇ ((q0 ◇ q0) ◇ q0))):=by
    intro q0 q1
    exact ((cg (fun t => q1 ◇ t) (cg (fun t => (q0 ◇ (q0 ◇ ((q0 ◇ q0) ◇ q0))) ◇ t) (cg (fun t => (q0 ◇ (q0 ◇ ((q0 ◇ q0) ◇ q0))) ◇ t) ((h q0 ((q0 ◇ (q0 ◇ ((q0 ◇ q0) ◇ q0))) ◇ (q0 ◇ (q0 ◇ ((q0 ◇ q0) ◇ q0))))).symm)))).symm).trans ((h (q0 ◇ (q0 ◇ ((q0 ◇ q0) ◇ q0))) q1).symm)
  have p1 : forall (q0 q1:G), (q1 ◇ (((q0 ◇ (q0 ◇ ((q0 ◇ q0) ◇ q0))) ◇ ((q0 ◇ (q0 ◇ ((q0 ◇ q0) ◇ q0))) ◇ q0)) ◇ (((q0 ◇ (q0 ◇ ((q0 ◇ q0) ◇ q0))) ◇ ((q0 ◇ (q0 ◇ ((q0 ◇ q0) ◇ q0))) ◇ q0)) ◇ (q0 ◇ (q0 ◇ ((q0 ◇ q0) ◇ q0)))))) = ((q0 ◇ (q0 ◇ ((q0 ◇ q0) ◇ q0))) ◇ ((q0 ◇ (q0 ◇ ((q0 ◇ q0) ◇ q0))) ◇ q0)):=by
    intro q0 q1
    exact ((cg (fun t => q1 ◇ t) (cg (fun t => ((q0 ◇ (q0 ◇ ((q0 ◇ q0) ◇ q0))) ◇ ((q0 ◇ (q0 ◇ ((q0 ◇ q0) ◇ q0))) ◇ q0)) ◇ t) (cg (fun t => ((q0 ◇ (q0 ◇ ((q0 ◇ q0) ◇ q0))) ◇ ((q0 ◇ (q0 ◇ ((q0 ◇ q0) ◇ q0))) ◇ q0)) ◇ t) (p0 q0 (((q0 ◇ (q0 ◇ ((q0 ◇ q0) ◇ q0))) ◇ ((q0 ◇ (q0 ◇ ((q0 ◇ q0) ◇ q0))) ◇ q0)) ◇ ((q0 ◇ (q0 ◇ ((q0 ◇ q0) ◇ q0))) ◇ ((q0 ◇ (q0 ◇ ((q0 ◇ q0) ◇ q0))) ◇ q0))))))).symm).trans ((h ((q0 ◇ (q0 ◇ ((q0 ◇ q0) ◇ q0))) ◇ ((q0 ◇ (q0 ◇ ((q0 ◇ q0) ◇ q0))) ◇ q0)) q1).symm)
  have p2 : forall (q0 q1:G), (q1 ◇ (((q0 ◇ (q0 ◇ ((q0 ◇ q0) ◇ q0))) ◇ ((q0 ◇ (q0 ◇ ((q0 ◇ q0) ◇ q0))) ◇ q0)) ◇ q0)) = ((q0 ◇ (q0 ◇ ((q0 ◇ q0) ◇ q0))) ◇ ((q0 ◇ (q0 ◇ ((q0 ◇ q0) ◇ q0))) ◇ q0)):=by
    intro q0 q1
    exact ((cg (fun t => q1 ◇ t) (cg (fun t => ((q0 ◇ (q0 ◇ ((q0 ◇ q0) ◇ q0))) ◇ ((q0 ◇ (q0 ◇ ((q0 ◇ q0) ◇ q0))) ◇ q0)) ◇ t) ((h q0 ((q0 ◇ (q0 ◇ ((q0 ◇ q0) ◇ q0))) ◇ ((q0 ◇ (q0 ◇ ((q0 ◇ q0) ◇ q0))) ◇ q0))).symm))).symm).trans (p1 q0 q1)
  have p3 : forall (q0 q1:G), (q1 ◇ ((((q0 ◇ (q0 ◇ ((q0 ◇ q0) ◇ q0))) ◇ ((q0 ◇ (q0 ◇ ((q0 ◇ q0) ◇ q0))) ◇ q0)) ◇ q0) ◇ (q0 ◇ (q0 ◇ ((q0 ◇ q0) ◇ q0))))) = (((q0 ◇ (q0 ◇ ((q0 ◇ q0) ◇ q0))) ◇ ((q0 ◇ (q0 ◇ ((q0 ◇ q0) ◇ q0))) ◇ q0)) ◇ q0):=by
    intro q0 q1
    exact ((cg (fun t => q1 ◇ t) (cg (fun t => (((q0 ◇ (q0 ◇ ((q0 ◇ q0) ◇ q0))) ◇ ((q0 ◇ (q0 ◇ ((q0 ◇ q0) ◇ q0))) ◇ q0)) ◇ q0) ◇ t) (p0 q0 (((q0 ◇ (q0 ◇ ((q0 ◇ q0) ◇ q0))) ◇ ((q0 ◇ (q0 ◇ ((q0 ◇ q0) ◇ q0))) ◇ q0)) ◇ q0)))).symm).trans (((cg (fun t => q1 ◇ t) (cg (fun t => (((q0 ◇ (q0 ◇ ((q0 ◇ q0) ◇ q0))) ◇ ((q0 ◇ (q0 ◇ ((q0 ◇ q0) ◇ q0))) ◇ q0)) ◇ q0) ◇ t) (cg (fun t => (((q0 ◇ (q0 ◇ ((q0 ◇ q0) ◇ q0))) ◇ ((q0 ◇ (q0 ◇ ((q0 ◇ q0) ◇ q0))) ◇ q0)) ◇ q0) ◇ t) (p2 q0 ((((q0 ◇ (q0 ◇ ((q0 ◇ q0) ◇ q0))) ◇ ((q0 ◇ (q0 ◇ ((q0 ◇ q0) ◇ q0))) ◇ q0)) ◇ q0) ◇ (((q0 ◇ (q0 ◇ ((q0 ◇ q0) ◇ q0))) ◇ ((q0 ◇ (q0 ◇ ((q0 ◇ q0) ◇ q0))) ◇ q0)) ◇ q0)))))).symm).trans ((h (((q0 ◇ (q0 ◇ ((q0 ◇ q0) ◇ q0))) ◇ ((q0 ◇ (q0 ◇ ((q0 ◇ q0) ◇ q0))) ◇ q0)) ◇ q0) q1).symm))
  have p4 : forall (q0 q1:G), (((q0 ◇ (q0 ◇ ((q0 ◇ q0) ◇ q0))) ◇ ((q0 ◇ (q0 ◇ ((q0 ◇ q0) ◇ q0))) ◇ q0)) ◇ q0) = (q1 ◇ q0):=by
    intro q0 q1
    exact (((cg (fun t => q1 ◇ t) ((h q0 (((q0 ◇ (q0 ◇ ((q0 ◇ q0) ◇ q0))) ◇ ((q0 ◇ (q0 ◇ ((q0 ◇ q0) ◇ q0))) ◇ q0)) ◇ q0)).symm)).symm).trans (p3 q0 q1)).symm
  have p5 : forall (q0 q1:G), (q1 ◇ q0) = (q0 ◇ q0):=by
    intro q0 q1
    exact ((p4 q0 q1).symm).trans (p4 q0 q0)
  have p6 : forall (x y q0 q1:G), (y ◇ (x ◇ (x ◇ (x ◇ x)))) = x:=by
    intro x y q0 q1
    exact ((h x y).trans (cg (fun t => y ◇ t) (cg (fun t => x ◇ t) (cg (fun t => x ◇ t) (p5 x (x ◇ x)))))).symm
  exact (calc
    x = x:=rfl
    _ = (y ◇ (x ◇ (x ◇ ((y ◇ x) ◇ x)))):=(((cg (fun t => y ◇ t) (cg (fun t => x ◇ t) (cg (fun t => x ◇ t) (cg (fun t => t ◇ x) (p5 x y))))).trans (cg (fun t => y ◇ t) (cg (fun t => x ◇ t) (cg (fun t => x ◇ t) (p5 x (x ◇ x)))))).trans (p6 x y (y ◇ (x ◇ (x ◇ (x ◇ x)))) (y ◇ (x ◇ (x ◇ (x ◇ x)))))).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_5775_to_5785 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_5775_to_5785
