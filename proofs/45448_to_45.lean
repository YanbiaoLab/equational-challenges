-- Equation45448 → Equation45
-- Recorded verdict: true
-- Premise: x ◇ y = y ◇ (((y ◇ z) ◇ x) ◇ x)
-- Conclusion: x ◇ y = z ◇ y
-- Original submission SHA-256: 22dbcd7e60a637c25e095e78702f5b6c117f63bb586e4ee05f52599d367a2671
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = y ◇ (((y ◇ z) ◇ x) ◇ x)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = z ◇ y
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have cg : ∀ (f:G → G) {a b:G}, a = b → f a = f b:=by
    intro f a b p
    exact congrArg f p
  have p0 : forall (q0 q1 q2:G), (q2 ◇ (((q0 ◇ q2) ◇ q1) ◇ q1)) = (q1 ◇ q2):=by
    intro q0 q1 q2
    exact ((cg (fun t => q2 ◇ t) (cg (fun t => t ◇ q1) (cg (fun t => t ◇ q1) ((h q0 q2 q0).symm)))).symm).trans ((h q1 q2 (((q2 ◇ q0) ◇ q0) ◇ q0)).symm)
  have p1 : forall (x y z:G), (y ◇ (((y ◇ z) ◇ x) ◇ x)) = (y ◇ (((y ◇ x) ◇ x) ◇ x)):=by
    intro x y z
    exact ((h x y z).symm).trans (h x y x)
  have p2 : forall (x y z:G), (y ◇ (((y ◇ x) ◇ x) ◇ x)) = (x ◇ y):=by
    intro x y z
    exact ((h x y x).trans (p1 x y x)).symm
  have p3 : forall (q0 q1 q2 q3:G), ((((q2 ◇ q1) ◇ q0) ◇ q0) ◇ (((q0 ◇ q2) ◇ q3) ◇ q3)) = (q3 ◇ (((q2 ◇ q1) ◇ q0) ◇ q0)):=by
    intro q0 q1 q2 q3
    exact ((cg (fun t => (((q2 ◇ q1) ◇ q0) ◇ q0) ◇ t) (cg (fun t => t ◇ q3) (cg (fun t => t ◇ q3) ((h q0 q2 q1).symm)))).symm).trans (p0 q2 q3 (((q2 ◇ q1) ◇ q0) ◇ q0))
  have p4 : forall (q0 q1 q2 q3:G), ((((q0 ◇ q2) ◇ q1) ◇ q1) ◇ (((q1 ◇ q2) ◇ q3) ◇ q3)) = (q3 ◇ (((q0 ◇ q2) ◇ q1) ◇ q1)):=by
    intro q0 q1 q2 q3
    exact ((cg (fun t => (((q0 ◇ q2) ◇ q1) ◇ q1) ◇ t) (cg (fun t => t ◇ q3) (cg (fun t => t ◇ q3) (p0 q0 q1 q2)))).symm).trans (p0 q2 q3 (((q0 ◇ q2) ◇ q1) ◇ q1))
  have p5 : forall (q0 q1 q2 q3:G), (((((q2 ◇ q3) ◇ q1) ◇ q0) ◇ q0) ◇ q2) = (q2 ◇ ((q0 ◇ (q2 ◇ q3)) ◇ ((((q2 ◇ q3) ◇ q1) ◇ q0) ◇ q0))):=by
    intro q0 q1 q2 q3
    exact (((cg (fun t => q2 ◇ t) (cg (fun t => t ◇ ((((q2 ◇ q3) ◇ q1) ◇ q0) ◇ q0)) ((h q0 (q2 ◇ q3) q1).symm))).symm).trans ((h ((((q2 ◇ q3) ◇ q1) ◇ q0) ◇ q0) q2 q3).symm)).symm
  have p6 : forall (q0 q1 q2 q3 q4:G), (q4 ◇ (((q3 ◇ (((q3 ◇ q1) ◇ q0) ◇ q0)) ◇ q2) ◇ q2)) = (q4 ◇ (((q0 ◇ q3) ◇ q2) ◇ q2)):=by
    intro q0 q1 q2 q3 q4
    exact (((p4 q0 q2 q3 q4).symm).trans (((cg (fun t => t ◇ (((q2 ◇ q3) ◇ q4) ◇ q4)) (cg (fun t => t ◇ q2) (cg (fun t => t ◇ q2) ((h q0 q3 q1).symm)))).symm).trans (p3 q2 (((q3 ◇ q1) ◇ q0) ◇ q0) q3 q4))).symm
  have p7 : forall (q0 q1 q2 q3 q5 q4:G), ((((q3 ◇ (((q3 ◇ q1) ◇ q0) ◇ q0)) ◇ q2) ◇ q2) ◇ q5) = ((((q0 ◇ q3) ◇ q2) ◇ q2) ◇ q5):=by
    intro q0 q1 q2 q3 q5 q4
    exact ((((cg (fun t => q5 ◇ t) (cg (fun t => t ◇ (((q0 ◇ q3) ◇ q2) ◇ q2)) (p6 q0 q1 q2 q3 (q4 ◇ q5)))).trans (p0 q4 (((q0 ◇ q3) ◇ q2) ◇ q2) q5)).symm).trans (((cg (fun t => q5 ◇ t) (p6 q0 q1 q2 q3 ((q4 ◇ q5) ◇ (((q3 ◇ (((q3 ◇ q1) ◇ q0) ◇ q0)) ◇ q2) ◇ q2)))).symm).trans (p0 q4 (((q3 ◇ (((q3 ◇ q1) ◇ q0) ◇ q0)) ◇ q2) ◇ q2) q5))).symm
  have p8 : forall (q0 q1 q2:G), (q2 ◇ (q2 ◇ ((q2 ◇ (q2 ◇ q1)) ◇ ((((q2 ◇ q1) ◇ q0) ◇ q2) ◇ q2)))) = (q2 ◇ q2):=by
    intro q0 q1 q2
    exact ((cg (fun t => q2 ◇ t) (p5 q2 q0 q2 q1)).symm).trans (p0 ((q2 ◇ q1) ◇ q0) q2 q2)
  have p9 : forall (q0 q1:G), (q1 ◇ (q1 ◇ (q1 ◇ (q1 ◇ (q1 ◇ q0))))) = (q1 ◇ q1):=by
    intro q0 q1
    exact ((cg (fun t => q1 ◇ t) (cg (fun t => q1 ◇ t) (p0 (q1 ◇ q0) q1 (q1 ◇ (q1 ◇ q0))))).symm).trans (p8 (q1 ◇ (q1 ◇ q0)) q0 q1)
  have pa : forall (q0:G), (q0 ◇ (q0 ◇ q0)) = (q0 ◇ q0):=by
    intro q0
    exact ((cg (fun t => q0 ◇ t) (p9 q0 q0)).symm).trans (p9 (q0 ◇ q0) q0)
  have pb : forall (q0:G), ((((q0 ◇ q0) ◇ q0) ◇ q0) ◇ (q0 ◇ q0)) = (q0 ◇ q0):=by
    intro q0
    exact ((cg (fun t => (((q0 ◇ q0) ◇ q0) ◇ q0) ◇ t) (p0 q0 q0 q0)).symm).trans ((((cg (fun t => (((q0 ◇ q0) ◇ q0) ◇ q0) ◇ t) (p3 q0 q0 q0 q0)).symm).trans (pa (((q0 ◇ q0) ◇ q0) ◇ q0))).trans ((p3 q0 q0 q0 q0).trans (p0 q0 q0 q0)))
  have pc : forall (q0:G), (q0 ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) = ((q0 ◇ q0) ◇ q0):=by
    intro q0
    exact ((cg (fun t => q0 ◇ t) (cg (fun t => t ◇ (q0 ◇ q0)) (pb q0))).symm).trans (p0 ((q0 ◇ q0) ◇ q0) (q0 ◇ q0) q0)
  have pd : forall (q0 q1:G), ((q0 ◇ q0) ◇ (((q0 ◇ q0) ◇ q1) ◇ q1)) = (q1 ◇ (q0 ◇ q0)):=by
    intro q0 q1
    exact ((cg (fun t => (q0 ◇ q0) ◇ t) (cg (fun t => t ◇ q1) (cg (fun t => t ◇ q1) (pa q0)))).symm).trans (p0 q0 q1 (q0 ◇ q0))
  have pe : forall (q0 q1:G), ((((q1 ◇ q1) ◇ q0) ◇ q0) ◇ q1) = (q1 ◇ ((q0 ◇ (q1 ◇ q1)) ◇ (((q1 ◇ q1) ◇ q0) ◇ q0))):=by
    intro q0 q1
    exact (((cg (fun t => q1 ◇ t) (cg (fun t => t ◇ (((q1 ◇ q1) ◇ q0) ◇ q0)) (pd q1 q0))).symm).trans ((h (((q1 ◇ q1) ◇ q0) ◇ q0) q1 q1).symm)).symm
  have pf : forall (q0:G), ((q0 ◇ q0) ◇ q0) = (q0 ◇ q0):=by
    intro q0
    exact (((((cg (fun t => t ◇ q0) (cg (fun t => q0 ◇ t) (cg (fun t => t ◇ (((q0 ◇ q0) ◇ q0) ◇ q0)) (pa q0)))).trans (cg (fun t => t ◇ q0) (cg (fun t => q0 ◇ t) (pd q0 q0)))).trans (cg (fun t => t ◇ q0) (cg (fun t => q0 ◇ t) (pa q0)))).trans (cg (fun t => t ◇ q0) (pa q0))).symm).trans ((((cg (fun t => t ◇ q0) (pe q0 q0)).symm).trans (p5 q0 q0 q0 q0)).trans ((((cg (fun t => q0 ◇ t) (cg (fun t => t ◇ ((((q0 ◇ q0) ◇ q0) ◇ q0) ◇ q0)) (pa q0))).trans (cg (fun t => q0 ◇ t) (p2 q0 (q0 ◇ q0) ((q0 ◇ q0) ◇ ((((q0 ◇ q0) ◇ q0) ◇ q0) ◇ q0))))).trans (cg (fun t => q0 ◇ t) (pa q0))).trans (pa q0)))
  have pg : forall (q0:G), ((q0 ◇ q0) ◇ (q0 ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0)))) = (q0 ◇ q0):=by
    intro q0
    exact ((((cg (fun t => (q0 ◇ q0) ◇ t) (cg (fun t => q0 ◇ t) (cg (fun t => (q0 ◇ (q0 ◇ q0)) ◇ t) (cg (fun t => t ◇ q0) (pf q0))))).trans (cg (fun t => (q0 ◇ q0) ◇ t) (cg (fun t => q0 ◇ t) (cg (fun t => (q0 ◇ (q0 ◇ q0)) ◇ t) (pf q0))))).trans (cg (fun t => (q0 ◇ q0) ◇ t) (cg (fun t => q0 ◇ t) (cg (fun t => t ◇ (q0 ◇ q0)) (pa q0))))).symm).trans ((((cg (fun t => (q0 ◇ q0) ◇ t) (pe q0 q0)).symm).trans ((h q0 (q0 ◇ q0) q0).symm)).trans (pa q0))
  have ph : forall (q0:G), (q0 ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) = (q0 ◇ q0):=by
    intro q0
    exact (pc q0).trans (pf q0)
  have pi : forall (q0:G), ((q0 ◇ q0) ◇ (q0 ◇ q0)) = (q0 ◇ q0):=by
    intro q0
    exact ((cg (fun t => (q0 ◇ q0) ◇ t) (ph q0)).symm).trans (pg q0)
  have pj : forall (q0 q1:G), (q0 ◇ ((q0 ◇ q1) ◇ (q0 ◇ q1))) = ((q0 ◇ q1) ◇ q0):=by
    intro q0 q1
    exact ((cg (fun t => q0 ◇ t) (pf (q0 ◇ q1))).symm).trans ((h (q0 ◇ q1) q0 q1).symm)
  have pk : forall (q0 q1:G), (q1 ◇ ((q0 ◇ q1) ◇ (q0 ◇ q1))) = ((q0 ◇ q1) ◇ q1):=by
    intro q0 q1
    exact ((cg (fun t => q1 ◇ t) (pf (q0 ◇ q1))).symm).trans (p0 q0 (q0 ◇ q1) q1)
  have pl : forall (q0 q1:G), ((((q0 ◇ q1) ◇ q1) ◇ q1) ◇ (q1 ◇ q1)) = (q1 ◇ q1):=by
    intro q0 q1
    exact ((cg (fun t => (((q0 ◇ q1) ◇ q1) ◇ q1) ◇ t) (pf q1)).symm).trans ((((cg (fun t => (((q0 ◇ q1) ◇ q1) ◇ q1) ◇ t) (cg (fun t => t ◇ q1) (pf q1))).symm).trans (p4 q0 q1 q1 q1)).trans (p0 q0 q1 q1))
  have pm : forall (q0 q1:G), (((q0 ◇ q1) ◇ q1) ◇ (q1 ◇ q1)) = ((q1 ◇ q1) ◇ ((q0 ◇ q1) ◇ q1)):=by
    intro q0 q1
    exact ((cg (fun t => ((q0 ◇ q1) ◇ q1) ◇ t) (pi q1)).symm).trans (((cg (fun t => ((q0 ◇ q1) ◇ q1) ◇ t) (cg (fun t => t ◇ (q1 ◇ q1)) (pl q0 q1))).symm).trans ((h (q1 ◇ q1) ((q0 ◇ q1) ◇ q1) q1).symm))
  have pn : forall (q0 q1:G), ((q1 ◇ q1) ◇ (((q0 ◇ q1) ◇ q1) ◇ q1)) = (q1 ◇ q1):=by
    intro q0 q1
    exact (((((cg (fun t => (((q0 ◇ q1) ◇ q1) ◇ q1) ◇ t) (cg (fun t => t ◇ (q1 ◇ q1)) (pi q1))).trans (cg (fun t => (((q0 ◇ q1) ◇ q1) ◇ q1) ◇ t) (pi q1))).trans (pl q0 q1)).symm).trans (((cg (fun t => (((q0 ◇ q1) ◇ q1) ◇ q1) ◇ t) (cg (fun t => t ◇ (q1 ◇ q1)) (cg (fun t => t ◇ (q1 ◇ q1)) (pl q0 q1)))).symm).trans (p2 (q1 ◇ q1) (((q0 ◇ q1) ◇ q1) ◇ q1) q0))).symm
  have po : forall (q0 q1:G), ((((q0 ◇ q1) ◇ q1) ◇ q1) ◇ q1) = (q1 ◇ q1):=by
    intro q0 q1
    exact ((((cg (fun t => q1 ◇ t) (pn q0 q1)).trans (pa q1)).symm).trans (((cg (fun t => q1 ◇ t) (cg (fun t => t ◇ (((q0 ◇ q1) ◇ q1) ◇ q1)) (pn q0 q1))).symm).trans ((h (((q0 ◇ q1) ◇ q1) ◇ q1) q1 q1).symm))).symm
  have pp : forall (q0 q1:G), ((q0 ◇ q1) ◇ (q1 ◇ q1)) = (q1 ◇ (q0 ◇ q1)):=by
    intro q0 q1
    exact ((cg (fun t => (q0 ◇ q1) ◇ t) (po q0 q1)).symm).trans ((h q1 (q0 ◇ q1) q1).symm)
  have pq : forall (q1 q2 q0:G), (((q1 ◇ q2) ◇ (q1 ◇ q2)) ◇ q1) = ((q1 ◇ q2) ◇ q1):=by
    intro q1 q2 q0
    exact ((cg (fun t => t ◇ q1) (pn q0 (q1 ◇ q2))).symm).trans ((((cg (fun t => t ◇ q1) (cg (fun t => t ◇ (((q0 ◇ (q1 ◇ q2)) ◇ (q1 ◇ q2)) ◇ (q1 ◇ q2))) (pn q0 (q1 ◇ q2)))).symm).trans (p5 (((q0 ◇ (q1 ◇ q2)) ◇ (q1 ◇ q2)) ◇ (q1 ◇ q2)) (q1 ◇ q2) q1 q2)).trans ((((((cg (fun t => q1 ◇ t) (cg (fun t => ((((q0 ◇ (q1 ◇ q2)) ◇ (q1 ◇ q2)) ◇ (q1 ◇ q2)) ◇ (q1 ◇ q2)) ◇ t) (cg (fun t => t ◇ (((q0 ◇ (q1 ◇ q2)) ◇ (q1 ◇ q2)) ◇ (q1 ◇ q2))) (pn q0 (q1 ◇ q2))))).trans (cg (fun t => q1 ◇ t) (cg (fun t => t ◇ (((q1 ◇ q2) ◇ (q1 ◇ q2)) ◇ (((q0 ◇ (q1 ◇ q2)) ◇ (q1 ◇ q2)) ◇ (q1 ◇ q2)))) (po q0 (q1 ◇ q2))))).trans (cg (fun t => q1 ◇ t) (cg (fun t => ((q1 ◇ q2) ◇ (q1 ◇ q2)) ◇ t) (pn q0 (q1 ◇ q2))))).trans (cg (fun t => q1 ◇ t) (pp (q1 ◇ q2) (q1 ◇ q2)))).trans (cg (fun t => q1 ◇ t) (pa (q1 ◇ q2)))).trans (pj q1 q2)))
  have pr : forall (q1 q2 q0:G), (((q1 ◇ q2) ◇ (q1 ◇ q2)) ◇ q2) = ((q1 ◇ q2) ◇ q2):=by
    intro q1 q2 q0
    exact ((cg (fun t => t ◇ q2) (cg (fun t => (q1 ◇ q2) ◇ t) (p0 q0 q1 q2))).symm).trans ((((cg (fun t => t ◇ q2) (cg (fun t => t ◇ (q2 ◇ (((q0 ◇ q2) ◇ q1) ◇ q1))) (p0 q0 q1 q2))).symm).trans (pq q2 (((q0 ◇ q2) ◇ q1) ◇ q1) q0)).trans (cg (fun t => t ◇ q2) (p0 q0 q1 q2)))
  have ps : forall (q0 q1:G), ((q1 ◇ q1) ◇ ((q0 ◇ q1) ◇ q1)) = (q1 ◇ ((q0 ◇ q1) ◇ q1)):=by
    intro q0 q1
    exact (((pp (q0 ◇ q1) q1).symm).trans (pm q0 q1)).symm
  have pt : forall (q0 q1:G), ((((q0 ◇ q1) ◇ q0) ◇ q0) ◇ q0) = (q0 ◇ (q0 ◇ (((q0 ◇ q1) ◇ q0) ◇ q0))):=by
    intro q0 q1
    exact (((cg (fun t => q0 ◇ t) (p4 q0 q0 q1 q0)).symm).trans (pk ((q0 ◇ q1) ◇ q0) q0)).symm
  have pu : forall (q0 q1:G), (q1 ◇ ((q0 ◇ (q1 ◇ q0)) ◇ (q0 ◇ q0))) = ((q0 ◇ q0) ◇ q1):=by
    intro q0 q1
    exact ((((cg (fun t => t ◇ q1) (po q1 q0)).symm).trans (p5 q0 q0 q1 q0)).trans (cg (fun t => q1 ◇ t) (cg (fun t => (q0 ◇ (q1 ◇ q0)) ◇ t) (po q1 q0)))).symm
  have pv : forall (q0 q1:G), ((q1 ◇ q0) ◇ (((q1 ◇ q0) ◇ q1) ◇ q1)) = (q1 ◇ (q1 ◇ q0)):=by
    intro q0 q1
    exact ((cg (fun t => (q1 ◇ q0) ◇ t) (cg (fun t => t ◇ q1) (pq q1 q0 q0))).symm).trans ((h q1 (q1 ◇ q0) (q1 ◇ q0)).symm)
  have pw : forall (q0 q1 q2 q3:G), ((((q0 ◇ (q2 ◇ q3)) ◇ q1) ◇ q1) ◇ q2) = (q2 ◇ ((q1 ◇ (q2 ◇ q3)) ◇ (((q0 ◇ (q2 ◇ q3)) ◇ q1) ◇ q1))):=by
    intro q0 q1 q2 q3
    exact (((cg (fun t => q2 ◇ t) (cg (fun t => t ◇ (((q0 ◇ (q2 ◇ q3)) ◇ q1) ◇ q1)) (p0 q0 q1 (q2 ◇ q3)))).symm).trans ((h (((q0 ◇ (q2 ◇ q3)) ◇ q1) ◇ q1) q2 q3).symm)).symm
  have px : forall (q0 q1:G), (((q0 ◇ q1) ◇ (q0 ◇ q1)) ◇ (q1 ◇ q1)) = ((q0 ◇ q1) ◇ q1):=by
    intro q0 q1
    exact ((cg (fun t => ((q0 ◇ q1) ◇ (q0 ◇ q1)) ◇ t) (po q0 q1)).symm).trans ((((cg (fun t => ((q0 ◇ q1) ◇ (q0 ◇ q1)) ◇ t) (cg (fun t => t ◇ q1) (cg (fun t => t ◇ q1) (pr q0 q1 q0)))).symm).trans (p2 q1 ((q0 ◇ q1) ◇ (q0 ◇ q1)) q0)).trans (pk q0 q1))
  have py : forall (q0 q1:G), (((q0 ◇ q1) ◇ q1) ◇ q1) = (q1 ◇ ((q0 ◇ q1) ◇ q1)):=by
    intro q0 q1
    exact (((cg (fun t => t ◇ (q1 ◇ q1)) (cg (fun t => ((q0 ◇ q1) ◇ q1) ◇ t) (px q0 q1))).trans (px (q0 ◇ q1) q1)).symm).trans ((((cg (fun t => t ◇ (q1 ◇ q1)) (cg (fun t => t ◇ (((q0 ◇ q1) ◇ (q0 ◇ q1)) ◇ (q1 ◇ q1))) (px q0 q1))).symm).trans (pr ((q0 ◇ q1) ◇ (q0 ◇ q1)) (q1 ◇ q1) q0)).trans ((cg (fun t => t ◇ (q1 ◇ q1)) (px q0 q1)).trans (pp (q0 ◇ q1) q1)))
  have pz : forall (q0 q1:G), (q1 ◇ (q0 ◇ ((q1 ◇ q0) ◇ q0))) = (q0 ◇ q1):=by
    intro q0 q1
    exact ((cg (fun t => q1 ◇ t) (py q1 q0)).symm).trans ((h q0 q1 q0).symm)
  have p10 : forall (q0 q1:G), ((q1 ◇ q0) ◇ (q1 ◇ q1)) = (q1 ◇ (q1 ◇ q0)):=by
    intro q0 q1
    exact ((cg (fun t => (q1 ◇ q0) ◇ t) ((h q1 q1 q0).symm)).symm).trans (pz q1 (q1 ◇ q0))
  have p11 : forall (q0 q1:G), (q1 ◇ (q1 ◇ ((q0 ◇ q1) ◇ q1))) = (q1 ◇ q1):=by
    intro q0 q1
    exact ((cg (fun t => q1 ◇ t) (py q0 q1)).symm).trans (p0 q0 q1 q1)
  have p12 : forall (q0 q1:G), ((q1 ◇ ((q0 ◇ q1) ◇ q1)) ◇ q1) = (q1 ◇ q1):=by
    intro q0 q1
    exact ((cg (fun t => t ◇ q1) (py q0 q1)).symm).trans (po q0 q1)
  have p13 : forall (q0 q1:G), ((q1 ◇ q1) ◇ (q0 ◇ q1)) = (q1 ◇ (q0 ◇ q1)):=by
    intro q0 q1
    exact ((cg (fun t => t ◇ (q0 ◇ q1)) (pf q1)).symm).trans ((((cg (fun t => t ◇ (q0 ◇ q1)) (cg (fun t => t ◇ q1) (p12 q0 q1))).symm).trans (pw q1 q1 (q0 ◇ q1) q1)).trans (((((cg (fun t => (q0 ◇ q1) ◇ t) (cg (fun t => (q1 ◇ ((q0 ◇ q1) ◇ q1)) ◇ t) (cg (fun t => t ◇ q1) (p12 q0 q1)))).trans (cg (fun t => (q0 ◇ q1) ◇ t) (cg (fun t => (q1 ◇ ((q0 ◇ q1) ◇ q1)) ◇ t) (pf q1)))).trans (cg (fun t => (q0 ◇ q1) ◇ t) (p10 ((q0 ◇ q1) ◇ q1) q1))).trans (cg (fun t => (q0 ◇ q1) ◇ t) (p11 q0 q1))).trans (pp q0 q1)))
  have p14 : forall (q0 q1:G), ((((q0 ◇ q1) ◇ q0) ◇ q0) ◇ q0) = (q0 ◇ q0):=by
    intro q0 q1
    exact (pt q0 q1).trans (p11 (q0 ◇ q1) q0)
  have p15 : forall (q0 q1:G), (q0 ◇ (q0 ◇ (q0 ◇ (q0 ◇ q1)))) = (q0 ◇ q0):=by
    intro q0 q1
    exact ((cg (fun t => q0 ◇ t) (p10 (q0 ◇ q1) q0)).symm).trans ((((cg (fun t => q0 ◇ t) (cg (fun t => t ◇ (q0 ◇ q0)) (p10 q1 q0))).symm).trans ((h (q0 ◇ q0) q0 q1).symm)).trans (pf q0))
  have p16 : forall (q0 q1:G), (q1 ◇ (((q1 ◇ q0) ◇ q1) ◇ q1)) = (q1 ◇ q1):=by
    intro q0 q1
    exact (((p14 q1 q0).symm).trans (py (q1 ◇ q0) q1)).symm
  have p17 : forall (q0 q1:G), ((q0 ◇ q1) ◇ (((q0 ◇ q1) ◇ q1) ◇ q1)) = (q1 ◇ (q0 ◇ q1)):=by
    intro q0 q1
    exact ((cg (fun t => (q0 ◇ q1) ◇ t) (cg (fun t => t ◇ q1) (pr q0 q1 q0))).symm).trans ((h q1 (q0 ◇ q1) (q0 ◇ q1)).symm)
  have p18 : forall (q0 q1:G), (q0 ◇ ((((q0 ◇ q0) ◇ q1) ◇ q0) ◇ q0)) = (q0 ◇ q0):=by
    intro q0 q1
    exact (((ps ((q0 ◇ q0) ◇ q1) q0).symm).trans ((h q0 (q0 ◇ q0) q1).symm)).trans (pa q0)
  have p19 : forall (q0 q1:G), (((q1 ◇ q1) ◇ q0) ◇ (q1 ◇ q1)) = (q1 ◇ ((q1 ◇ q1) ◇ q0)):=by
    intro q0 q1
    exact ((cg (fun t => ((q1 ◇ q1) ◇ q0) ◇ t) (p18 q1 q0)).symm).trans (pz q1 ((q1 ◇ q1) ◇ q0))
  have p1a : forall (q0 q1:G), (q1 ◇ (q0 ◇ (q0 ◇ (q1 ◇ q0)))) = ((q0 ◇ q0) ◇ q1):=by
    intro q0 q1
    exact ((cg (fun t => q1 ◇ t) (p10 (q1 ◇ q0) q0)).symm).trans (pu q0 q1)
  have p1b : forall (q0 q1:G), (q1 ◇ (q0 ◇ (q0 ◇ (q0 ◇ q1)))) = ((q0 ◇ q0) ◇ q1):=by
    intro q0 q1
    exact ((cg (fun t => q1 ◇ t) (p10 (q0 ◇ q1) q0)).symm).trans (((cg (fun t => q1 ◇ t) (cg (fun t => t ◇ (q0 ◇ q0)) (p10 q1 q0))).symm).trans (p0 q0 (q0 ◇ q0) q1))
  have p1c : forall (q0 q1:G), ((q1 ◇ q1) ◇ (q1 ◇ q0)) = (q1 ◇ (q1 ◇ q0)):=by
    intro q0 q1
    exact (((p10 q0 q1).symm).trans (((cg (fun t => (q1 ◇ q0) ◇ t) (p15 q1 q0)).symm).trans (p1b q1 (q1 ◇ q0)))).symm
  have p1d : forall (q0 q1 q2 q3:G), ((((q0 ◇ (q2 ◇ q3)) ◇ q1) ◇ q1) ◇ q3) = (q3 ◇ ((q1 ◇ (q2 ◇ q3)) ◇ (((q0 ◇ (q2 ◇ q3)) ◇ q1) ◇ q1))):=by
    intro q0 q1 q2 q3
    exact (((cg (fun t => q3 ◇ t) (cg (fun t => t ◇ (((q0 ◇ (q2 ◇ q3)) ◇ q1) ◇ q1)) (p0 q0 q1 (q2 ◇ q3)))).symm).trans (p0 q2 (((q0 ◇ (q2 ◇ q3)) ◇ q1) ◇ q1) q3)).symm
  have p1e : forall (q0 q1 q2:G), (q2 ◇ (q2 ◇ (((q2 ◇ q1) ◇ q0) ◇ q0))) = (q2 ◇ (q0 ◇ q2)):=by
    intro q0 q1 q2
    exact ((((p6 q0 q1 q2 q2 (q0 ◇ q2)).trans (p17 q0 q2)).symm).trans (((cg (fun t => t ◇ (((q2 ◇ (((q2 ◇ q1) ◇ q0) ◇ q0)) ◇ q2) ◇ q2)) ((h q0 q2 q1).symm)).symm).trans (pv (((q2 ◇ q1) ◇ q0) ◇ q0) q2))).symm
  have p1f : forall (q0 q2 q3 q4 q1:G), (((((q0 ◇ q2) ◇ (q3 ◇ q4)) ◇ (q3 ◇ q4)) ◇ (q3 ◇ q4)) ◇ q3) = ((q3 ◇ q4) ◇ q3):=by
    intro q0 q2 q3 q4 q1
    exact (((cg (fun t => t ◇ q3) (p7 q0 q1 (q3 ◇ q4) q2 (q3 ◇ q4) q0)).symm).trans (pw (q2 ◇ (((q2 ◇ q1) ◇ q0) ◇ q0)) (q3 ◇ q4) q3 q4)).trans ((((cg (fun t => q3 ◇ t) (cg (fun t => ((q3 ◇ q4) ◇ (q3 ◇ q4)) ◇ t) (p7 q0 q1 (q3 ◇ q4) q2 (q3 ◇ q4) ((((q2 ◇ (((q2 ◇ q1) ◇ q0) ◇ q0)) ◇ (q3 ◇ q4)) ◇ (q3 ◇ q4)) ◇ (q3 ◇ q4))))).trans (cg (fun t => q3 ◇ t) (p13 (((q0 ◇ q2) ◇ (q3 ◇ q4)) ◇ (q3 ◇ q4)) (q3 ◇ q4)))).trans (cg (fun t => q3 ◇ t) (p0 (q0 ◇ q2) (q3 ◇ q4) (q3 ◇ q4)))).trans (pj q3 q4))
  have p1g : forall (q0 q2 q3 q4 q1:G), (((((q0 ◇ q2) ◇ (q3 ◇ q4)) ◇ (q3 ◇ q4)) ◇ (q3 ◇ q4)) ◇ q4) = ((q3 ◇ q4) ◇ q4):=by
    intro q0 q2 q3 q4 q1
    exact (((cg (fun t => t ◇ q4) (p7 q0 q1 (q3 ◇ q4) q2 (q3 ◇ q4) q0)).symm).trans (p1d (q2 ◇ (((q2 ◇ q1) ◇ q0) ◇ q0)) (q3 ◇ q4) q3 q4)).trans ((((cg (fun t => q4 ◇ t) (cg (fun t => ((q3 ◇ q4) ◇ (q3 ◇ q4)) ◇ t) (p7 q0 q1 (q3 ◇ q4) q2 (q3 ◇ q4) ((((q2 ◇ (((q2 ◇ q1) ◇ q0) ◇ q0)) ◇ (q3 ◇ q4)) ◇ (q3 ◇ q4)) ◇ (q3 ◇ q4))))).trans (cg (fun t => q4 ◇ t) (p13 (((q0 ◇ q2) ◇ (q3 ◇ q4)) ◇ (q3 ◇ q4)) (q3 ◇ q4)))).trans (cg (fun t => q4 ◇ t) (p0 (q0 ◇ q2) (q3 ◇ q4) (q3 ◇ q4)))).trans (pk q3 q4))
  have p1h : forall (q2 q3 q4 q0 q1:G), (((((q4 ◇ q4) ◇ q3) ◇ q2) ◇ q2) ◇ q4) = (q4 ◇ ((q2 ◇ (q4 ◇ q4)) ◇ ((((q4 ◇ q4) ◇ q3) ◇ q2) ◇ q2))):=by
    intro q2 q3 q4 q0 q1
    exact (((cg (fun t => t ◇ q4) (cg (fun t => t ◇ q2) (cg (fun t => t ◇ q2) (cg (fun t => t ◇ q3) (p8 q0 q1 q4))))).symm).trans (p5 q2 q3 q4 (q4 ◇ ((q4 ◇ (q4 ◇ q1)) ◇ ((((q4 ◇ q1) ◇ q0) ◇ q4) ◇ q4))))).trans ((cg (fun t => q4 ◇ t) (cg (fun t => (q2 ◇ (q4 ◇ (q4 ◇ ((q4 ◇ (q4 ◇ q1)) ◇ ((((q4 ◇ q1) ◇ q0) ◇ q4) ◇ q4))))) ◇ t) (cg (fun t => t ◇ q2) (cg (fun t => t ◇ q2) (cg (fun t => t ◇ q3) (p8 q0 q1 q4)))))).trans (cg (fun t => q4 ◇ t) (cg (fun t => t ◇ ((((q4 ◇ q4) ◇ q3) ◇ q2) ◇ q2)) (cg (fun t => q2 ◇ t) (p8 q0 q1 q4)))))
  have p1i : forall (q0 q1:G), (q0 ◇ ((q0 ◇ q1) ◇ (q0 ◇ (q0 ◇ q1)))) = ((q0 ◇ q1) ◇ q0):=by
    intro q0 q1
    exact ((((cg (fun t => q0 ◇ t) (cg (fun t => ((q0 ◇ q1) ◇ (q0 ◇ q0)) ◇ t) (cg (fun t => t ◇ (q0 ◇ q1)) (cg (fun t => t ◇ (q0 ◇ q1)) (p1c q1 q0))))).trans (cg (fun t => q0 ◇ t) (cg (fun t => t ◇ (((q0 ◇ (q0 ◇ q1)) ◇ (q0 ◇ q1)) ◇ (q0 ◇ q1))) (p10 q1 q0)))).trans (cg (fun t => q0 ◇ t) (p17 q0 (q0 ◇ q1)))).symm).trans (((p1h (q0 ◇ q1) (q0 ◇ q1) q0 q0 q0).symm).trans (p1f q0 q0 q0 q1 q0))
  have p1j : forall (q0 q1:G), (q1 ◇ ((q0 ◇ q1) ◇ (q1 ◇ (q0 ◇ q1)))) = ((q0 ◇ q1) ◇ q1):=by
    intro q0 q1
    exact ((((cg (fun t => q1 ◇ t) (cg (fun t => ((q0 ◇ q1) ◇ (q1 ◇ q1)) ◇ t) (cg (fun t => t ◇ (q0 ◇ q1)) (cg (fun t => t ◇ (q0 ◇ q1)) (p13 q0 q1))))).trans (cg (fun t => q1 ◇ t) (cg (fun t => t ◇ (((q1 ◇ (q0 ◇ q1)) ◇ (q0 ◇ q1)) ◇ (q0 ◇ q1))) (pp q0 q1)))).trans (cg (fun t => q1 ◇ t) (p17 q1 (q0 ◇ q1)))).symm).trans (((p1h (q0 ◇ q1) (q0 ◇ q1) q1 q0 q0).symm).trans (p1g q1 q1 q0 q1 q0))
  have p1k : forall (q0 q1 q2:G), ((q2 ◇ (((q2 ◇ q1) ◇ q0) ◇ q0)) ◇ q2) = ((q0 ◇ q2) ◇ q2):=by
    intro q0 q1 q2
    exact ((((cg (fun t => q2 ◇ t) (cg (fun t => (q0 ◇ q2) ◇ t) (p1e q0 q1 q2))).trans (p1j q0 q2)).symm).trans (((cg (fun t => q2 ◇ t) (cg (fun t => t ◇ (q2 ◇ (q2 ◇ (((q2 ◇ q1) ◇ q0) ◇ q0)))) ((h q0 q2 q1).symm))).symm).trans (p1i q2 (((q2 ◇ q1) ◇ q0) ◇ q0)))).symm
  have p1l : forall (q0 q1 q2:G), ((((q0 ◇ q2) ◇ q2) ◇ q2) ◇ (((q1 ◇ q2) ◇ q2) ◇ q2)) = (q2 ◇ q2):=by
    intro q0 q1 q2
    exact ((((((cg (fun t => (((q1 ◇ q2) ◇ q2) ◇ q2) ◇ t) (p13 ((q0 ◇ q2) ◇ q2) q2)).trans (cg (fun t => (((q1 ◇ q2) ◇ q2) ◇ q2) ◇ t) (p0 q0 q2 q2))).trans (pp ((q1 ◇ q2) ◇ q2) q2)).trans (p0 q1 q2 q2)).symm).trans (((cg (fun t => (((q1 ◇ q2) ◇ q2) ◇ q2) ◇ t) (cg (fun t => t ◇ (((q0 ◇ q2) ◇ q2) ◇ q2)) (pn q0 q2))).symm).trans (p4 q1 q2 q2 (((q0 ◇ q2) ◇ q2) ◇ q2)))).symm
  have p1m : forall (q0 q1 q2:G), ((((q1 ◇ q2) ◇ q2) ◇ q2) ◇ ((q0 ◇ q2) ◇ q2)) = (q2 ◇ ((q0 ◇ q2) ◇ q2)):=by
    intro q0 q1 q2
    exact (((((cg (fun t => ((q0 ◇ q2) ◇ q2) ◇ t) (p13 ((q1 ◇ q2) ◇ q2) q2)).trans (cg (fun t => ((q0 ◇ q2) ◇ q2) ◇ t) (p0 q1 q2 q2))).trans (pp (q0 ◇ q2) q2)).symm).trans (((cg (fun t => ((q0 ◇ q2) ◇ q2) ◇ t) (cg (fun t => t ◇ (((q1 ◇ q2) ◇ q2) ◇ q2)) (p1l q0 q1 q2))).symm).trans ((h (((q1 ◇ q2) ◇ q2) ◇ q2) ((q0 ◇ q2) ◇ q2) q2).symm))).symm
  have p1n : forall (q0 q1:G), (q1 ◇ (q0 ◇ (q0 ◇ ((q0 ◇ q0) ◇ q1)))) = ((q0 ◇ q0) ◇ q1):=by
    intro q0 q1
    exact ((cg (fun t => q1 ◇ t) (p10 ((q0 ◇ q0) ◇ q1) q0)).symm).trans (((cg (fun t => q1 ◇ t) (cg (fun t => t ◇ (q0 ◇ q0)) (p19 q1 q0))).symm).trans (p0 (q0 ◇ q0) (q0 ◇ q0) q1))
  have p1o : forall (q0 q2 q3 q1:G), ((((q0 ◇ q2) ◇ q2) ◇ q2) ◇ (((q0 ◇ q2) ◇ q3) ◇ q3)) = (q3 ◇ (((q0 ◇ q2) ◇ q2) ◇ q2)):=by
    intro q0 q2 q3 q1
    exact ((p6 q0 q1 q3 q2 (((q0 ◇ q2) ◇ q2) ◇ q2)).symm).trans ((((cg (fun t => t ◇ (((q2 ◇ (((q2 ◇ q1) ◇ q0) ◇ q0)) ◇ q3) ◇ q3)) (cg (fun t => t ◇ q2) (p1k q0 q1 q2))).symm).trans (p4 q2 q2 (((q2 ◇ q1) ◇ q0) ◇ q0) q3)).trans (cg (fun t => q3 ◇ t) (cg (fun t => t ◇ q2) (p1k q0 q1 q2))))
  have p1p : forall (q0 q1:G), ((((q0 ◇ q1) ◇ q1) ◇ q1) ◇ (q0 ◇ q1)) = (q1 ◇ (q0 ◇ q1)):=by
    intro q0 q1
    exact (((((cg (fun t => (q0 ◇ q1) ◇ t) (p1m (q0 ◇ q1) q0 q1)).trans (cg (fun t => (q0 ◇ q1) ◇ t) (p0 q0 q1 q1))).trans (pp q0 q1)).symm).trans (((cg (fun t => (q0 ◇ q1) ◇ t) (p1o q0 q1 (((q0 ◇ q1) ◇ q1) ◇ q1) q0)).symm).trans (pz (((q0 ◇ q1) ◇ q1) ◇ q1) (q0 ◇ q1)))).symm
  have p1q : forall (q0 q1:G), ((((q0 ◇ q1) ◇ q1) ◇ q1) ◇ ((q0 ◇ q1) ◇ (q0 ◇ q1))) = (q1 ◇ (q0 ◇ q1)):=by
    intro q0 q1
    exact (((cg (fun t => (((q0 ◇ q1) ◇ q1) ◇ q1) ◇ t) (pf (q0 ◇ q1))).symm).trans (p1o q0 q1 (q0 ◇ q1) q0)).trans (p17 q0 q1)
  have p1r : forall (q0 q1:G), ((q1 ◇ (q0 ◇ q1)) ◇ (q0 ◇ q1)) = ((q0 ◇ q1) ◇ (q1 ◇ (q0 ◇ q1))):=by
    intro q0 q1
    exact (((cg (fun t => t ◇ ((q0 ◇ q1) ◇ (q0 ◇ q1))) (cg (fun t => (q1 ◇ (q0 ◇ q1)) ◇ t) (p1q q0 q1))).trans (px q1 (q0 ◇ q1))).symm).trans ((((cg (fun t => t ◇ ((q0 ◇ q1) ◇ (q0 ◇ q1))) (cg (fun t => t ◇ ((((q0 ◇ q1) ◇ q1) ◇ q1) ◇ ((q0 ◇ q1) ◇ (q0 ◇ q1)))) (p1q q0 q1))).symm).trans (pr (((q0 ◇ q1) ◇ q1) ◇ q1) ((q0 ◇ q1) ◇ (q0 ◇ q1)) q0)).trans ((cg (fun t => t ◇ ((q0 ◇ q1) ◇ (q0 ◇ q1))) (p1q q0 q1)).trans (pp q1 (q0 ◇ q1))))
  have p1s : forall (q0 q1:G), ((q1 ◇ q1) ◇ ((q0 ◇ q1) ◇ (q1 ◇ (q0 ◇ q1)))) = ((q0 ◇ q1) ◇ q1):=by
    intro q0 q1
    exact ((((cg (fun t => t ◇ ((q1 ◇ (q0 ◇ q1)) ◇ ((q0 ◇ q1) ◇ (q0 ◇ q1)))) (cg (fun t => t ◇ q1) (po q0 q1))).trans (cg (fun t => t ◇ ((q1 ◇ (q0 ◇ q1)) ◇ ((q0 ◇ q1) ◇ (q0 ◇ q1)))) (pf q1))).trans (cg (fun t => (q1 ◇ q1) ◇ t) (pp q1 (q0 ◇ q1)))).symm).trans ((((cg (fun t => (((((q0 ◇ q1) ◇ q1) ◇ q1) ◇ q1) ◇ q1) ◇ t) (cg (fun t => t ◇ ((q0 ◇ q1) ◇ (q0 ◇ q1))) (p1q q0 q1))).symm).trans (p1o ((q0 ◇ q1) ◇ q1) q1 ((q0 ◇ q1) ◇ (q0 ◇ q1)) q0)).trans (((cg (fun t => ((q0 ◇ q1) ◇ (q0 ◇ q1)) ◇ t) (cg (fun t => t ◇ q1) (po q0 q1))).trans (cg (fun t => ((q0 ◇ q1) ◇ (q0 ◇ q1)) ◇ t) (pf q1))).trans (px q0 q1)))
  have p1t : forall (q0 q2 q3 q4 q1:G), ((q3 ◇ q3) ◇ (((((q0 ◇ q2) ◇ q3) ◇ q3) ◇ q4) ◇ q4)) = (q4 ◇ (q3 ◇ q3)):=by
    intro q0 q2 q3 q4 q1
    exact (((cg (fun t => (((((q0 ◇ q2) ◇ q3) ◇ q3) ◇ q3) ◇ q3) ◇ t) (cg (fun t => t ◇ q4) (p7 q0 q1 q3 q2 q4 ((((q2 ◇ (((q2 ◇ q1) ◇ q0) ◇ q0)) ◇ q3) ◇ q3) ◇ q4)))).trans (cg (fun t => t ◇ (((((q0 ◇ q2) ◇ q3) ◇ q3) ◇ q4) ◇ q4)) (po (q0 ◇ q2) q3))).symm).trans ((((cg (fun t => t ◇ (((((q2 ◇ (((q2 ◇ q1) ◇ q0) ◇ q0)) ◇ q3) ◇ q3) ◇ q4) ◇ q4)) (cg (fun t => t ◇ q3) (p7 q0 q1 q3 q2 q3 q0))).symm).trans (p1o ((q2 ◇ (((q2 ◇ q1) ◇ q0) ◇ q0)) ◇ q3) q3 q4 q0)).trans ((cg (fun t => q4 ◇ t) (cg (fun t => t ◇ q3) (p7 q0 q1 q3 q2 q3 ((((q2 ◇ (((q2 ◇ q1) ◇ q0) ◇ q0)) ◇ q3) ◇ q3) ◇ q3)))).trans (cg (fun t => q4 ◇ t) (po (q0 ◇ q2) q3))))
  have p1u : forall (q0 q1:G), ((q0 ◇ q1) ◇ q1) = (q1 ◇ (q0 ◇ q1)):=by
    intro q0 q1
    exact (((cg (fun t => (q1 ◇ q1) ◇ t) (p1r q0 q1)).trans (p1s q0 q1)).symm).trans ((((cg (fun t => (q1 ◇ q1) ◇ t) (cg (fun t => t ◇ (q0 ◇ q1)) (p1p q0 q1))).symm).trans (p1t q0 q1 q1 (q0 ◇ q1) q0)).trans (pp q0 q1))
  have p1v : forall (q0 q1:G), ((q0 ◇ q0) ◇ q1) = (q0 ◇ q1):=by
    intro q0 q1
    exact ((p1a q0 q1).symm).trans (((cg (fun t => q1 ◇ t) (cg (fun t => q0 ◇ t) (p1u q1 q0))).symm).trans (pz q0 q1))
  have p1w : forall (q0 q1:G), (q1 ◇ (q0 ◇ q0)) = (q1 ◇ q0):=by
    intro q0 q1
    exact ((((cg (fun t => q0 ◇ t) (cg (fun t => t ◇ q1) (cg (fun t => t ◇ q1) (p1v q0 q1)))).trans (p2 q1 q0 (q0 ◇ (((q0 ◇ q1) ◇ q1) ◇ q1)))).symm).trans (((p1v q0 ((((q0 ◇ q0) ◇ q1) ◇ q1) ◇ q1)).symm).trans (p2 q1 (q0 ◇ q0) q0))).symm
  have p1x : forall (q0 q1:G), (q1 ◇ ((q1 ◇ q0) ◇ q0)) = (q0 ◇ q1):=by
    intro q0 q1
    exact ((cg (fun t => q1 ◇ t) (cg (fun t => t ◇ q0) (p1v q1 q0))).symm).trans ((h q0 q1 q1).symm)
  have p1y : forall (q0 q1:G), (q1 ◇ (q0 ◇ (q0 ◇ (q0 ◇ q1)))) = (q0 ◇ q1):=by
    intro q0 q1
    exact ((cg (fun t => q1 ◇ t) (cg (fun t => q0 ◇ t) (cg (fun t => q0 ◇ t) (p1v q0 q1)))).symm).trans ((p1n q0 q1).trans (p1v q0 q1))
  have p1z : forall (q0 q1 q2:G), ((((q0 ◇ q1) ◇ q0) ◇ q0) ◇ q2) = (q0 ◇ q2):=by
    intro q0 q1 q2
    exact ((((cg (fun t => t ◇ q2) (p16 q1 q0)).trans (p1v q0 q2)).symm).trans (((cg (fun t => t ◇ q2) (p4 q0 q0 q1 q0)).symm).trans (p1v (((q0 ◇ q1) ◇ q0) ◇ q0) q2))).symm
  have p20 : forall (q0 q1 q2:G), ((((q0 ◇ q1) ◇ q1) ◇ q1) ◇ q2) = (q1 ◇ q2):=by
    intro q0 q1 q2
    exact ((((cg (fun t => t ◇ q2) (p0 q0 q1 q1)).trans (p1v q1 q2)).symm).trans (((cg (fun t => t ◇ q2) (p1m (q0 ◇ q1) q0 q1)).symm).trans (p1v (((q0 ◇ q1) ◇ q1) ◇ q1) q2))).symm
  have p21 : forall (q0 q1 q2:G), (q2 ◇ (((q0 ◇ q1) ◇ q0) ◇ q0)) = (q2 ◇ q0):=by
    intro q0 q1 q2
    exact ((((cg (fun t => q2 ◇ t) (p16 q1 q0)).trans (p1w q0 q2)).symm).trans (((cg (fun t => q2 ◇ t) (p4 q0 q0 q1 q0)).symm).trans (p1w (((q0 ◇ q1) ◇ q0) ◇ q0) q2))).symm
  have p22 : forall (q0 q1:G), (q1 ◇ q0) = (q0 ◇ q1):=by
    intro q0 q1
    exact ((p21 q0 q1 q1).symm).trans (p0 q0 q0 q1)
  have p23 : forall (q0 q1:G), (((q0 ◇ q1) ◇ q1) ◇ q1) = (q1 ◇ q1):=by
    intro q0 q1
    exact (((((((((cg (fun t => q1 ◇ t) (cg (fun t => ((q1 ◇ q0) ◇ q1) ◇ t) (cg (fun t => t ◇ q1) (cg (fun t => t ◇ q1) (p22 q0 q1))))).trans (cg (fun t => q1 ◇ t) (cg (fun t => t ◇ (((q0 ◇ q1) ◇ q1) ◇ q1)) (cg (fun t => t ◇ q1) (p22 q0 q1))))).trans (cg (fun t => q1 ◇ t) (p22 (((q0 ◇ q1) ◇ q1) ◇ q1) ((q0 ◇ q1) ◇ q1)))).trans (cg (fun t => q1 ◇ t) (p20 q0 q1 ((q0 ◇ q1) ◇ q1)))).trans (cg (fun t => q1 ◇ t) (p22 ((q0 ◇ q1) ◇ q1) q1))).trans (p22 (((q0 ◇ q1) ◇ q1) ◇ q1) q1)).trans (p20 q0 q1 q1)).symm).trans ((((cg (fun t => q1 ◇ t) (cg (fun t => ((q1 ◇ q0) ◇ q1) ◇ t) (p21 q1 q0 ((q1 ◇ q0) ◇ q1)))).symm).trans (p1y ((q1 ◇ q0) ◇ q1) q1)).trans (cg (fun t => t ◇ q1) (cg (fun t => t ◇ q1) (p22 q0 q1))))).symm
  have p24 : forall (q0 q1:G), (((q0 ◇ q1) ◇ q0) ◇ q1) = (q0 ◇ q1):=by
    intro q0 q1
    exact (((cg (fun t => q1 ◇ t) (cg (fun t => t ◇ q0) (p22 q0 q1))).trans (p22 ((q0 ◇ q1) ◇ q0) q1)).symm).trans (p1x q0 q1)
  have p25 : forall (q0 q1 q2:G), (((q0 ◇ q1) ◇ q1) ◇ q2) = (q1 ◇ q2):=by
    intro q0 q1 q2
    exact (((((((((cg (fun t => t ◇ q2) (cg (fun t => t ◇ ((q0 ◇ q1) ◇ q1)) (p1v q1 ((q0 ◇ q1) ◇ q1)))).trans (cg (fun t => t ◇ q2) (cg (fun t => t ◇ ((q0 ◇ q1) ◇ q1)) (p22 ((q0 ◇ q1) ◇ q1) q1)))).trans (cg (fun t => t ◇ q2) (cg (fun t => t ◇ ((q0 ◇ q1) ◇ q1)) (p23 q0 q1)))).trans (cg (fun t => t ◇ q2) (p1v q1 ((q0 ◇ q1) ◇ q1)))).trans (cg (fun t => t ◇ q2) (p22 ((q0 ◇ q1) ◇ q1) q1))).trans (cg (fun t => t ◇ q2) (p23 q0 q1))).trans (p1v q1 q2)).symm).trans (((cg (fun t => t ◇ q2) (cg (fun t => t ◇ ((q0 ◇ q1) ◇ q1)) (cg (fun t => t ◇ ((q0 ◇ q1) ◇ q1)) (p23 q0 q1)))).symm).trans (p1z ((q0 ◇ q1) ◇ q1) q1 q2))).symm
  have p26 : forall (q0 q1:G), ((q0 ◇ q1) ◇ q1) = (q1 ◇ q1):=by
    intro q0 q1
    exact ((((cg (fun t => t ◇ q1) (p22 (q0 ◇ q1) q1)).trans (p25 q0 q1 q1)).symm).trans (((cg (fun t => t ◇ q1) (p25 q0 q1 (q0 ◇ q1))).symm).trans (p24 (q0 ◇ q1) q1))).symm
  have p27 : forall (q0 q2 q1:G), ((q0 ◇ q2) ◇ q0) = (q0 ◇ q0):=by
    intro q0 q2 q1
    exact ((((((cg (fun t => (q0 ◇ q2) ◇ t) (cg (fun t => t ◇ q0) (cg (fun t => t ◇ q0) (p22 q1 q2)))).trans (cg (fun t => (q0 ◇ q2) ◇ t) (p26 (q1 ◇ q2) q0))).trans (p22 (q0 ◇ q0) (q0 ◇ q2))).trans (p1v q0 (q0 ◇ q2))).trans (p22 (q0 ◇ q2) q0)).symm).trans ((((cg (fun t => t ◇ (((q2 ◇ q1) ◇ q0) ◇ q0)) ((h q0 q2 q1).symm)).symm).trans (p26 q2 (((q2 ◇ q1) ◇ q0) ◇ q0))).trans (((((((cg (fun t => t ◇ (((q2 ◇ q1) ◇ q0) ◇ q0)) (cg (fun t => t ◇ q0) (cg (fun t => t ◇ q0) (p22 q1 q2)))).trans (cg (fun t => (((q1 ◇ q2) ◇ q0) ◇ q0) ◇ t) (cg (fun t => t ◇ q0) (cg (fun t => t ◇ q0) (p22 q1 q2))))).trans (cg (fun t => t ◇ (((q1 ◇ q2) ◇ q0) ◇ q0)) (p26 (q1 ◇ q2) q0))).trans (cg (fun t => (q0 ◇ q0) ◇ t) (p26 (q1 ◇ q2) q0))).trans (p1v q0 (q0 ◇ q0))).trans (p22 (q0 ◇ q0) q0)).trans (p1v q0 q0)))
  have p28 : forall (q0 q1:G), ((q0 ◇ q1) ◇ (q0 ◇ q1)) = (q1 ◇ q1):=by
    intro q0 q1
    exact (((((p1v q1 (q0 ◇ q1)).trans (p22 (q0 ◇ q1) q1)).trans (p26 q0 q1)).symm).trans (((cg (fun t => t ◇ (q0 ◇ q1)) (p26 q0 q1)).symm).trans (p27 (q0 ◇ q1) q1 q0))).symm
  have p29 : forall (q0 q1:G), (q0 ◇ q1) = (q0 ◇ q0):=by
    intro q0 q1
    exact (((((((cg (fun t => q0 ◇ t) (p1v q1 (q0 ◇ q1))).trans (cg (fun t => q0 ◇ t) (p22 (q0 ◇ q1) q1))).trans (cg (fun t => q0 ◇ t) (p26 q0 q1))).trans (p22 (q1 ◇ q1) q0)).trans (p1v q1 q0)).trans (p22 q0 q1)).symm).trans ((((cg (fun t => q0 ◇ t) (cg (fun t => t ◇ (q0 ◇ q1)) (p28 q0 q1))).symm).trans ((h (q0 ◇ q1) q0 q1).symm)).trans (p27 q0 q1 ((q0 ◇ q1) ◇ q0)))
  have p2a : forall (q0 q1:G), (q1 ◇ q0) = (q0 ◇ q0):=by
    intro q0 q1
    exact (p22 q0 q1).trans (p29 q0 q1)
  exact (p2a y x).trans ((p2a y z).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_45448_to_45 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_45448_to_45
