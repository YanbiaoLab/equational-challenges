-- Equation19010 → Equation31535
-- Recorded verdict: true
-- Premise: x = (y ◇ x) ◇ ((z ◇ x) ◇ (y ◇ z))
-- Conclusion: x = (y ◇ ((z ◇ x) ◇ (y ◇ z))) ◇ x
-- Original submission SHA-256: 74da52facc10f35ab341f2a345dc57b4d803c7a2a3cc74e666e453e2203ce5b4
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (y ◇ x) ◇ ((z ◇ x) ◇ (y ◇ z))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (y ◇ ((z ◇ x) ◇ (y ◇ z))) ◇ x
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have cg : ∀ (f:G → G) {a b:G}, a = b → f a = f b:=by
    intro f a b p
    exact congrArg f p
  have p0 : forall (x y z:G), ((y ◇ x) ◇ ((z ◇ x) ◇ (y ◇ z))) = ((x ◇ x) ◇ ((x ◇ x) ◇ (x ◇ x))):=by
    intro x y z
    exact ((h x y z).symm).trans (h x x x)
  have p1 : forall (q0:G), ((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) = q0:=by
    intro q0
    exact ((p0 q0 q0 q0).symm).trans ((h q0 q0 q0).symm)
  have p2 : forall (q0 q1 q2 q3:G), (q0 ◇ ((q3 ◇ ((q2 ◇ q0) ◇ (q1 ◇ q2))) ◇ ((q1 ◇ q0) ◇ q3))) = ((q2 ◇ q0) ◇ (q1 ◇ q2)):=by
    intro q0 q1 q2 q3
    exact ((cg (fun t => t ◇ ((q3 ◇ ((q2 ◇ q0) ◇ (q1 ◇ q2))) ◇ ((q1 ◇ q0) ◇ q3))) ((h q0 q1 q2).symm)).symm).trans ((h ((q2 ◇ q0) ◇ (q1 ◇ q2)) (q1 ◇ q0) q3).symm)
  have p3 : forall (q0 q1 q2:G), (q0 ◇ (q0 ◇ ((q1 ◇ q0) ◇ (q1 ◇ q0)))) = ((q2 ◇ q0) ◇ (q1 ◇ q2)):=by
    intro q0 q1 q2
    exact ((cg (fun t => q0 ◇ t) (cg (fun t => t ◇ ((q1 ◇ q0) ◇ (q1 ◇ q0))) ((h q0 q1 q2).symm))).symm).trans (p2 q0 q1 q2 (q1 ◇ q0))
  have p4 : forall (q0 q1 q2 q3:G), ((q3 ◇ q1) ◇ (q2 ◇ q3)) = ((q0 ◇ q1) ◇ (q2 ◇ q0)):=by
    intro q0 q1 q2 q3
    exact (((p3 q1 q2 q0).symm).trans (p3 q1 q2 q3)).symm
  have p5 : forall (q0 q1 q2:G), ((q2 ◇ q0) ◇ (q1 ◇ q2)) = ((q0 ◇ q0) ◇ (q1 ◇ q0)):=by
    intro q0 q1 q2
    exact ((p3 q0 q1 q2).symm).trans (p3 q0 q1 q0)
  have p6 : forall (q0 q1:G), ((q1 ◇ q0) ◇ ((q0 ◇ q0) ◇ (q1 ◇ q0))) = q0:=by
    intro q0 q1
    exact ((cg (fun t => (q1 ◇ q0) ◇ t) (p5 q0 q1 q0)).symm).trans ((h q0 q1 q0).symm)
  have p7 : forall (q0 q1 q3 q2:G), ((q3 ◇ ((q0 ◇ q0) ◇ (q1 ◇ q0))) ◇ (q0 ◇ (q3 ◇ (q1 ◇ q0)))) = ((q0 ◇ q0) ◇ (q1 ◇ q0)):=by
    intro q0 q1 q3 q2
    exact ((cg (fun t => t ◇ (q0 ◇ (q3 ◇ (q1 ◇ q0)))) (cg (fun t => q3 ◇ t) (p5 q0 q1 q2))).symm).trans ((((cg (fun t => (q3 ◇ ((q2 ◇ q0) ◇ (q1 ◇ q2))) ◇ t) (cg (fun t => t ◇ (q3 ◇ (q1 ◇ q0))) ((h q0 q1 q2).symm))).symm).trans ((h ((q2 ◇ q0) ◇ (q1 ◇ q2)) q3 (q1 ◇ q0)).symm)).trans (p5 q0 q1 q2))
  have p8 : forall (q0 q1 q2:G), (q0 ◇ (q0 ◇ ((q1 ◇ q0) ◇ (q1 ◇ q0)))) = ((q0 ◇ q0) ◇ (q1 ◇ q0)):=by
    intro q0 q1 q2
    exact (p3 q0 q1 q2).trans (p5 q0 q1 q2)
  have p9 : forall (q0 q1 q2:G), ((((q0 ◇ q0) ◇ (q0 ◇ q0)) ◇ q2) ◇ q0) = ((q1 ◇ q2) ◇ ((q0 ◇ q0) ◇ q1)):=by
    intro q0 q1 q2
    exact ((cg (fun t => (((q0 ◇ q0) ◇ (q0 ◇ q0)) ◇ q2) ◇ t) (p1 q0)).symm).trans (p4 q1 q2 (q0 ◇ q0) ((q0 ◇ q0) ◇ (q0 ◇ q0)))
  have pa : forall (q0 q1 q3 q2:G), (((q1 ◇ q0) ◇ q3) ◇ ((((q0 ◇ q0) ◇ (q1 ◇ q0)) ◇ q3) ◇ q0)) = q3:=by
    intro q0 q1 q3 q2
    exact ((cg (fun t => ((q1 ◇ q0) ◇ q3) ◇ t) (cg (fun t => t ◇ q0) (cg (fun t => t ◇ q3) (p5 q0 q1 q2)))).symm).trans (((cg (fun t => ((q1 ◇ q0) ◇ q3) ◇ t) (cg (fun t => (((q2 ◇ q0) ◇ (q1 ◇ q2)) ◇ q3) ◇ t) ((h q0 q1 q2).symm))).symm).trans ((h q3 (q1 ◇ q0) ((q2 ◇ q0) ◇ (q1 ◇ q2))).symm))
  have pb : forall (q0 q1:G), ((((q0 ◇ q0) ◇ (q0 ◇ q0)) ◇ q1) ◇ q0) = ((q1 ◇ q1) ◇ ((q0 ◇ q0) ◇ q1)):=by
    intro q0 q1
    exact ((cg (fun t => (((q0 ◇ q0) ◇ (q0 ◇ q0)) ◇ q1) ◇ t) (p1 q0)).symm).trans (p5 q1 (q0 ◇ q0) ((q0 ◇ q0) ◇ (q0 ◇ q0)))
  have pc : forall (q0 q1:G), ((q1 ◇ q1) ◇ ((q0 ◇ q1) ◇ (q1 ◇ q0))) = q1:=by
    intro q0 q1
    exact ((cg (fun t => (q1 ◇ q1) ◇ t) (p4 q0 q1 q1 q1)).symm).trans (p1 q1)
  have pd : forall (q0 q1 q2:G), ((q1 ◇ q2) ◇ ((q0 ◇ q0) ◇ q1)) = ((q0 ◇ q2) ◇ ((q0 ◇ q0) ◇ q0)):=by
    intro q0 q1 q2
    exact ((p9 q0 q1 q2).symm).trans (p9 q0 q0 q2)
  have pe : forall (q0 q1:G), ((((q0 ◇ q0) ◇ (q0 ◇ q0)) ◇ q1) ◇ q0) = ((q0 ◇ q1) ◇ ((q0 ◇ q0) ◇ q0)):=by
    intro q0 q1
    exact (pb q0 q1).trans (pd q0 q1 q1)
  have pf : forall (q0 q1 q2:G), ((q1 ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) ◇ (q2 ◇ q1)) = (q0 ◇ (q2 ◇ (q0 ◇ q0))):=by
    intro q0 q1 q2
    exact (((cg (fun t => t ◇ (q2 ◇ (q0 ◇ q0))) (p1 q0)).symm).trans (p4 q1 ((q0 ◇ q0) ◇ (q0 ◇ q0)) q2 (q0 ◇ q0))).symm
  have pg : forall (q0 q1 q3 q4 q2:G), ((((q0 ◇ q0) ◇ (q1 ◇ q0)) ◇ q4) ◇ q0) = ((q3 ◇ q4) ◇ ((q1 ◇ q0) ◇ q3)):=by
    intro q0 q1 q3 q4 q2
    exact ((cg (fun t => t ◇ q0) (cg (fun t => t ◇ q4) (p5 q0 q1 q2))).symm).trans (((cg (fun t => (((q2 ◇ q0) ◇ (q1 ◇ q2)) ◇ q4) ◇ t) ((h q0 q1 q2).symm)).symm).trans (p4 q3 q4 (q1 ◇ q0) ((q2 ◇ q0) ◇ (q1 ◇ q2))))
  have ph : forall (q0 q1 q2 q3 q4:G), ((q3 ◇ q4) ◇ ((q2 ◇ q1) ◇ q3)) = ((q0 ◇ q4) ◇ ((q2 ◇ q1) ◇ q0)):=by
    intro q0 q1 q2 q3 q4
    exact (((pg q1 q2 q0 q4 q0).symm).trans (pg q1 q2 q3 q4 q0)).symm
  have pi : forall (q0 q1 q3 q4 q2:G), ((q3 ◇ q4) ◇ ((q1 ◇ q0) ◇ q3)) = ((q0 ◇ q4) ◇ ((q1 ◇ q0) ◇ q0)):=by
    intro q0 q1 q3 q4 q2
    exact ((pg q0 q1 q3 q4 q2).symm).trans (pg q0 q1 q0 q4 q2)
  have pj : forall (q1 q0:G), ((q1 ◇ q1) ◇ (((q1 ◇ q1) ◇ (q1 ◇ q1)) ◇ q1)) = (q1 ◇ (q1 ◇ (q1 ◇ q1))):=by
    intro q1 q0
    exact ((((cg (fun t => t ◇ (q1 ◇ q1)) (pf q1 q0 (q1 ◇ q1))).trans (pf q1 q1 q1)).symm).trans ((((cg (fun t => t ◇ (q1 ◇ q1)) (pg q1 q1 q0 ((q1 ◇ q1) ◇ (q1 ◇ q1)) q0)).symm).trans (pe (q1 ◇ q1) q1)).trans (p5 q1 ((q1 ◇ q1) ◇ (q1 ◇ q1)) (q1 ◇ q1)))).symm
  have pk : forall (q0 q1:G), (((q0 ◇ (q0 ◇ q0)) ◇ ((q0 ◇ q0) ◇ q0)) ◇ (q1 ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0)))) = (q0 ◇ (q1 ◇ (q0 ◇ q0))):=by
    intro q0 q1
    exact ((((cg (fun t => t ◇ (q1 ◇ (q0 ◇ q0))) (p1 q0)).symm).trans (p5 ((q0 ◇ q0) ◇ (q0 ◇ q0)) q1 (q0 ◇ q0))).trans (cg (fun t => t ◇ (q1 ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0)))) (pi q0 q0 (q0 ◇ q0) (q0 ◇ q0) (((q0 ◇ q0) ◇ (q0 ◇ q0)) ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0)))))).symm
  have pl : forall (q0 q1 q3 q2:G), ((((q0 ◇ q0) ◇ (q1 ◇ q0)) ◇ q3) ◇ q0) = ((q0 ◇ q3) ◇ ((q1 ◇ q0) ◇ q0)):=by
    intro q0 q1 q3 q2
    exact ((cg (fun t => t ◇ q0) (cg (fun t => t ◇ q3) (p5 q0 q1 q2))).symm).trans ((((cg (fun t => (((q2 ◇ q0) ◇ (q1 ◇ q2)) ◇ q3) ◇ t) ((h q0 q1 q2).symm)).symm).trans (p5 q3 (q1 ◇ q0) ((q2 ◇ q0) ◇ (q1 ◇ q2)))).trans (pi q0 q1 q3 q3 ((q3 ◇ q3) ◇ ((q1 ◇ q0) ◇ q3))))
  have pm : forall (q0 q1 q3 q2:G), (((q1 ◇ q0) ◇ q3) ◇ ((q0 ◇ q3) ◇ ((q1 ◇ q0) ◇ q0))) = q3:=by
    intro q0 q1 q3 q2
    exact ((((cg (fun t => ((q1 ◇ q0) ◇ q3) ◇ t) (cg (fun t => t ◇ ((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0)))) (cg (fun t => t ◇ q3) (p5 q0 q1 q2)))).trans (cg (fun t => ((q1 ◇ q0) ◇ q3) ◇ t) (cg (fun t => (((q0 ◇ q0) ◇ (q1 ◇ q0)) ◇ q3) ◇ t) (p6 q0 q0)))).trans (cg (fun t => ((q1 ◇ q0) ◇ q3) ◇ t) (pl q0 q1 q3 ((((q0 ◇ q0) ◇ (q1 ◇ q0)) ◇ q3) ◇ q0)))).symm).trans (((cg (fun t => ((q1 ◇ q0) ◇ q3) ◇ t) (cg (fun t => (((q2 ◇ q0) ◇ (q1 ◇ q2)) ◇ q3) ◇ t) (p0 q0 q1 q2))).symm).trans ((h q3 (q1 ◇ q0) ((q2 ◇ q0) ◇ (q1 ◇ q2))).symm))
  have pn : forall (q0 q1:G), (((q0 ◇ q0) ◇ (q0 ◇ q0)) ◇ (((q0 ◇ q0) ◇ (q0 ◇ q0)) ◇ (q0 ◇ q0))) = (q0 ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))):=by
    intro q0 q1
    exact ((cg (fun t => ((q0 ◇ q0) ◇ (q0 ◇ q0)) ◇ t) (cg (fun t => ((q0 ◇ q0) ◇ (q0 ◇ q0)) ◇ t) (cg (fun t => q0 ◇ t) (p6 q0 q0)))).symm).trans ((((cg (fun t => ((q0 ◇ q0) ◇ (q0 ◇ q0)) ◇ t) (cg (fun t => ((q0 ◇ q0) ◇ (q0 ◇ q0)) ◇ t) (cg (fun t => t ◇ ((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0)))) (p1 q0)))).symm).trans (p3 ((q0 ◇ q0) ◇ (q0 ◇ q0)) (q0 ◇ q0) q1)).trans (pf q0 q1 (q0 ◇ q0)))
  have po : forall (q0:G), (((q0 ◇ q0) ◇ (q0 ◇ q0)) ◇ (q0 ◇ (q0 ◇ q0))) = (q0 ◇ q0):=by
    intro q0
    exact ((p5 (q0 ◇ q0) q0 ((q0 ◇ q0) ◇ (q0 ◇ q0))).symm).trans (((cg (fun t => (((q0 ◇ q0) ◇ (q0 ◇ q0)) ◇ (q0 ◇ q0)) ◇ t) (pn q0 q0)).symm).trans ((h (q0 ◇ q0) ((q0 ◇ q0) ◇ (q0 ◇ q0)) (q0 ◇ q0)).symm))
  have pp : forall (q0:G), ((q0 ◇ (q0 ◇ q0)) ◇ (q0 ◇ q0)) = (q0 ◇ q0):=by
    intro q0
    exact ((cg (fun t => (q0 ◇ (q0 ◇ q0)) ◇ t) (po q0)).symm).trans ((h (q0 ◇ q0) q0 (q0 ◇ q0)).symm)
  have pq : forall (q0:G), (q0 ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) = ((q0 ◇ q0) ◇ (q0 ◇ q0)):=by
    intro q0
    exact (((po (q0 ◇ q0)).symm).trans (pf q0 ((q0 ◇ q0) ◇ (q0 ◇ q0)) (q0 ◇ q0))).symm
  have pr : forall (q0:G), (((q0 ◇ q0) ◇ (q0 ◇ q0)) ◇ (q0 ◇ q0)) = ((q0 ◇ q0) ◇ q0):=by
    intro q0
    exact ((((cg (fun t => (q0 ◇ q0) ◇ t) (cg (fun t => (q0 ◇ q0) ◇ t) (cg (fun t => (q0 ◇ q0) ◇ t) (pp q0)))).trans (cg (fun t => (q0 ◇ q0) ◇ t) (p6 q0 q0))).symm).trans ((((cg (fun t => (q0 ◇ q0) ◇ t) (cg (fun t => (q0 ◇ q0) ◇ t) (cg (fun t => t ◇ ((q0 ◇ (q0 ◇ q0)) ◇ (q0 ◇ q0))) (pp q0)))).symm).trans (p8 (q0 ◇ q0) (q0 ◇ (q0 ◇ q0)) q0)).trans (cg (fun t => ((q0 ◇ q0) ◇ (q0 ◇ q0)) ◇ t) (pp q0)))).symm
  have ps : forall (q0:G), ((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ q0)) = (q0 ◇ q0):=by
    intro q0
    exact ((((cg (fun t => t ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) (cg (fun t => ((q0 ◇ q0) ◇ (q0 ◇ q0)) ◇ t) (po q0))).trans (cg (fun t => t ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) (pr q0))).trans (p5 q0 (q0 ◇ q0) (q0 ◇ q0))).symm).trans ((((cg (fun t => (((q0 ◇ q0) ◇ (q0 ◇ q0)) ◇ (((q0 ◇ q0) ◇ (q0 ◇ q0)) ◇ (q0 ◇ (q0 ◇ q0)))) ◇ t) (cg (fun t => (q0 ◇ q0) ◇ t) (po q0))).symm).trans (p7 (q0 ◇ q0) q0 ((q0 ◇ q0) ◇ (q0 ◇ q0)) q0)).trans (po q0))
  have pt : forall (q0:G), (((q0 ◇ q0) ◇ q0) ◇ (q0 ◇ q0)) = q0:=by
    intro q0
    exact ((cg (fun t => ((q0 ◇ q0) ◇ q0) ◇ t) (ps q0)).symm).trans ((h q0 (q0 ◇ q0) q0).symm)
  have pu : forall (q0:G), (((q0 ◇ q0) ◇ (q0 ◇ q0)) ◇ q0) = q0:=by
    intro q0
    exact ((((cg (fun t => (q0 ◇ q0) ◇ t) (cg (fun t => (q0 ◇ q0) ◇ t) (cg (fun t => q0 ◇ t) (pt q0)))).trans (p6 q0 q0)).symm).trans ((((cg (fun t => (q0 ◇ q0) ◇ t) (cg (fun t => (q0 ◇ q0) ◇ t) (cg (fun t => t ◇ (((q0 ◇ q0) ◇ q0) ◇ (q0 ◇ q0))) (pt q0)))).symm).trans (p8 (q0 ◇ q0) ((q0 ◇ q0) ◇ q0) q0)).trans (cg (fun t => ((q0 ◇ q0) ◇ (q0 ◇ q0)) ◇ t) (pt q0)))).symm
  have pv : forall (q0 q1:G), (q0 ◇ ((q0 ◇ q0) ◇ q0)) = q0:=by
    intro q0 q1
    exact (((cg (fun t => q0 ◇ t) (p5 q0 ((q0 ◇ q0) ◇ (q0 ◇ q0)) q1)).trans (cg (fun t => q0 ◇ t) (cg (fun t => (q0 ◇ q0) ◇ t) (pu q0)))).symm).trans (((cg (fun t => t ◇ ((q1 ◇ q0) ◇ (((q0 ◇ q0) ◇ (q0 ◇ q0)) ◇ q1))) (pu q0)).symm).trans ((h q0 ((q0 ◇ q0) ◇ (q0 ◇ q0)) q1).symm))
  have pw : forall (q1 q0:G), ((q1 ◇ q1) ◇ q1) = (q1 ◇ (q1 ◇ (q1 ◇ q1))):=by
    intro q1 q0
    exact ((cg (fun t => (q1 ◇ q1) ◇ t) (pu q1)).symm).trans (pj q1 q0)
  have px : forall (q0 q1 q2:G), ((q1 ◇ q2) ◇ (q0 ◇ q1)) = ((q0 ◇ q2) ◇ (q0 ◇ q0)):=by
    intro q0 q1 q2
    exact (((cg (fun t => (q1 ◇ q2) ◇ t) (cg (fun t => t ◇ q1) (pu q0))).symm).trans (pi q0 ((q0 ◇ q0) ◇ (q0 ◇ q0)) q1 q2 q0)).trans (cg (fun t => (q0 ◇ q2) ◇ t) (cg (fun t => t ◇ q0) (pu q0)))
  have py : forall (q0 q1 q2:G), ((q1 ◇ q0) ◇ (q1 ◇ q1)) = ((q0 ◇ q0) ◇ (q1 ◇ q0)):=by
    intro q0 q1 q2
    exact ((px q1 q2 q0).symm).trans (p5 q0 q1 q2)
  have pz : forall (q0 q1:G), ((q0 ◇ q1) ◇ ((q0 ◇ q1) ◇ (q0 ◇ q0))) = q1:=by
    intro q0 q1
    exact ((cg (fun t => (q0 ◇ q1) ◇ t) (cg (fun t => (q0 ◇ q1) ◇ t) (cg (fun t => t ◇ q0) (pu q0)))).symm).trans (((cg (fun t => t ◇ ((q0 ◇ q1) ◇ ((((q0 ◇ q0) ◇ (q0 ◇ q0)) ◇ q0) ◇ q0))) (cg (fun t => t ◇ q1) (pu q0))).symm).trans (pm q0 ((q0 ◇ q0) ◇ (q0 ◇ q0)) q1 q0))
  have p10 : forall (q0 q1:G), ((q1 ◇ q1) ◇ (q1 ◇ q1)) = ((q0 ◇ q1) ◇ (q1 ◇ q0)):=by
    intro q0 q1
    exact ((((cg (fun t => q1 ◇ t) (cg (fun t => t ◇ ((q1 ◇ q1) ◇ (q1 ◇ q1))) (pc q0 q1))).trans (cg (fun t => q1 ◇ t) (pq q1))).trans (pq q1)).symm).trans (((cg (fun t => t ◇ (((q1 ◇ q1) ◇ ((q0 ◇ q1) ◇ (q1 ◇ q0))) ◇ ((q1 ◇ q1) ◇ (q1 ◇ q1)))) (pc q0 q1)).symm).trans (pz (q1 ◇ q1) ((q0 ◇ q1) ◇ (q1 ◇ q0))))
  have p11 : forall (q0 q1:G), ((q0 ◇ (q0 ◇ (q0 ◇ q0))) ◇ (q0 ◇ q0)) = q0:=by
    intro q0 q1
    exact (((cg (fun t => (q0 ◇ (q0 ◇ (q0 ◇ q0))) ◇ t) (pi q0 q0 q1 q0 ((q1 ◇ q0) ◇ ((q0 ◇ q0) ◇ q1)))).trans (cg (fun t => (q0 ◇ (q0 ◇ (q0 ◇ q0))) ◇ t) (ps q0))).symm).trans (((cg (fun t => t ◇ ((q1 ◇ q0) ◇ ((q0 ◇ q0) ◇ q1))) (pw q0 q0)).symm).trans ((h q0 (q0 ◇ q0) q1).symm))
  have p12 : forall (q0:G), (q0 ◇ (q0 ◇ (q0 ◇ (q0 ◇ q0)))) = q0:=by
    intro q0
    exact ((cg (fun t => q0 ◇ t) (pw q0 q0)).symm).trans (pv q0 q0)
  have p13 : forall (q0 q1:G), (((q0 ◇ q1) ◇ (q1 ◇ q0)) ◇ q1) = q1:=by
    intro q0 q1
    exact ((cg (fun t => t ◇ q1) (p10 q0 q1)).symm).trans (pu q1)
  have p14 : forall (q0 q1:G), (((q0 ◇ q0) ◇ q1) ◇ ((q0 ◇ q0) ◇ q0)) = ((q0 ◇ q1) ◇ q0):=by
    intro q0 q1
    exact ((((cg (fun t => (q0 ◇ q1) ◇ t) (pu q0)).symm).trans (pi (q0 ◇ q0) (q0 ◇ q0) q0 q1 q0)).trans (cg (fun t => ((q0 ◇ q0) ◇ q1) ◇ t) (pr q0))).symm
  have p15 : forall (q0 q1:G), (((q0 ◇ q0) ◇ (q0 ◇ q0)) ◇ (q1 ◇ q0)) = (q0 ◇ (q1 ◇ (q0 ◇ q0))):=by
    intro q0 q1
    exact ((cg (fun t => ((q0 ◇ q0) ◇ (q0 ◇ q0)) ◇ t) (cg (fun t => q1 ◇ t) (p6 q0 q0))).symm).trans (((cg (fun t => t ◇ (q1 ◇ ((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))))) (pp (q0 ◇ q0))).symm).trans (pf q0 ((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) q1))
  have p16 : forall (q0 q1:G), (q0 ◇ (q1 ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0)))) = ((q0 ◇ q0) ◇ (q1 ◇ q0)):=by
    intro q0 q1
    exact ((cg (fun t => t ◇ (q1 ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0)))) (pu q0)).symm).trans (p5 q0 q1 ((q0 ◇ q0) ◇ (q0 ◇ q0)))
  have p17 : forall (q0 q1:G), ((((q0 ◇ q0) ◇ q0) ◇ q1) ◇ q0) = ((q0 ◇ q1) ◇ (q0 ◇ q0)):=by
    intro q0 q1
    exact (((cg (fun t => t ◇ q0) (cg (fun t => t ◇ q1) (cg (fun t => (q0 ◇ q0) ◇ t) (pu q0)))).symm).trans (pl q0 ((q0 ◇ q0) ◇ (q0 ◇ q0)) q1 q0)).trans (cg (fun t => (q0 ◇ q1) ◇ t) (cg (fun t => t ◇ q0) (p13 q0 q0)))
  have p18 : forall (q0:G), (((q0 ◇ q0) ◇ q0) ◇ q0) = (q0 ◇ (q0 ◇ q0)):=by
    intro q0
    exact (((cg (fun t => t ◇ q0) (pv ((q0 ◇ q0) ◇ q0) q0)).symm).trans (p17 q0 ((((q0 ◇ q0) ◇ q0) ◇ ((q0 ◇ q0) ◇ q0)) ◇ ((q0 ◇ q0) ◇ q0)))).trans (((cg (fun t => t ◇ (q0 ◇ q0)) (cg (fun t => q0 ◇ t) (cg (fun t => t ◇ ((q0 ◇ q0) ◇ q0)) (p14 q0 q0)))).trans (cg (fun t => t ◇ (q0 ◇ q0)) (cg (fun t => q0 ◇ t) (p14 q0 q0)))).trans (cg (fun t => t ◇ (q0 ◇ q0)) (pv q0 (q0 ◇ ((q0 ◇ q0) ◇ q0)))))
  have p19 : forall (q0 q1:G), ((q0 ◇ (q0 ◇ q0)) ◇ ((q0 ◇ q0) ◇ (q0 ◇ (q0 ◇ q0)))) = q0:=by
    intro q0 q1
    exact (((cg (fun t => (q0 ◇ (q0 ◇ q0)) ◇ t) (pi q0 (q0 ◇ q0) q1 q0 ((q1 ◇ q0) ◇ (((q0 ◇ q0) ◇ q0) ◇ q1)))).trans (cg (fun t => (q0 ◇ (q0 ◇ q0)) ◇ t) (cg (fun t => (q0 ◇ q0) ◇ t) (p18 q0)))).symm).trans (((cg (fun t => t ◇ ((q1 ◇ q0) ◇ (((q0 ◇ q0) ◇ q0) ◇ q1))) (p18 q0)).symm).trans ((h q0 ((q0 ◇ q0) ◇ q0) q1).symm))
  have p1a : forall (q0:G), ((q0 ◇ q0) ◇ (q0 ◇ (q0 ◇ q0))) = (q0 ◇ (q0 ◇ q0)):=by
    intro q0
    exact (((cg (fun t => t ◇ (q0 ◇ (q0 ◇ q0))) (cg (fun t => t ◇ q0) (px q0 (q0 ◇ q0) (q0 ◇ (q0 ◇ q0))))).trans (cg (fun t => t ◇ (q0 ◇ (q0 ◇ q0))) (cg (fun t => t ◇ q0) (p11 q0 ((q0 ◇ (q0 ◇ (q0 ◇ q0))) ◇ (q0 ◇ q0)))))).symm).trans (((cg (fun t => t ◇ (q0 ◇ (q0 ◇ q0))) (cg (fun t => (((q0 ◇ q0) ◇ (q0 ◇ (q0 ◇ q0))) ◇ (q0 ◇ (q0 ◇ q0))) ◇ t) (p19 q0 q0))).symm).trans (p13 ((q0 ◇ q0) ◇ (q0 ◇ (q0 ◇ q0))) (q0 ◇ (q0 ◇ q0))))
  have p1b : forall (q0 q1:G), ((q1 ◇ (q0 ◇ q0)) ◇ (q1 ◇ q1)) = ((q0 ◇ q0) ◇ (q1 ◇ (q0 ◇ (q0 ◇ q0)))):=by
    intro q0 q1
    exact ((((cg (fun t => t ◇ (q1 ◇ (q0 ◇ (q0 ◇ q0)))) (pp q0)).symm).trans (p5 (q0 ◇ q0) q1 (q0 ◇ (q0 ◇ q0)))).trans (px q1 (q0 ◇ q0) (q0 ◇ q0))).symm
  have p1c : forall (q0 q1:G), ((q0 ◇ (q1 ◇ q1)) ◇ ((q1 ◇ q1) ◇ q0)) = (q1 ◇ (q1 ◇ q1)):=by
    intro q0 q1
    exact (((p10 q0 (q1 ◇ q1)).symm).trans (p1b q1 (q1 ◇ q1))).trans ((cg (fun t => (q1 ◇ q1) ◇ t) (p1a q1)).trans (p1a q1))
  have p1d : forall (q0 q1:G), (((q0 ◇ (q1 ◇ q0)) ◇ q0) ◇ q0) = (q0 ◇ ((q1 ◇ q0) ◇ q0)):=by
    intro q0 q1
    exact (((cg (fun t => t ◇ q0) (p14 q0 (q1 ◇ q0))).symm).trans (pl q0 q1 ((q0 ◇ q0) ◇ q0) q0)).trans (cg (fun t => t ◇ ((q1 ◇ q0) ◇ q0)) (pv q0 (q0 ◇ ((q0 ◇ q0) ◇ q0))))
  have p1e : forall (q0 q1:G), ((q0 ◇ q0) ◇ (q1 ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0)))) = ((q0 ◇ (q0 ◇ q0)) ◇ (q1 ◇ (q0 ◇ q0))):=by
    intro q0 q1
    exact ((((cg (fun t => t ◇ (q1 ◇ (q0 ◇ q0))) (cg (fun t => (q0 ◇ q0) ◇ t) (p1a q0))).trans (cg (fun t => t ◇ (q1 ◇ (q0 ◇ q0))) (p1a q0))).symm).trans (((cg (fun t => t ◇ (q1 ◇ (q0 ◇ q0))) (p1b q0 (q0 ◇ q0))).symm).trans (p15 (q0 ◇ q0) q1))).symm
  have p1f : forall (q0 q1:G), ((q0 ◇ (q0 ◇ q0)) ◇ (q1 ◇ (q0 ◇ q0))) = (q0 ◇ (q1 ◇ (q0 ◇ (q0 ◇ q0)))):=by
    intro q0 q1
    exact (((((((cg (fun t => (((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) ◇ (((q0 ◇ q0) ◇ (q0 ◇ q0)) ◇ (q0 ◇ q0))) ◇ t) (cg (fun t => q1 ◇ t) (cg (fun t => (q0 ◇ q0) ◇ t) (p1a q0)))).trans (cg (fun t => (((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) ◇ (((q0 ◇ q0) ◇ (q0 ◇ q0)) ◇ (q0 ◇ q0))) ◇ t) (cg (fun t => q1 ◇ t) (p1a q0)))).trans (cg (fun t => t ◇ (q1 ◇ (q0 ◇ (q0 ◇ q0)))) (cg (fun t => ((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) ◇ t) (p15 q0 q0)))).trans (cg (fun t => t ◇ (q1 ◇ (q0 ◇ (q0 ◇ q0)))) (cg (fun t => t ◇ (q0 ◇ (q0 ◇ (q0 ◇ q0)))) (p6 q0 q0)))).trans (cg (fun t => t ◇ (q1 ◇ (q0 ◇ (q0 ◇ q0)))) (p12 q0))).symm).trans ((((cg (fun t => (((q0 ◇ q0) ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) ◇ (((q0 ◇ q0) ◇ (q0 ◇ q0)) ◇ (q0 ◇ q0))) ◇ t) (cg (fun t => q1 ◇ t) (p1b q0 (q0 ◇ q0)))).symm).trans (pk (q0 ◇ q0) q1)).trans (p1e q0 q1))).symm
  have p1g : forall (q0 q1:G), ((q0 ◇ q0) ◇ (q1 ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0)))) = (q0 ◇ (q1 ◇ (q0 ◇ (q0 ◇ q0)))):=by
    intro q0 q1
    exact (p1e q0 q1).trans (p1f q0 q1)
  have p1h : forall (q0 q1:G), (q0 ◇ (q1 ◇ (q0 ◇ (q0 ◇ q0)))) = (((q0 ◇ q0) ◇ q0) ◇ (q1 ◇ q0)):=by
    intro q0 q1
    exact (((cg (fun t => t ◇ (q1 ◇ q0)) (cg (fun t => (q0 ◇ q0) ◇ t) (p13 q0 q0))).symm).trans ((((cg (fun t => t ◇ (q1 ◇ q0)) (p16 q0 ((q0 ◇ q0) ◇ (q0 ◇ q0)))).symm).trans (pf (q0 ◇ q0) q0 q1)).trans (p1g q0 q1))).symm
  have p1i : forall (q0 q1:G), ((q1 ◇ (q0 ◇ q0)) ◇ (q1 ◇ q1)) = ((q0 ◇ (q0 ◇ q0)) ◇ (q1 ◇ q0)):=by
    intro q0 q1
    exact (((((((cg (fun t => (((q0 ◇ q0) ◇ (q0 ◇ q0)) ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) ◇ t) (cg (fun t => q1 ◇ t) (cg (fun t => q0 ◇ t) (p15 q0 q0)))).trans (cg (fun t => (((q0 ◇ q0) ◇ (q0 ◇ q0)) ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) ◇ t) (cg (fun t => q1 ◇ t) (p1h q0 q0)))).trans (cg (fun t => (((q0 ◇ q0) ◇ (q0 ◇ q0)) ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) ◇ t) (cg (fun t => q1 ◇ t) (pt q0)))).trans (cg (fun t => t ◇ (q1 ◇ q0)) (pi q0 q0 (q0 ◇ q0) (q0 ◇ q0) (((q0 ◇ q0) ◇ (q0 ◇ q0)) ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0)))))).trans (cg (fun t => t ◇ (q1 ◇ q0)) (p1c q0 q0))).symm).trans ((((cg (fun t => (((q0 ◇ q0) ◇ (q0 ◇ q0)) ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))) ◇ t) (cg (fun t => q1 ◇ t) (pf q0 ((q0 ◇ q0) ◇ (q0 ◇ q0)) ((q0 ◇ q0) ◇ (q0 ◇ q0))))).symm).trans (p1g ((q0 ◇ q0) ◇ (q0 ◇ q0)) q1)).trans (((((cg (fun t => ((q0 ◇ q0) ◇ (q0 ◇ q0)) ◇ t) (cg (fun t => q1 ◇ t) (cg (fun t => ((q0 ◇ q0) ◇ (q0 ◇ q0)) ◇ t) (pi q0 q0 (q0 ◇ q0) (q0 ◇ q0) (((q0 ◇ q0) ◇ (q0 ◇ q0)) ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))))))).trans (cg (fun t => ((q0 ◇ q0) ◇ (q0 ◇ q0)) ◇ t) (cg (fun t => q1 ◇ t) (cg (fun t => ((q0 ◇ q0) ◇ (q0 ◇ q0)) ◇ t) (p1c q0 q0))))).trans (cg (fun t => ((q0 ◇ q0) ◇ (q0 ◇ q0)) ◇ t) (cg (fun t => q1 ◇ t) (px q0 (q0 ◇ q0) (q0 ◇ q0))))).trans (cg (fun t => ((q0 ◇ q0) ◇ (q0 ◇ q0)) ◇ t) (cg (fun t => q1 ◇ t) (pp q0)))).trans (px q1 (q0 ◇ q0) (q0 ◇ q0))))).symm
  have p1j : forall (q0 q1:G), ((q0 ◇ (q0 ◇ q0)) ◇ (q1 ◇ (q0 ◇ q0))) = (((q0 ◇ q0) ◇ q0) ◇ (q1 ◇ q0)):=by
    intro q0 q1
    exact (p1f q0 q1).trans (p1h q0 q1)
  have p1k : forall (q0 q1 q2 q3:G), (((q2 ◇ q1) ◇ q3) ◇ ((q0 ◇ q3) ◇ ((q2 ◇ q1) ◇ q0))) = q3:=by
    intro q0 q1 q2 q3
    exact ((cg (fun t => ((q2 ◇ q1) ◇ q3) ◇ t) (pg q1 q2 q0 q3 q0)).symm).trans (pa q1 q2 q3 q0)
  have p1l : forall (q0 q1 q2 q3 q4:G), ((((q0 ◇ q2) ◇ (q3 ◇ q0)) ◇ q4) ◇ q2) = ((q1 ◇ q4) ◇ ((q3 ◇ q2) ◇ q1)):=by
    intro q0 q1 q2 q3 q4
    exact ((cg (fun t => (((q0 ◇ q2) ◇ (q3 ◇ q0)) ◇ q4) ◇ t) ((h q2 q3 q0).symm)).symm).trans (ph q1 q2 q3 ((q0 ◇ q2) ◇ (q3 ◇ q0)) q4)
  have p1m : forall (q0 q1:G), ((q0 ◇ q1) ◇ ((q1 ◇ q1) ◇ q0)) = (q1 ◇ q1):=by
    intro q0 q1
    exact (((cg (fun t => t ◇ q1) (p13 q0 q1)).symm).trans (p1l q0 q0 q1 q1 q1)).symm
  have p1n : forall (q0 q1:G), ((((q1 ◇ q1) ◇ q0) ◇ ((q1 ◇ q1) ◇ q0)) ◇ (q1 ◇ q1)) = q0:=by
    intro q0 q1
    exact (((((cg (fun t => ((q1 ◇ q1) ◇ q0) ◇ t) (cg (fun t => ((q1 ◇ q1) ◇ q0) ◇ t) (cg (fun t => (q1 ◇ q1) ◇ t) (p1m q0 q1)))).trans (cg (fun t => ((q1 ◇ q1) ◇ q0) ◇ t) (pi q1 q1 (q1 ◇ q1) q0 (((q1 ◇ q1) ◇ q0) ◇ ((q1 ◇ q1) ◇ (q1 ◇ q1)))))).trans (p1k q1 q1 q1 q0)).symm).trans ((((cg (fun t => ((q1 ◇ q1) ◇ q0) ◇ t) (cg (fun t => ((q1 ◇ q1) ◇ q0) ◇ t) (cg (fun t => t ◇ ((q0 ◇ q1) ◇ ((q1 ◇ q1) ◇ q0))) (p1m q0 q1)))).symm).trans (p8 ((q1 ◇ q1) ◇ q0) (q0 ◇ q1) q0)).trans (cg (fun t => (((q1 ◇ q1) ◇ q0) ◇ ((q1 ◇ q1) ◇ q0)) ◇ t) (p1m q0 q1)))).symm
  have p1o : forall (q0 q1:G), (((q0 ◇ q1) ◇ (q0 ◇ q1)) ◇ q0) = q1:=by
    intro q0 q1
    exact ((((((cg (fun t => t ◇ ((q0 ◇ (q0 ◇ q0)) ◇ (q0 ◇ (q0 ◇ q0)))) (cg (fun t => t ◇ (((q0 ◇ (q0 ◇ q0)) ◇ (q0 ◇ (q0 ◇ q0))) ◇ q1)) (cg (fun t => t ◇ q1) (pt q0)))).trans (cg (fun t => t ◇ ((q0 ◇ (q0 ◇ q0)) ◇ (q0 ◇ (q0 ◇ q0)))) (cg (fun t => (q0 ◇ q1) ◇ t) (cg (fun t => t ◇ q1) (p1j q0 q0))))).trans (cg (fun t => t ◇ ((q0 ◇ (q0 ◇ q0)) ◇ (q0 ◇ (q0 ◇ q0)))) (cg (fun t => (q0 ◇ q1) ◇ t) (cg (fun t => t ◇ q1) (pt q0))))).trans (cg (fun t => ((q0 ◇ q1) ◇ (q0 ◇ q1)) ◇ t) (p1j q0 q0))).trans (cg (fun t => ((q0 ◇ q1) ◇ (q0 ◇ q1)) ◇ t) (pt q0))).symm).trans (((cg (fun t => t ◇ ((q0 ◇ (q0 ◇ q0)) ◇ (q0 ◇ (q0 ◇ q0)))) (cg (fun t => t ◇ (((q0 ◇ (q0 ◇ q0)) ◇ (q0 ◇ (q0 ◇ q0))) ◇ q1)) (cg (fun t => t ◇ q1) (p1j q0 q0)))).symm).trans (p1n q1 (q0 ◇ (q0 ◇ q0))))
  have p1p : forall (q0 q1:G), (q0 ◇ ((q1 ◇ q1) ◇ q0)) = q1:=by
    intro q0 q1
    exact ((cg (fun t => q0 ◇ t) (cg (fun t => (q1 ◇ q1) ◇ t) (p1o q1 q0))).symm).trans (((cg (fun t => t ◇ ((q1 ◇ q1) ◇ (((q1 ◇ q0) ◇ (q1 ◇ q0)) ◇ q1))) (p1o q1 q0)).symm).trans (p6 q1 ((q1 ◇ q0) ◇ (q1 ◇ q0))))
  have p1q : forall (q0 q1:G), (q1 ◇ (q0 ◇ q1)) = (q0 ◇ (q0 ◇ q0)):=by
    intro q0 q1
    exact ((((cg (fun t => q1 ◇ t) (cg (fun t => t ◇ q1) (cg (fun t => q0 ◇ t) (p15 q0 q0)))).trans (cg (fun t => q1 ◇ t) (cg (fun t => t ◇ q1) (p1h q0 q0)))).trans (cg (fun t => q1 ◇ t) (cg (fun t => t ◇ q1) (pt q0)))).symm).trans ((((cg (fun t => q1 ◇ t) (cg (fun t => t ◇ q1) (pf q0 ((q0 ◇ q0) ◇ (q0 ◇ q0)) ((q0 ◇ q0) ◇ (q0 ◇ q0))))).symm).trans (p1p q1 (((q0 ◇ q0) ◇ (q0 ◇ q0)) ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0))))).trans ((pi q0 q0 (q0 ◇ q0) (q0 ◇ q0) (((q0 ◇ q0) ◇ (q0 ◇ q0)) ◇ ((q0 ◇ q0) ◇ (q0 ◇ q0)))).trans (p1c q0 q0)))
  have p1r : forall (q0 q1:G), (q1 ◇ (q0 ◇ (q1 ◇ q1))) = ((q1 ◇ q1) ◇ q0):=by
    intro q0 q1
    exact (((cg (fun t => t ◇ (q0 ◇ q1)) (cg (fun t => (q1 ◇ q1) ◇ t) (p1m q0 q1))).trans (p15 q1 q0)).symm).trans (((cg (fun t => t ◇ (q0 ◇ q1)) (cg (fun t => t ◇ ((q0 ◇ q1) ◇ ((q1 ◇ q1) ◇ q0))) (p1m q0 q1))).symm).trans (p1o (q0 ◇ q1) ((q1 ◇ q1) ◇ q0)))
  have p1s : forall (q0 q1:G), (((q1 ◇ q0) ◇ q1) ◇ q1) = (q0 ◇ (q0 ◇ q0)):=by
    intro q0 q1
    exact (((cg (fun t => t ◇ q1) (cg (fun t => t ◇ q1) (cg (fun t => q1 ◇ t) (p1o q1 q0)))).symm).trans (p1d q1 ((q1 ◇ q0) ◇ (q1 ◇ q0)))).trans ((cg (fun t => q1 ◇ t) (cg (fun t => t ◇ q1) (p1o q1 q0))).trans (p1q q0 q1))
  have p1t : forall (q0 q1:G), (q0 ◇ ((q1 ◇ q0) ◇ q1)) = q1:=by
    intro q0 q1
    exact ((((cg (fun t => t ◇ ((q1 ◇ q0) ◇ q1)) (cg (fun t => (q0 ◇ (q0 ◇ q0)) ◇ t) (p1s q0 q1))).trans (cg (fun t => t ◇ ((q1 ◇ q0) ◇ q1)) (p1j q0 q0))).trans (cg (fun t => t ◇ ((q1 ◇ q0) ◇ q1)) (pt q0))).symm).trans (((cg (fun t => t ◇ ((q1 ◇ q0) ◇ q1)) (cg (fun t => t ◇ (((q1 ◇ q0) ◇ q1) ◇ q1)) (p1s q0 q1))).symm).trans (p1o ((q1 ◇ q0) ◇ q1) q1))
  have p1u : forall (q0 q1:G), ((q0 ◇ q1) ◇ q0) = ((q0 ◇ q0) ◇ q1):=by
    intro q0 q1
    exact (((cg (fun t => t ◇ q1) (cg (fun t => q0 ◇ t) (p1t q1 q0))).symm).trans (((cg (fun t => t ◇ q1) (cg (fun t => t ◇ (q1 ◇ ((q0 ◇ q1) ◇ q0))) (p1t q1 q0))).symm).trans (p1o q1 ((q0 ◇ q1) ◇ q0)))).symm
  have p1v : forall (q0 q1:G), ((((q0 ◇ q0) ◇ q0) ◇ ((q0 ◇ q0) ◇ q0)) ◇ q1) = (q1 ◇ (q1 ◇ q1)):=by
    intro q0 q1
    exact (((p1q q1 ((q0 ◇ q0) ◇ q0)).symm).trans (((cg (fun t => ((q0 ◇ q0) ◇ q0) ◇ t) (cg (fun t => q1 ◇ t) (p14 q0 q0))).symm).trans (p1r q1 ((q0 ◇ q0) ◇ q0)))).symm
  have p1w : forall (q0 q1:G), (q1 ◇ ((q0 ◇ q0) ◇ q0)) = q1:=by
    intro q0 q1
    exact ((((((cg (fun t => t ◇ ((((q0 ◇ q0) ◇ q0) ◇ ((q0 ◇ q0) ◇ q0)) ◇ (((q0 ◇ q0) ◇ q0) ◇ ((q0 ◇ q0) ◇ q0)))) (pc q1 q1)).trans (cg (fun t => q1 ◇ t) (pi q0 (q0 ◇ q0) ((q0 ◇ q0) ◇ q0) ((q0 ◇ q0) ◇ q0) ((((q0 ◇ q0) ◇ q0) ◇ ((q0 ◇ q0) ◇ q0)) ◇ (((q0 ◇ q0) ◇ q0) ◇ ((q0 ◇ q0) ◇ q0)))))).trans (cg (fun t => q1 ◇ t) (cg (fun t => (q0 ◇ ((q0 ◇ q0) ◇ q0)) ◇ t) (p1s q0 q0)))).trans (cg (fun t => q1 ◇ t) (cg (fun t => t ◇ (q0 ◇ (q0 ◇ q0))) (p1p q0 q0)))).trans (cg (fun t => q1 ◇ t) (p1r q0 q0))).symm).trans ((((cg (fun t => t ◇ ((((q0 ◇ q0) ◇ q0) ◇ ((q0 ◇ q0) ◇ q0)) ◇ (((q0 ◇ q0) ◇ q0) ◇ ((q0 ◇ q0) ◇ q0)))) (p1v q0 (q1 ◇ q1))).symm).trans (p1i q1 (((q0 ◇ q0) ◇ q0) ◇ ((q0 ◇ q0) ◇ q0)))).trans ((((cg (fun t => (q1 ◇ (q1 ◇ q1)) ◇ t) (p1v q0 q1)).trans (p1j q1 q1)).trans (p1u (q1 ◇ q1) q1)).trans (p13 q1 q1)))
  have p1x : forall (q1 q2 q3 q4 q0:G), ((q1 ◇ (q3 ◇ q1)) ◇ q4) = ((q2 ◇ q4) ◇ (q3 ◇ q2)):=by
    intro q1 q2 q3 q4 q0
    exact ((cg (fun t => t ◇ q4) (cg (fun t => t ◇ (q3 ◇ q1)) (p1w q0 q1))).symm).trans ((((p1w q0 (((q1 ◇ ((q0 ◇ q0) ◇ q0)) ◇ (q3 ◇ q1)) ◇ q4)).symm).trans (p1l q1 q2 ((q0 ◇ q0) ◇ q0) q3 q4)).trans (cg (fun t => (q2 ◇ q4) ◇ t) (cg (fun t => t ◇ q2) (p1w q0 q3))))
  have p1y : forall (q0 q2 q3 q1:G), ((q2 ◇ q3) ◇ q0) = ((q2 ◇ q0) ◇ q3):=by
    intro q0 q2 q3 q1
    exact (((cg (fun t => (q2 ◇ q3) ◇ t) (p1o q2 q0)).symm).trans ((p1x q1 q2 ((q2 ◇ q0) ◇ (q2 ◇ q0)) q3 q0).symm)).trans (cg (fun t => t ◇ q3) (p1p q1 (q2 ◇ q0)))
  exact (calc
    x = x:=rfl
    _ = ((y ◇ ((z ◇ x) ◇ (y ◇ z))) ◇ x):=(((((cg (fun t => t ◇ x) (cg (fun t => y ◇ t) (px y z x))).trans (cg (fun t => t ◇ x) (cg (fun t => y ◇ t) (py x y ((y ◇ x) ◇ (y ◇ y)))))).trans (p1y x y ((x ◇ x) ◇ (y ◇ x)) ((y ◇ ((x ◇ x) ◇ (y ◇ x))) ◇ x))).trans (p1q (x ◇ x) (y ◇ x))).trans (pc x x)).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_19010_to_31535 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_19010_to_31535
