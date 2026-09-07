-- Equation19023 → Equation57619
-- Recorded verdict: true
-- Premise: x = (y ◇ x) ◇ ((z ◇ y) ◇ (x ◇ z))
-- Conclusion: x ◇ (y ◇ x) = ((z ◇ y) ◇ z) ◇ z
-- Original submission SHA-256: e5f6dadd4e7fd598dcc32eb82429bf1eb6a47f31da8f18c464798b8c54b8880b
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (y ◇ x) ◇ ((z ◇ y) ◇ (x ◇ z))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ (y ◇ x) = ((z ◇ y) ◇ z) ◇ z
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z
  have cg : ∀ (f:G → G) {a b:G}, a=b → f a=f b:=by
    intro f a b p
    exact congrArg f p
  have p0:=fun (a b:G)=>by
    exact ((cg (fun t => (b ◇ (a ◇ (b ◇ a))) ◇ t) ((h b (b ◇ a) a).symm)).symm).trans ((h (a ◇ (b ◇ a)) b (b ◇ a)).symm)
  have p1:=fun (a:G)=>by
    exact ((cg (fun t => t ◇ (a ◇ a)) (cg (fun t => (a ◇ a) ◇ t) ((h a a a).symm))).symm).trans (p0 (a ◇ a) (a ◇ a))
  have p2:=fun (a b c:G)=>by
    exact ((h a b c).symm).trans (h a a a)
  have p3:=fun (a:G)=>by
    exact ((p2 a a a).symm).trans ((h a a a).symm)
  have p4:=fun (a:G)=>by
    exact (p1 a).trans (p3 a)
  have p5:=fun (a b c d:G)=>by
    exact ((cg (fun t => t ◇ ((d ◇ (b ◇ a)) ◇ (((c ◇ b) ◇ (a ◇ c)) ◇ d))) ((h a b c).symm)).symm).trans ((h ((c ◇ b) ◇ (a ◇ c)) (b ◇ a) d).symm)
  have p6:=fun (a:G)=>by
    exact (((cg (fun t => t ◇ ((a ◇ a) ◇ a)) (cg (fun t => ((a ◇ a) ◇ a) ◇ t) (cg (fun t => (a ◇ a) ◇ t) (p4 a)))).symm).trans (p0 (a ◇ a) ((a ◇ a) ◇ a))).trans (cg (fun t => (a ◇ a) ◇ t) (p4 a))
  have p7:=fun (a b:G)=>by
    exact (((cg (fun t => t ◇ (b ◇ (a ◇ (b ◇ a)))) (cg (fun t => (b ◇ (a ◇ (b ◇ a))) ◇ t) (cg (fun t => b ◇ t) (p0 a b)))).symm).trans (p0 b (b ◇ (a ◇ (b ◇ a))))).trans (cg (fun t => b ◇ t) (p0 a b))
  have p8:=fun (a b c d:G)=>by
    exact ((cg (fun t => (((c ◇ b) ◇ (a ◇ c)) ◇ d) ◇ t) (cg (fun t => t ◇ (d ◇ (b ◇ a))) ((h a b c).symm))).symm).trans ((h d ((c ◇ b) ◇ (a ◇ c)) (b ◇ a)).symm)
  have p9:=fun (a:G)=>by
    exact (((cg (fun t => t ◇ (((a ◇ a) ◇ a) ◇ ((a ◇ a) ◇ a))) (cg (fun t => (((a ◇ a) ◇ a) ◇ ((a ◇ a) ◇ a)) ◇ t) (cg (fun t => ((a ◇ a) ◇ a) ◇ t) (p6 a)))).symm).trans (p0 ((a ◇ a) ◇ a) (((a ◇ a) ◇ a) ◇ ((a ◇ a) ◇ a)))).trans (cg (fun t => ((a ◇ a) ◇ a) ◇ t) (p6 a))
  have pa:=fun (a:G)=>by
    exact (((p3 ((a ◇ a) ◇ a)).symm).trans (((cg (fun t => t ◇ ((((a ◇ a) ◇ a) ◇ ((a ◇ a) ◇ a)) ◇ (((a ◇ a) ◇ a) ◇ ((a ◇ a) ◇ a)))) (p9 a)).symm).trans (p4 (((a ◇ a) ◇ a) ◇ ((a ◇ a) ◇ a))))).symm
  have pb:=fun (a b c d:G)=>by
    exact ((cg (fun t => (d ◇ (b ◇ a)) ◇ t) (cg (fun t => (((c ◇ b) ◇ (a ◇ c)) ◇ d) ◇ t) ((h a b c).symm))).symm).trans ((h (b ◇ a) d ((c ◇ b) ◇ (a ◇ c))).symm)
  have pc:=fun (a b:G)=>by
    exact ((cg (fun t => (b ◇ (a ◇ (b ◇ a))) ◇ t) (p7 a b)).symm).trans ((((cg (fun t => t ◇ (((b ◇ (a ◇ (b ◇ a))) ◇ (b ◇ (a ◇ (b ◇ a)))) ◇ (b ◇ (a ◇ (b ◇ a))))) (p7 a b)).symm).trans (pa (b ◇ (a ◇ (b ◇ a))))).trans (p7 a b))
  have pd:=fun (a b:G)=>by
    exact ((cg (fun t => ((a ◇ a) ◇ b) ◇ t) (cg (fun t => t ◇ (b ◇ ((a ◇ a) ◇ a))) (p4 a))).symm).trans ((h b (a ◇ a) ((a ◇ a) ◇ a)).symm)
  have pe:=fun (a:G)=>by
    exact ((cg (fun t => ((a ◇ a) ◇ ((a ◇ a) ◇ a)) ◇ t) (cg (fun t => a ◇ t) (pa a))).symm).trans (pd a ((a ◇ a) ◇ a))
  have pf:=fun (a b:G)=>by
    exact ((cg (fun t => t ◇ ((b ◇ ((a ◇ a) ◇ a)) ◇ ((a ◇ a) ◇ b))) (p4 a)).symm).trans ((h (a ◇ a) ((a ◇ a) ◇ a) b).symm)
  have pg:=fun (a:G)=>by
    exact ((cg (fun t => a ◇ t) (cg (fun t => t ◇ ((a ◇ a) ◇ ((a ◇ a) ◇ a))) (pa a))).symm).trans (pf a ((a ◇ a) ◇ a))
  have ph:=fun (a b:G)=>by
    exact ((cg (fun t => (((a ◇ a) ◇ a) ◇ b) ◇ t) (cg (fun t => t ◇ (b ◇ ((a ◇ a) ◇ a))) (pa a))).symm).trans ((h b ((a ◇ a) ◇ a) ((a ◇ a) ◇ a)).symm)
  have pi:=fun (a b c:G)=>by
    exact ((cg (fun t => (b ◇ (c ◇ (a ◇ (c ◇ a)))) ◇ t) (cg (fun t => (c ◇ b) ◇ t) (p0 a c))).symm).trans ((h (c ◇ (a ◇ (c ◇ a))) b c).symm)
  have pj:=fun (a b:G)=>by
    exact ((cg (fun t => (b ◇ ((a ◇ a) ◇ a)) ◇ t) (cg (fun t => ((a ◇ a) ◇ b) ◇ t) (p4 a))).symm).trans ((h ((a ◇ a) ◇ a) b (a ◇ a)).symm)
  have pk:=fun (a:G)=>by
    exact ((cg (fun t => (((a ◇ a) ◇ (a ◇ a)) ◇ ((a ◇ a) ◇ a)) ◇ t) (cg (fun t => t ◇ a) (p3 a))).symm).trans (pj a ((a ◇ a) ◇ (a ◇ a)))
  have pl:=fun (a:G)=>by
    exact ((cg (fun t => t ◇ (((a ◇ a) ◇ ((a ◇ a) ◇ a)) ◇ a)) (pa a)).symm).trans (pj a ((a ◇ a) ◇ a))
  have pm:=fun (a:G)=>by
    exact ((((cg (fun t => t ◇ (((a ◇ a) ◇ a) ◇ ((a ◇ a) ◇ a))) (cg (fun t => (((a ◇ a) ◇ ((a ◇ a) ◇ a)) ◇ a) ◇ t) (cg (fun t => t ◇ ((a ◇ a) ◇ a)) (pa a)))).trans (cg (fun t => t ◇ (((a ◇ a) ◇ a) ◇ ((a ◇ a) ◇ a))) (cg (fun t => (((a ◇ a) ◇ ((a ◇ a) ◇ a)) ◇ a) ◇ t) (pa a)))).trans (cg (fun t => ((((a ◇ a) ◇ ((a ◇ a) ◇ a)) ◇ a) ◇ ((a ◇ a) ◇ a)) ◇ t) (pa a))).symm).trans ((((cg (fun t => ((((a ◇ a) ◇ ((a ◇ a) ◇ a)) ◇ a) ◇ ((((a ◇ a) ◇ a) ◇ ((a ◇ a) ◇ a)) ◇ ((a ◇ a) ◇ a))) ◇ t) (cg (fun t => t ◇ ((a ◇ a) ◇ a)) (pj a ((a ◇ a) ◇ a)))).symm).trans (pj ((a ◇ a) ◇ a) (((a ◇ a) ◇ ((a ◇ a) ◇ a)) ◇ a))).trans ((cg (fun t => t ◇ ((a ◇ a) ◇ a)) (pa a)).trans (pa a)))
  have pn:=fun (a:G)=>by
    exact ((cg (fun t => t ◇ (a ◇ ((((a ◇ a) ◇ (a ◇ a)) ◇ ((a ◇ a) ◇ (a ◇ a))) ◇ (a ◇ a)))) (p3 (a ◇ a))).symm).trans (p8 a a a (((a ◇ a) ◇ (a ◇ a)) ◇ ((a ◇ a) ◇ (a ◇ a))))
  have po:=fun (a:G)=>by
    exact (((cg (fun t => t ◇ ((((a ◇ a) ◇ ((a ◇ a) ◇ a)) ◇ a) ◇ ((a ◇ a) ◇ a))) (cg (fun t => ((((a ◇ a) ◇ ((a ◇ a) ◇ a)) ◇ a) ◇ ((a ◇ a) ◇ a)) ◇ t) (pa a))).trans (cg (fun t => t ◇ ((((a ◇ a) ◇ ((a ◇ a) ◇ a)) ◇ a) ◇ ((a ◇ a) ◇ a))) (pm a))).symm).trans ((((cg (fun t => t ◇ ((((a ◇ a) ◇ ((a ◇ a) ◇ a)) ◇ a) ◇ ((a ◇ a) ◇ a))) (cg (fun t => ((((a ◇ a) ◇ ((a ◇ a) ◇ a)) ◇ a) ◇ ((a ◇ a) ◇ a)) ◇ t) (cg (fun t => ((a ◇ a) ◇ a) ◇ t) (pm a)))).symm).trans (p0 ((a ◇ a) ◇ a) ((((a ◇ a) ◇ ((a ◇ a) ◇ a)) ◇ a) ◇ ((a ◇ a) ◇ a)))).trans ((cg (fun t => ((a ◇ a) ◇ a) ◇ t) (pm a)).trans (pa a)))
  have pp:=fun (a:G)=>by
    exact ((((cg (fun t => t ◇ ((a ◇ a) ◇ a)) (pl a)).trans (pa a)).symm).trans (((cg (fun t => (((a ◇ a) ◇ a) ◇ (((a ◇ a) ◇ ((a ◇ a) ◇ a)) ◇ a)) ◇ t) (po a)).symm).trans (ph a (((a ◇ a) ◇ ((a ◇ a) ◇ a)) ◇ a)))).symm
  have pq:=fun (a:G)=>by
    exact ((cg (fun t => t ◇ ((a ◇ a) ◇ ((a ◇ a) ◇ a))) (pe a)).symm).trans ((((cg (fun t => t ◇ ((a ◇ a) ◇ ((a ◇ a) ◇ a))) (cg (fun t => ((a ◇ a) ◇ ((a ◇ a) ◇ a)) ◇ t) (cg (fun t => a ◇ t) (pp a)))).symm).trans (p0 a ((a ◇ a) ◇ ((a ◇ a) ◇ a)))).trans (cg (fun t => a ◇ t) (pp a)))
  have pr:=fun (a:G)=>by
    exact ((cg (fun t => a ◇ t) (pq a)).symm).trans (pg a)
  have ps:=fun (a:G)=>by
    exact ((cg (fun t => t ◇ ((a ◇ a) ◇ (a ◇ (a ◇ (a ◇ a))))) (pp a)).symm).trans (p8 (a ◇ a) a a a)
  have pt:=fun (a b:G)=>by
    exact ((cg (fun t => (((a ◇ (b ◇ b)) ◇ (b ◇ a)) ◇ b) ◇ t) (pr b)).symm).trans (p8 b (b ◇ b) a b)
  have pu:=fun (a b:G)=>by
    exact ((cg (fun t => (b ◇ ((a ◇ a) ◇ a)) ◇ t) (cg (fun t => (((a ◇ a) ◇ a) ◇ b) ◇ t) (pa a))).symm).trans ((h ((a ◇ a) ◇ a) b ((a ◇ a) ◇ a)).symm)
  have pv:=fun (a:G)=>by
    exact ((cg (fun t => (((a ◇ a) ◇ (a ◇ a)) ◇ (a ◇ a)) ◇ t) (cg (fun t => ((a ◇ a) ◇ (a ◇ a)) ◇ t) (cg (fun t => (a ◇ a) ◇ t) ((h a a a).symm)))).symm).trans (ps (a ◇ a))
  have pw:=fun (a:G)=>by
    exact ((cg (fun t => (((a ◇ a) ◇ a) ◇ (((a ◇ a) ◇ (a ◇ a)) ◇ (a ◇ a))) ◇ t) (pk a)).symm).trans (pj (a ◇ a) ((a ◇ a) ◇ a))
  have px:=fun (a b:G)=>by
    exact ((cg (fun t => (((b ◇ a) ◇ (((a ◇ a) ◇ a) ◇ b)) ◇ a) ◇ t) (pd a a)).symm).trans (p8 ((a ◇ a) ◇ a) a b a)
  have py:=fun (a:G)=>by
    exact (((cg (fun t => t ◇ (a ◇ a)) (cg (fun t => t ◇ (a ◇ a)) (cg (fun t => ((a ◇ a) ◇ a) ◇ t) (pv a)))).trans (cg (fun t => t ◇ (a ◇ a)) (cg (fun t => t ◇ (a ◇ a)) (p4 a)))).symm).trans (((cg (fun t => t ◇ (a ◇ a)) (cg (fun t => t ◇ (a ◇ a)) (cg (fun t => t ◇ ((((a ◇ a) ◇ (a ◇ a)) ◇ (a ◇ a)) ◇ (((a ◇ a) ◇ (a ◇ a)) ◇ ((a ◇ a) ◇ a)))) (pk a)))).symm).trans (px (a ◇ a) (((a ◇ a) ◇ (a ◇ a)) ◇ ((a ◇ a) ◇ a))))
  have pz:=fun (a:G)=>by
    exact ((cg (fun t => t ◇ ((a ◇ a) ◇ (a ◇ a))) ((h a a a).symm)).symm).trans (py (a ◇ a))
  have p10:=fun (a:G)=>by
    exact ((cg (fun t => t ◇ ((a ◇ a) ◇ (a ◇ a))) (pk a)).symm).trans (((cg (fun t => t ◇ ((a ◇ a) ◇ (a ◇ a))) (cg (fun t => t ◇ (a ◇ a)) (cg (fun t => t ◇ ((a ◇ a) ◇ a)) (pz a)))).symm).trans (pt a (a ◇ a)))
  have p11:=fun (a b:G)=>by
    exact ((cg (fun t => ((a ◇ a) ◇ b) ◇ t) (cg (fun t => t ◇ (b ◇ (a ◇ (a ◇ a)))) (py a))).symm).trans ((h b (a ◇ a) (a ◇ (a ◇ a))).symm)
  have p12:=fun (a b:G)=>by
    exact ((cg (fun t => t ◇ ((b ◇ (a ◇ (a ◇ a))) ◇ ((a ◇ a) ◇ b))) (py a)).symm).trans ((h (a ◇ a) (a ◇ (a ◇ a)) b).symm)
  have p13:=fun (a:G)=>by
    exact ((cg (fun t => (a ◇ a) ◇ t) (cg (fun t => (((a ◇ a) ◇ (a ◇ a)) ◇ (a ◇ (a ◇ a))) ◇ t) (p3 a))).symm).trans (p12 a ((a ◇ a) ◇ (a ◇ a)))
  have p14:=fun (a b:G)=>by
    exact ((cg (fun t => (b ◇ (a ◇ (a ◇ a))) ◇ t) (cg (fun t => ((a ◇ a) ◇ b) ◇ t) (py a))).symm).trans ((h (a ◇ (a ◇ a)) b (a ◇ a)).symm)
  have p15:=fun (a:G)=>by
    exact ((cg (fun t => (((a ◇ a) ◇ (a ◇ a)) ◇ (a ◇ (a ◇ a))) ◇ t) (cg (fun t => t ◇ (a ◇ a)) (p3 a))).symm).trans (p14 a ((a ◇ a) ◇ (a ◇ a)))
  have p16:=fun (a b:G)=>by
    exact ((cg (fun t => t ◇ ((b ◇ a) ◇ (((a ◇ a) ◇ (a ◇ a)) ◇ b))) (pz a)).symm).trans ((h ((a ◇ a) ◇ (a ◇ a)) a b).symm)
  have p17:=fun (a b:G)=>by
    exact ((cg (fun t => (((b ◇ (a ◇ a)) ◇ ((a ◇ a) ◇ b)) ◇ (a ◇ a)) ◇ t) (cg (fun t => (a ◇ a) ◇ t) (p3 a))).symm).trans (p8 (a ◇ a) (a ◇ a) b (a ◇ a))
  have p18:=fun (a:G)=>by
    exact (((cg (fun t => t ◇ ((a ◇ a) ◇ a)) (cg (fun t => t ◇ (a ◇ a)) (cg (fun t => t ◇ (a ◇ a)) (pt (a ◇ a) a)))).trans (cg (fun t => t ◇ ((a ◇ a) ◇ a)) (py a))).symm).trans (((cg (fun t => t ◇ ((a ◇ a) ◇ a)) (cg (fun t => t ◇ (a ◇ a)) (cg (fun t => (((((a ◇ a) ◇ (a ◇ a)) ◇ (a ◇ (a ◇ a))) ◇ a) ◇ (a ◇ a)) ◇ t) (p13 a)))).symm).trans (p17 a ((((a ◇ a) ◇ (a ◇ a)) ◇ (a ◇ (a ◇ a))) ◇ a)))
  have p19:=fun (a:G)=>by
    exact (((p4 a).symm).trans (((cg (fun t => ((a ◇ a) ◇ a) ◇ t) (p18 a)).symm).trans (pq a))).symm
  have p1a:=fun (a:G)=>by
    exact ((cg (fun t => (((a ◇ a) ◇ a) ◇ a) ◇ t) (cg (fun t => ((a ◇ a) ◇ a) ◇ t) (p19 a))).symm).trans (ph a a)
  have p1b:=fun (a:G)=>by
    exact ((((cg (fun t => a ◇ t) (cg (fun t => t ◇ ((((a ◇ a) ◇ a) ◇ a) ◇ (((a ◇ a) ◇ a) ◇ a))) (p1a a))).trans (cg (fun t => a ◇ t) (cg (fun t => a ◇ t) (p1a a)))).symm).trans (((cg (fun t => t ◇ (((((a ◇ a) ◇ a) ◇ a) ◇ (((a ◇ a) ◇ a) ◇ a)) ◇ ((((a ◇ a) ◇ a) ◇ a) ◇ (((a ◇ a) ◇ a) ◇ a)))) (p1a a)).symm).trans (p3 (((a ◇ a) ◇ a) ◇ a)))).symm
  have p1c:=fun (a:G)=>by
    exact (((cg (fun t => t ◇ (((a ◇ a) ◇ a) ◇ a)) (p1b a)).trans (cg (fun t => (a ◇ (a ◇ a)) ◇ t) (p1b a))).symm).trans (p1a a)
  have p1d:=fun (a:G)=>by
    exact (((cg (fun t => t ◇ (a ◇ (a ◇ a))) (p19 a)).symm).trans (((cg (fun t => (a ◇ ((a ◇ a) ◇ a)) ◇ t) (p1b a)).symm).trans (pj a a))).symm
  have p1e:=fun (a:G)=>by
    exact (((((cg (fun t => t ◇ ((a ◇ a) ◇ a)) (cg (fun t => ((a ◇ a) ◇ a) ◇ t) (cg (fun t => (a ◇ a) ◇ t) (p3 a)))).trans (cg (fun t => t ◇ ((a ◇ a) ◇ a)) (pa a))).trans (pa a)).symm).trans (((cg (fun t => t ◇ ((a ◇ a) ◇ a)) (cg (fun t => ((a ◇ a) ◇ a) ◇ t) (p1d (a ◇ a)))).symm).trans (pw a))).symm
  have p1f:=fun (a:G)=>by
    exact ((cg (fun t => ((a ◇ a) ◇ (a ◇ a)) ◇ t) (cg (fun t => a ◇ t) (p18 a))).symm).trans (pd a (a ◇ a))
  have p1g:=fun (a:G)=>by
    exact ((cg (fun t => t ◇ (a ◇ (a ◇ a))) (p1f a)).symm).trans (p15 a)
  have p1h:=fun (a:G)=>by
    exact (((cg (fun t => ((a ◇ a) ◇ (a ◇ a)) ◇ t) ((h a a a).symm)).symm).trans (p1g (a ◇ a))).trans (p3 a)
  have p1i:=fun (a:G)=>by
    exact (((p1g a).symm).trans (((cg (fun t => (a ◇ a) ◇ t) (cg (fun t => a ◇ t) (p1h (a ◇ a)))).symm).trans (pn a))).symm
  have p1j:=fun (a:G)=>by
    exact (((((cg (fun t => t ◇ (((a ◇ (a ◇ a)) ◇ (a ◇ (a ◇ a))) ◇ ((a ◇ (a ◇ a)) ◇ (a ◇ (a ◇ a))))) (cg (fun t => a ◇ t) (p1c a))).trans (cg (fun t => (a ◇ a) ◇ t) (cg (fun t => t ◇ ((a ◇ (a ◇ a)) ◇ (a ◇ (a ◇ a)))) (p1c a)))).trans (cg (fun t => (a ◇ a) ◇ t) (cg (fun t => a ◇ t) (p1c a)))).symm).trans ((((cg (fun t => t ◇ (((a ◇ (a ◇ a)) ◇ (a ◇ (a ◇ a))) ◇ ((a ◇ (a ◇ a)) ◇ (a ◇ (a ◇ a))))) (cg (fun t => t ◇ ((a ◇ (a ◇ a)) ◇ (a ◇ (a ◇ a)))) (p1c a))).symm).trans (p1i (a ◇ (a ◇ a)))).trans (cg (fun t => (a ◇ (a ◇ a)) ◇ t) (p1c a)))).symm
  have p1k:=fun (a:G)=>by
    exact ((cg (fun t => a ◇ t) (cg (fun t => t ◇ (a ◇ (a ◇ a))) (p1c a))).symm).trans ((((cg (fun t => t ◇ (((a ◇ (a ◇ a)) ◇ (a ◇ (a ◇ a))) ◇ (a ◇ (a ◇ a)))) (p1c a)).symm).trans (p18 (a ◇ (a ◇ a)))).trans (p1c a))
  have p1l:=fun (a:G)=>by
    exact ((cg (fun t => (a ◇ a) ◇ t) (p1d a)).symm).trans (p18 a)
  have p1m:=fun (a:G)=>by
    exact ((cg (fun t => (a ◇ (a ◇ a)) ◇ t) (cg (fun t => (a ◇ a) ◇ t) (p1c a))).symm).trans (((cg (fun t => t ◇ ((a ◇ a) ◇ ((a ◇ (a ◇ a)) ◇ (a ◇ (a ◇ a))))) (p1g a)).symm).trans (p11 a (a ◇ (a ◇ a))))
  have p1n:=fun (a:G)=>by
    exact (((cg (fun t => ((a ◇ a) ◇ (a ◇ a)) ◇ t) (cg (fun t => ((a ◇ a) ◇ a) ◇ t) (cg (fun t => (a ◇ a) ◇ t) (p3 a)))).trans (cg (fun t => ((a ◇ a) ◇ (a ◇ a)) ◇ t) (pa a))).symm).trans (((cg (fun t => ((a ◇ a) ◇ (a ◇ a)) ◇ t) (cg (fun t => ((a ◇ a) ◇ a) ◇ t) (p1d (a ◇ a)))).symm).trans (p16 a (a ◇ a)))
  have p1o:=fun (a:G)=>by
    exact (((cg (fun t => t ◇ ((a ◇ a) ◇ (a ◇ a))) (p1i a)).symm).trans (p1d ((a ◇ a) ◇ (a ◇ a)))).trans (((cg (fun t => ((a ◇ a) ◇ (a ◇ a)) ◇ t) (cg (fun t => ((a ◇ a) ◇ (a ◇ a)) ◇ t) (p1i a))).trans (cg (fun t => ((a ◇ a) ◇ (a ◇ a)) ◇ t) (p1f a))).trans (p1e a))
  have p1p:=fun (a:G)=>by
    exact ((cg (fun t => t ◇ (a ◇ (a ◇ a))) (p1e a)).symm).trans (((cg (fun t => (((a ◇ a) ◇ (a ◇ a)) ◇ (a ◇ a)) ◇ t) (p1i a)).symm).trans (p10 (a ◇ a)))
  have p1q:=fun (a:G)=>by
    exact ((cg (fun t => ((a ◇ a) ◇ (a ◇ a)) ◇ t) (cg (fun t => a ◇ t) (p1i a))).symm).trans (((cg (fun t => ((a ◇ a) ◇ (a ◇ a)) ◇ t) (cg (fun t => t ◇ (((a ◇ a) ◇ (a ◇ a)) ◇ ((a ◇ a) ◇ (a ◇ a)))) (p1h a))).symm).trans (p16 a ((a ◇ a) ◇ (a ◇ a))))
  have p1r:=fun (a b c:G)=>by
    exact ((cg (fun t => (a ◇ a) ◇ t) (cg (fun t => t ◇ (((b ◇ ((a ◇ a) ◇ a)) ◇ ((a ◇ a) ◇ b)) ◇ c)) (cg (fun t => c ◇ t) (p4 a)))).symm).trans (p5 (a ◇ a) ((a ◇ a) ◇ a) b c)
  have p1s:=fun (a b:G)=>by
    exact ((cg (fun t => (a ◇ a) ◇ t) (cg (fun t => (b ◇ a) ◇ t) (cg (fun t => t ◇ b) (p19 a)))).symm).trans ((((cg (fun t => (a ◇ a) ◇ t) (cg (fun t => (b ◇ a) ◇ t) (cg (fun t => t ◇ b) (cg (fun t => t ◇ ((a ◇ a) ◇ a)) (p19 a))))).symm).trans (p1r a a b)).trans ((cg (fun t => t ◇ ((a ◇ a) ◇ a)) (p19 a)).trans (p19 a)))
  have p1t:=fun (a b:G)=>by
    exact ((cg (fun t => (((b ◇ b) ◇ b) ◇ a) ◇ t) (cg (fun t => t ◇ (a ◇ b)) (p19 b))).symm).trans ((h a ((b ◇ b) ◇ b) b).symm)
  have p1u:=fun (a b:G)=>by
    exact ((cg (fun t => t ◇ ((b ◇ a) ◇ (((a ◇ a) ◇ a) ◇ b))) (p19 a)).symm).trans ((h ((a ◇ a) ◇ a) a b).symm)
  have p1v:=fun (a b:G)=>by
    exact ((cg (fun t => (b ◇ a) ◇ t) (cg (fun t => t ◇ (a ◇ ((b ◇ b) ◇ (b ◇ b)))) (p1h b))).symm).trans ((h a b ((b ◇ b) ◇ (b ◇ b))).symm)
  have p1w:=fun (a b:G)=>by
    exact ((cg (fun t => (((b ◇ a) ◇ ((a ◇ a) ◇ b)) ◇ a) ◇ t) (p1l a)).symm).trans (p8 (a ◇ a) a b a)
  have p1x:=fun (a b:G)=>by
    exact ((cg (fun t => t ◇ ((b ◇ ((a ◇ a) ◇ a)) ◇ (a ◇ b))) (p1b a)).symm).trans ((h a ((a ◇ a) ◇ a) b).symm)
  have p1y:=fun (a b:G)=>by
    exact ((cg (fun t => (b ◇ a) ◇ t) (cg (fun t => t ◇ (a ◇ (b ◇ b))) (p1d b))).symm).trans ((h a b (b ◇ b)).symm)
  have p1z:=fun (a b:G)=>by
    exact ((cg (fun t => ((a ◇ (a ◇ a)) ◇ b) ◇ t) (cg (fun t => t ◇ (b ◇ (a ◇ (a ◇ a)))) (p1c a))).symm).trans ((h b (a ◇ (a ◇ a)) (a ◇ (a ◇ a))).symm)
  have p20:=fun (a b:G)=>by
    exact ((cg (fun t => (a ◇ b) ◇ t) (cg (fun t => (a ◇ a) ◇ t) (cg (fun t => b ◇ t) (p1s a a)))).symm).trans (((cg (fun t => t ◇ ((a ◇ a) ◇ (b ◇ ((a ◇ a) ◇ ((a ◇ a) ◇ (a ◇ a)))))) (cg (fun t => t ◇ b) ((h a a a).symm))).symm).trans (p1z (a ◇ a) b))
  have p21:=fun (a b:G)=>by
    exact ((cg (fun t => t ◇ (b ◇ (((a ◇ (b ◇ b)) ◇ (b ◇ a)) ◇ b))) ((h b (b ◇ b) a).symm)).symm).trans (p1t ((a ◇ (b ◇ b)) ◇ (b ◇ a)) b)
  have p22:=fun (a b:G)=>by
    exact ((cg (fun t => (a ◇ (b ◇ b)) ◇ t) (cg (fun t => (b ◇ a) ◇ t) (p1d b))).symm).trans ((h (b ◇ b) a b).symm)
  have p23:=fun (a b:G)=>by
    exact ((((((cg (fun t => (((b ◇ ((a ◇ a) ◇ a)) ◇ (a ◇ b)) ◇ ((a ◇ (a ◇ a)) ◇ (a ◇ (a ◇ a)))) ◇ t) (cg (fun t => a ◇ t) (cg (fun t => (a ◇ (a ◇ a)) ◇ t) (cg (fun t => (a ◇ (a ◇ a)) ◇ t) (p1c a))))).trans (cg (fun t => (((b ◇ ((a ◇ a) ◇ a)) ◇ (a ◇ b)) ◇ ((a ◇ (a ◇ a)) ◇ (a ◇ (a ◇ a)))) ◇ t) (cg (fun t => a ◇ t) (cg (fun t => (a ◇ (a ◇ a)) ◇ t) (p1j a))))).trans (cg (fun t => t ◇ (a ◇ ((a ◇ (a ◇ a)) ◇ ((a ◇ a) ◇ (a ◇ a))))) (cg (fun t => ((b ◇ ((a ◇ a) ◇ a)) ◇ (a ◇ b)) ◇ t) (p1c a)))).trans (cg (fun t => (((b ◇ ((a ◇ a) ◇ a)) ◇ (a ◇ b)) ◇ a) ◇ t) (cg (fun t => a ◇ t) (p1o a)))).trans (cg (fun t => (((b ◇ ((a ◇ a) ◇ a)) ◇ (a ◇ b)) ◇ a) ◇ t) (p19 a))).symm).trans ((((cg (fun t => (((b ◇ ((a ◇ a) ◇ a)) ◇ (a ◇ b)) ◇ ((a ◇ (a ◇ a)) ◇ (a ◇ (a ◇ a)))) ◇ t) (cg (fun t => t ◇ ((a ◇ (a ◇ a)) ◇ ((a ◇ (a ◇ a)) ◇ ((a ◇ (a ◇ a)) ◇ (a ◇ (a ◇ a)))))) (p1x a b))).symm).trans (p22 ((b ◇ ((a ◇ a) ◇ a)) ◇ (a ◇ b)) (a ◇ (a ◇ a)))).trans (p1c a))
  have p24:=fun (a b:G)=>by
    exact ((cg (fun t => b ◇ t) (cg (fun t => (((a ◇ b) ◇ (b ◇ a)) ◇ ((b ◇ b) ◇ b)) ◇ t) ((h b b a).symm))).symm).trans (pf b ((a ◇ b) ◇ (b ◇ a)))
  have p25:=fun (a b:G)=>by
    exact ((((cg (fun t => ((a ◇ (a ◇ a)) ◇ b) ◇ t) (cg (fun t => t ◇ (b ◇ ((a ◇ (a ◇ a)) ◇ (a ◇ (a ◇ a))))) (cg (fun t => (a ◇ (a ◇ a)) ◇ t) (p1j a)))).trans (cg (fun t => ((a ◇ (a ◇ a)) ◇ b) ◇ t) (cg (fun t => ((a ◇ (a ◇ a)) ◇ ((a ◇ a) ◇ (a ◇ a))) ◇ t) (cg (fun t => b ◇ t) (p1c a))))).trans (cg (fun t => ((a ◇ (a ◇ a)) ◇ b) ◇ t) (cg (fun t => t ◇ (b ◇ a)) (p1o a)))).symm).trans (((cg (fun t => ((a ◇ (a ◇ a)) ◇ b) ◇ t) (cg (fun t => t ◇ (b ◇ ((a ◇ (a ◇ a)) ◇ (a ◇ (a ◇ a))))) (cg (fun t => (a ◇ (a ◇ a)) ◇ t) (cg (fun t => (a ◇ (a ◇ a)) ◇ t) (p1c a))))).symm).trans (p1y b (a ◇ (a ◇ a))))
  have p26:=fun (a b:G)=>by
    exact ((cg (fun t => (a ◇ b) ◇ t) (cg (fun t => t ◇ (b ◇ (a ◇ a))) (p1e a))).symm).trans (((cg (fun t => t ◇ ((((a ◇ a) ◇ (a ◇ a)) ◇ (a ◇ a)) ◇ (b ◇ (a ◇ a)))) (cg (fun t => t ◇ b) ((h a a a).symm))).symm).trans (p25 (a ◇ a) b))
  have p27:=fun (a b:G)=>by
    exact ((cg (fun t => (a ◇ ((b ◇ b) ◇ b)) ◇ t) (cg (fun t => (b ◇ a) ◇ t) (p1b b))).symm).trans ((h ((b ◇ b) ◇ b) a b).symm)
  have p28:=fun (a b:G)=>by
    exact ((cg (fun t => (((a ◇ b) ◇ (b ◇ a)) ◇ ((b ◇ b) ◇ b)) ◇ t) (cg (fun t => t ◇ b) ((h b b a).symm))).symm).trans (pj b ((a ◇ b) ◇ (b ◇ a)))
  have p29:=fun (a b:G)=>by
    exact ((cg (fun t => t ◇ ((b ◇ (a ◇ (a ◇ a))) ◇ (a ◇ b))) (p1j a)).symm).trans ((h a (a ◇ (a ◇ a)) b).symm)
  have p2a:=fun (a b:G)=>by
    exact ((cg (fun t => t ◇ ((b ◇ a) ◇ ((a ◇ a) ◇ b))) (p1i a)).symm).trans (((cg (fun t => (((a ◇ a) ◇ (a ◇ a)) ◇ ((a ◇ a) ◇ (a ◇ a))) ◇ t) (cg (fun t => t ◇ ((a ◇ a) ◇ b)) (cg (fun t => b ◇ t) ((h a a a).symm)))).symm).trans (p29 (a ◇ a) b))
  have p2b:=fun (a b:G)=>by
    exact (((cg (fun t => t ◇ (((a ◇ b) ◇ (b ◇ a)) ◇ ((b ◇ b) ◇ b))) (cg (fun t => (((a ◇ b) ◇ (b ◇ a)) ◇ ((b ◇ b) ◇ b)) ◇ t) (p18 b))).trans (cg (fun t => t ◇ (((a ◇ b) ◇ (b ◇ a)) ◇ ((b ◇ b) ◇ b))) (p28 a b))).symm).trans ((((cg (fun t => t ◇ (((a ◇ b) ◇ (b ◇ a)) ◇ ((b ◇ b) ◇ b))) (cg (fun t => (((a ◇ b) ◇ (b ◇ a)) ◇ ((b ◇ b) ◇ b)) ◇ t) (cg (fun t => (b ◇ b) ◇ t) (p28 a b)))).symm).trans (p0 (b ◇ b) (((a ◇ b) ◇ (b ◇ a)) ◇ ((b ◇ b) ◇ b)))).trans ((cg (fun t => (b ◇ b) ◇ t) (p28 a b)).trans (p18 b)))
  have p2c:=fun (a b:G)=>by
    exact (((cg (fun t => (b ◇ b) ◇ t) (p24 a b)).symm).trans (((cg (fun t => t ◇ (b ◇ ((((a ◇ b) ◇ (b ◇ a)) ◇ ((b ◇ b) ◇ b)) ◇ b))) (p2b a b)).symm).trans (p1t (((a ◇ b) ◇ (b ◇ a)) ◇ ((b ◇ b) ◇ b)) b))).symm
  have p2d:=fun (a b:G)=>by
    exact ((((cg (fun t => ((b ◇ b) ◇ ((a ◇ b) ◇ (b ◇ a))) ◇ t) (pz b)).trans (cg (fun t => t ◇ ((b ◇ b) ◇ (b ◇ b))) (p1s b a))).trans (pz b)).symm).trans (((cg (fun t => ((b ◇ b) ◇ ((a ◇ b) ◇ (b ◇ a))) ◇ t) (cg (fun t => b ◇ t) (p2c a b))).symm).trans (pd b ((a ◇ b) ◇ (b ◇ a))))
  have p2e:=fun (a b c:G)=>by
    exact (((p2d a c).symm).trans (p2d b c)).symm
  have p2f:=fun (a b:G)=>by
    exact ((cg (fun t => t ◇ b) (p2d a b)).symm).trans (p1h b)
  have p2g:=fun (a b:G)=>by
    exact (((cg (fun t => t ◇ (b ◇ b)) (p2d a b)).symm).trans (p1d (b ◇ b))).trans (cg (fun t => (b ◇ b) ◇ t) (p1s b b))
  have p2h:=fun (a b:G)=>by
    exact ((cg (fun t => ((a ◇ b) ◇ (b ◇ a)) ◇ t) (p1i b)).symm).trans (((cg (fun t => t ◇ (((b ◇ b) ◇ (b ◇ b)) ◇ ((b ◇ b) ◇ (b ◇ b)))) (p2d a b)).symm).trans (p20 (b ◇ b) (b ◇ b)))
  have p2i:=fun (a b:G)=>by
    exact ((cg (fun t => t ◇ ((a ◇ b) ◇ (b ◇ a))) (p1i b)).symm).trans ((((cg (fun t => (((b ◇ b) ◇ (b ◇ b)) ◇ ((b ◇ b) ◇ (b ◇ b))) ◇ t) (p2d a b)).symm).trans (p1e (b ◇ b))).trans (p1e b))
  have p2j:=fun (a b c:G)=>by
    exact ((cg (fun t => (c ◇ b) ◇ t) (cg (fun t => c ◇ t) (cg (fun t => b ◇ t) (p2d a c)))).symm).trans (p1v b c)
  have p2k:=fun (a b:G)=>by
    exact ((((cg (fun t => ((a ◇ a) ◇ a) ◇ t) (pa a)).trans (pa a)).symm).trans (((cg (fun t => t ◇ (((a ◇ a) ◇ a) ◇ ((a ◇ a) ◇ a))) (pa a)).symm).trans (p2d b ((a ◇ a) ◇ a)))).symm
  have p2l:=fun (a b c d:G)=>by
    exact ((cg (fun t => (((c ◇ b) ◇ (a ◇ c)) ◇ (b ◇ a)) ◇ t) ((h a b c).symm)).symm).trans (p2e d ((c ◇ b) ◇ (a ◇ c)) (b ◇ a))
  have p2m:=fun (a b c d:G)=>by
    exact ((p2l a b c d).symm).trans (p2l a b c a)
  have p2n:=fun (a b:G)=>by
    exact ((cg (fun t => t ◇ (b ◇ (b ◇ (a ◇ (b ◇ a))))) (p0 a b)).symm).trans ((p2d (b ◇ (a ◇ (b ◇ a))) b).symm)
  have p2o:=fun (a b:G)=>by
    exact (((cg (fun t => t ◇ (b ◇ ((a ◇ a) ◇ a))) (pu a b)).symm).trans ((((cg (fun t => t ◇ (b ◇ ((a ◇ a) ◇ a))) (cg (fun t => (b ◇ ((a ◇ a) ◇ a)) ◇ t) (cg (fun t => (((a ◇ a) ◇ a) ◇ b) ◇ t) (p2k a b)))).symm).trans (p0 (((a ◇ a) ◇ a) ◇ b) (b ◇ ((a ◇ a) ◇ a)))).trans (((cg (fun t => (((a ◇ a) ◇ a) ◇ b) ◇ t) (p2m a (a ◇ a) ((b ◇ ((a ◇ a) ◇ a)) ◇ (((a ◇ a) ◇ a) ◇ b)) b)).trans (cg (fun t => (((a ◇ a) ◇ a) ◇ b) ◇ t) (cg (fun t => (a ◇ ((a ◇ a) ◇ a)) ◇ t) (p1b a)))).trans (cg (fun t => (((a ◇ a) ◇ a) ◇ b) ◇ t) (cg (fun t => t ◇ (a ◇ (a ◇ a))) (p19 a)))))).symm
  have p2p:=fun (a b c:G)=>by
    exact (((cg (fun t => t ◇ ((a ◇ a) ◇ ((a ◇ a) ◇ ((a ◇ a) ◇ (a ◇ a))))) (cg (fun t => t ◇ b) (p2g c a))).trans (cg (fun t => (((a ◇ a) ◇ a) ◇ b) ◇ t) (cg (fun t => (a ◇ a) ◇ t) (p1s a a)))).symm).trans ((((cg (fun t => t ◇ ((a ◇ a) ◇ ((a ◇ a) ◇ ((a ◇ a) ◇ (a ◇ a))))) (cg (fun t => t ◇ b) (cg (fun t => t ◇ (a ◇ a)) (p2d c a)))).symm).trans (p2o (a ◇ a) b)).trans ((cg (fun t => (((a ◇ a) ◇ (a ◇ a)) ◇ (a ◇ a)) ◇ t) (cg (fun t => b ◇ t) (p1e a))).trans (cg (fun t => t ◇ (b ◇ ((a ◇ a) ◇ a))) (p1e a))))
  have p2q:=fun (a b:G)=>by
    exact (((cg (fun t => t ◇ ((b ◇ b) ◇ (((a ◇ (b ◇ b)) ◇ (b ◇ a)) ◇ b))) (pt a b)).symm).trans ((p2d (((a ◇ (b ◇ b)) ◇ (b ◇ a)) ◇ b) (b ◇ b)).symm)).trans (p1i b)
  have p2r:=fun (a b:G)=>by
    exact (((cg (fun t => t ◇ ((a ◇ a) ◇ (((b ◇ a) ◇ ((a ◇ a) ◇ b)) ◇ a))) (p1w a b)).symm).trans ((p2d (((b ◇ a) ◇ ((a ◇ a) ◇ b)) ◇ a) (a ◇ a)).symm)).trans (p1i a)
  have p2s:=fun (a b c d:G)=>by
    exact (((cg (fun t => t ◇ ((c ◇ b) ◇ (b ◇ c))) (p2e a b c)).symm).trans (p2e d (b ◇ c) (c ◇ b))).trans (p2m b c ((d ◇ (c ◇ b)) ◇ ((c ◇ b) ◇ d)) d)
  have p2t:=fun (a b:G)=>by
    exact ((cg (fun t => ((a ◇ a) ◇ (((b ◇ a) ◇ ((a ◇ a) ◇ b)) ◇ a)) ◇ t) (p1h a)).symm).trans (((cg (fun t => ((a ◇ a) ◇ (((b ◇ a) ◇ ((a ◇ a) ◇ b)) ◇ a)) ◇ t) (cg (fun t => ((a ◇ a) ◇ (a ◇ a)) ◇ t) (p1w a b))).symm).trans (p20 (a ◇ a) (((b ◇ a) ◇ ((a ◇ a) ◇ b)) ◇ a)))
  have p2u:=fun (a b:G)=>by
    exact ((cg (fun t => t ◇ (b ◇ (((a ◇ b) ◇ (((b ◇ b) ◇ b) ◇ a)) ◇ b))) (px b a)).symm).trans ((p2d (((a ◇ b) ◇ (((b ◇ b) ◇ b) ◇ a)) ◇ b) b).symm)
  have p2v:=fun (a b:G)=>by
    exact ((cg (fun t => t ◇ (b ◇ (((a ◇ ((b ◇ b) ◇ b)) ◇ (b ◇ a)) ◇ b))) (p23 b a)).symm).trans ((p2d (((a ◇ ((b ◇ b) ◇ b)) ◇ (b ◇ a)) ◇ b) b).symm)
  have p2w:=fun (a b c d:G)=>by
    exact ((cg (fun t => ((b ◇ d) ◇ (d ◇ b)) ◇ t) (p2e a d c)).symm).trans (p2s b c d a)
  have p2x:=fun (a b c:G)=>by
    exact ((cg (fun t => ((b ◇ a) ◇ c) ◇ t) (cg (fun t => t ◇ (c ◇ (a ◇ b))) ((p2d a b).symm))).symm).trans ((h c (b ◇ a) (a ◇ b)).symm)
  have p2y:=fun (a b:G)=>by
    exact ((cg (fun t => ((b ◇ ((a ◇ b) ◇ ((b ◇ b) ◇ b))) ◇ (b ◇ a)) ◇ t) (cg (fun t => t ◇ a) (pd b (a ◇ b)))).symm).trans (pb a b b (b ◇ ((a ◇ b) ◇ ((b ◇ b) ◇ b))))
  have p2z:=fun (a b c:G)=>by
    exact ((cg (fun t => t ◇ ((c ◇ (((a ◇ (b ◇ b)) ◇ (b ◇ a)) ◇ b)) ◇ ((b ◇ b) ◇ c))) (pt a b)).symm).trans ((h (b ◇ b) (((a ◇ (b ◇ b)) ◇ (b ◇ a)) ◇ b) c).symm)
  have p30:=fun (a b:G)=>by
    exact ((((cg (fun t => t ◇ (b ◇ b)) (p2q a b)).trans (py b)).symm).trans (((cg (fun t => (b ◇ ((b ◇ b) ◇ (((a ◇ (b ◇ b)) ◇ (b ◇ a)) ◇ b))) ◇ t) (p2z a b (b ◇ b))).symm).trans (p2j b ((b ◇ b) ◇ (((a ◇ (b ◇ b)) ◇ (b ◇ a)) ◇ b)) b))).symm
  have p31:=fun (a b:G)=>by
    exact (((((((cg (fun t => t ◇ (((((a ◇ (b ◇ b)) ◇ (b ◇ a)) ◇ b) ◇ (b ◇ b)) ◇ (((a ◇ (b ◇ b)) ◇ (b ◇ a)) ◇ b))) (cg (fun t => t ◇ (b ◇ b)) (cg (fun t => (b ◇ b) ◇ t) (cg (fun t => ((((a ◇ (b ◇ b)) ◇ (b ◇ a)) ◇ b) ◇ (b ◇ b)) ◇ t) (p1e b))))).trans (cg (fun t => t ◇ (((((a ◇ (b ◇ b)) ◇ (b ◇ a)) ◇ b) ◇ (b ◇ b)) ◇ (((a ◇ (b ◇ b)) ◇ (b ◇ a)) ◇ b))) (cg (fun t => t ◇ (b ◇ b)) (cg (fun t => (b ◇ b) ◇ t) (cg (fun t => t ◇ ((b ◇ b) ◇ b)) (pt a b)))))).trans (cg (fun t => t ◇ (((((a ◇ (b ◇ b)) ◇ (b ◇ a)) ◇ b) ◇ (b ◇ b)) ◇ (((a ◇ (b ◇ b)) ◇ (b ◇ a)) ◇ b))) (cg (fun t => t ◇ (b ◇ b)) (cg (fun t => (b ◇ b) ◇ t) (p19 b))))).trans (cg (fun t => (((b ◇ b) ◇ b) ◇ (b ◇ b)) ◇ t) (cg (fun t => t ◇ (((a ◇ (b ◇ b)) ◇ (b ◇ a)) ◇ b)) (pt a b)))).trans (cg (fun t => t ◇ (b ◇ (((a ◇ (b ◇ b)) ◇ (b ◇ a)) ◇ b))) (p4 b))).trans (p21 a b)).symm).trans ((((cg (fun t => t ◇ (((((a ◇ (b ◇ b)) ◇ (b ◇ a)) ◇ b) ◇ (b ◇ b)) ◇ (((a ◇ (b ◇ b)) ◇ (b ◇ a)) ◇ b))) (cg (fun t => ((b ◇ b) ◇ (((((a ◇ (b ◇ b)) ◇ (b ◇ a)) ◇ b) ◇ (b ◇ b)) ◇ (((b ◇ b) ◇ (b ◇ b)) ◇ (b ◇ b)))) ◇ t) (p30 a b))).symm).trans (p2y (((a ◇ (b ◇ b)) ◇ (b ◇ a)) ◇ b) (b ◇ b))).trans (p30 a b))
  have p32:=fun (a b c:G)=>by
    exact ((cg (fun t => t ◇ ((c ◇ (a ◇ b)) ◇ ((b ◇ a) ◇ c))) ((p2d a b).symm)).symm).trans ((h (b ◇ a) (a ◇ b) c).symm)
  have p33:=fun (a b:G)=>by
    exact ((cg (fun t => ((b ◇ (b ◇ a)) ◇ (b ◇ (a ◇ b))) ◇ t) (p32 a b b)).symm).trans (p2x (b ◇ a) b (b ◇ (a ◇ b)))
  have p34:=fun (a b:G)=>by
    exact ((((((cg (fun t => t ◇ (b ◇ ((a ◇ b) ◇ (((b ◇ b) ◇ b) ◇ a)))) (cg (fun t => t ◇ (b ◇ (((a ◇ b) ◇ (((b ◇ b) ◇ b) ◇ a)) ◇ b))) (p19 b))).trans (cg (fun t => (b ◇ (b ◇ (((a ◇ b) ◇ (((b ◇ b) ◇ b) ◇ a)) ◇ b))) ◇ t) (p1u b a))).trans (cg (fun t => t ◇ ((b ◇ b) ◇ b)) (p2u a b))).trans (p1n b)).symm).trans (((cg (fun t => t ◇ (b ◇ ((a ◇ b) ◇ (((b ◇ b) ◇ b) ◇ a)))) (cg (fun t => t ◇ (b ◇ (((a ◇ b) ◇ (((b ◇ b) ◇ b) ◇ a)) ◇ b))) (cg (fun t => b ◇ t) (p1u b a)))).symm).trans (p33 ((a ◇ b) ◇ (((b ◇ b) ◇ b) ◇ a)) b))).symm
  have p35:=fun (a b:G)=>by
    exact (((((cg (fun t => t ◇ (((a ◇ b) ◇ (((b ◇ b) ◇ b) ◇ a)) ◇ b)) (cg (fun t => ((b ◇ b) ◇ (b ◇ b)) ◇ t) (px b a))).trans (cg (fun t => t ◇ (((a ◇ b) ◇ (((b ◇ b) ◇ b) ◇ a)) ◇ b)) (p1h b))).trans (p34 a b)).symm).trans (((cg (fun t => t ◇ (((a ◇ b) ◇ (((b ◇ b) ◇ b) ◇ a)) ◇ b)) (cg (fun t => t ◇ ((((a ◇ b) ◇ (((b ◇ b) ◇ b) ◇ a)) ◇ b) ◇ b)) (p34 a b))).symm).trans (p2f b (((a ◇ b) ◇ (((b ◇ b) ◇ b) ◇ a)) ◇ b)))).symm
  have p36:=fun (a b:G)=>by
    exact (((((cg (fun t => (b ◇ ((a ◇ b) ◇ (((b ◇ b) ◇ b) ◇ a))) ◇ t) (p1s b b)).trans (cg (fun t => t ◇ b) (p1u b a))).trans (p1b b)).symm).trans (((cg (fun t => (b ◇ ((a ◇ b) ◇ (((b ◇ b) ◇ b) ◇ a))) ◇ t) (cg (fun t => (b ◇ b) ◇ t) (p35 a b))).symm).trans (p20 b ((a ◇ b) ◇ (((b ◇ b) ◇ b) ◇ a))))).symm
  have p37:=fun (a b:G)=>by
    exact ((cg (fun t => (b ◇ (a ◇ (a ◇ a))) ◇ t) (cg (fun t => (((a ◇ a) ◇ a) ◇ b) ◇ t) (p1m a))).symm).trans ((h (a ◇ (a ◇ a)) b ((a ◇ a) ◇ a)).symm)
  have p38:=fun (a b c:G)=>by
    exact ((cg (fun t => t ◇ ((c ◇ (((b ◇ a) ◇ ((a ◇ a) ◇ b)) ◇ a)) ◇ ((a ◇ a) ◇ c))) (p1w a b)).symm).trans ((h (a ◇ a) (((b ◇ a) ◇ ((a ◇ a) ◇ b)) ◇ a) c).symm)
  have p39:=fun (a b:G)=>by
    exact ((((cg (fun t => t ◇ (b ◇ b)) (p2r b a)).trans (py b)).symm).trans (((cg (fun t => (b ◇ ((b ◇ b) ◇ (((a ◇ b) ◇ ((b ◇ b) ◇ a)) ◇ b))) ◇ t) (p38 b a (b ◇ b))).symm).trans (p2j b ((b ◇ b) ◇ (((a ◇ b) ◇ ((b ◇ b) ◇ a)) ◇ b)) b))).symm
  have p3a:=fun (a b:G)=>by
    exact (((cg (fun t => t ◇ a) (p39 b a)).symm).trans (p2t a b)).symm
  have p3b:=fun (a b:G)=>by
    exact (((((cg (fun t => ((b ◇ (b ◇ b)) ◇ ((a ◇ b) ◇ ((b ◇ b) ◇ a))) ◇ t) (pa b)).trans (cg (fun t => t ◇ ((b ◇ b) ◇ b)) (p2a b a))).trans (p18 b)).symm).trans (((cg (fun t => ((b ◇ (b ◇ b)) ◇ ((a ◇ b) ◇ ((b ◇ b) ◇ a))) ◇ t) (cg (fun t => ((b ◇ b) ◇ b) ◇ t) (p3a b a))).symm).trans (p25 b ((a ◇ b) ◇ ((b ◇ b) ◇ a))))).symm
  have p3c:=fun (a b:G)=>by
    exact (((cg (fun t => (b ◇ (a ◇ (a ◇ a))) ◇ t) (cg (fun t => t ◇ b) (p1c a))).symm).trans (p3b b (a ◇ (a ◇ a)))).trans (p1c a)
  have p3d:=fun (a b:G)=>by
    exact ((((cg (fun t => t ◇ ((a ◇ b) ◇ (b ◇ (a ◇ (a ◇ a))))) (p3c a b)).symm).trans ((p2d (b ◇ (a ◇ (a ◇ a))) (a ◇ b)).symm)).trans (p2m b a (((a ◇ b) ◇ (a ◇ b)) ◇ ((a ◇ b) ◇ (a ◇ b))) (a ◇ b))).symm
  have p3e:=fun (a b c:G)=>by
    exact (((p3d a c).symm).trans (p2e b c (a ◇ c))).symm
  have p3f:=fun (a b c:G)=>by
    exact (p3e a b c).trans ((p3e a a c).symm)
  have p3g:=fun (a b c:G)=>by
    exact ((cg (fun t => (c ◇ b) ◇ t) (cg (fun t => t ◇ (b ◇ (((a ◇ ((c ◇ c) ◇ c)) ◇ (c ◇ a)) ◇ c))) (p23 c a))).symm).trans ((h b c (((a ◇ ((c ◇ c) ◇ c)) ◇ (c ◇ a)) ◇ c)).symm)
  have p3h:=fun (a b:G)=>by
    exact (((cg (fun t => t ◇ ((a ◇ ((b ◇ b) ◇ b)) ◇ (b ◇ a))) (cg (fun t => b ◇ t) (cg (fun t => b ◇ t) (p1b b)))).trans (cg (fun t => t ◇ ((a ◇ ((b ◇ b) ◇ b)) ◇ (b ◇ a))) (p1k b))).symm).trans ((((cg (fun t => (b ◇ (b ◇ (((b ◇ b) ◇ b) ◇ b))) ◇ t) (p5 b ((b ◇ b) ◇ b) a b)).symm).trans (p3g a (b ◇ (((b ◇ b) ◇ b) ◇ b)) b)).trans (cg (fun t => b ◇ t) (p1b b)))
  have p3i:=fun (a b:G)=>by
    exact ((((((cg (fun t => t ◇ (b ◇ ((a ◇ ((b ◇ b) ◇ b)) ◇ (b ◇ a)))) (cg (fun t => t ◇ (b ◇ (((a ◇ ((b ◇ b) ◇ b)) ◇ (b ◇ a)) ◇ b))) (p1k b))).trans (cg (fun t => (b ◇ (b ◇ (((a ◇ ((b ◇ b) ◇ b)) ◇ (b ◇ a)) ◇ b))) ◇ t) (p3h a b))).trans (cg (fun t => t ◇ (b ◇ (b ◇ (b ◇ b)))) (p2v a b))).trans (p1q b)).symm).trans (((cg (fun t => t ◇ (b ◇ ((a ◇ ((b ◇ b) ◇ b)) ◇ (b ◇ a)))) (cg (fun t => t ◇ (b ◇ (((a ◇ ((b ◇ b) ◇ b)) ◇ (b ◇ a)) ◇ b))) (cg (fun t => b ◇ t) (p3h a b)))).symm).trans (p33 ((a ◇ ((b ◇ b) ◇ b)) ◇ (b ◇ a)) b))).symm
  have p3j:=fun (a b:G)=>by
    exact (((((cg (fun t => t ◇ (((a ◇ ((b ◇ b) ◇ b)) ◇ (b ◇ a)) ◇ b)) (cg (fun t => ((b ◇ b) ◇ (b ◇ b)) ◇ t) (p23 b a))).trans (cg (fun t => t ◇ (((a ◇ ((b ◇ b) ◇ b)) ◇ (b ◇ a)) ◇ b)) (p1h b))).trans (p3i a b)).symm).trans (((cg (fun t => t ◇ (((a ◇ ((b ◇ b) ◇ b)) ◇ (b ◇ a)) ◇ b)) (cg (fun t => t ◇ ((((a ◇ ((b ◇ b) ◇ b)) ◇ (b ◇ a)) ◇ b) ◇ b)) (p3i a b))).symm).trans (p2f b (((a ◇ ((b ◇ b) ◇ b)) ◇ (b ◇ a)) ◇ b)))).symm
  have p3k:=fun (a b:G)=>by
    exact (((((cg (fun t => (b ◇ ((a ◇ ((b ◇ b) ◇ b)) ◇ (b ◇ a))) ◇ t) (p1s b b)).trans (cg (fun t => t ◇ b) (p3h a b))).trans (p0 b b)).symm).trans (((cg (fun t => (b ◇ ((a ◇ ((b ◇ b) ◇ b)) ◇ (b ◇ a))) ◇ t) (cg (fun t => (b ◇ b) ◇ t) (p3j a b))).symm).trans (p20 b ((a ◇ ((b ◇ b) ◇ b)) ◇ (b ◇ a))))).symm
  have p3l:=fun (a b:G)=>by
    exact (((((((cg (fun t => t ◇ (((b ◇ b) ◇ b) ◇ (((b ◇ b) ◇ (b ◇ b)) ◇ ((b ◇ b) ◇ (b ◇ b))))) (cg (fun t => b ◇ t) (cg (fun t => t ◇ ((b ◇ b) ◇ a)) (cg (fun t => a ◇ t) (p1e b))))).trans (cg (fun t => (b ◇ ((a ◇ ((b ◇ b) ◇ b)) ◇ ((b ◇ b) ◇ a))) ◇ t) (cg (fun t => ((b ◇ b) ◇ b) ◇ t) (p1i b)))).trans (cg (fun t => (b ◇ ((a ◇ ((b ◇ b) ◇ b)) ◇ ((b ◇ b) ◇ a))) ◇ t) (p1p b))).trans (cg (fun t => t ◇ ((b ◇ b) ◇ (b ◇ b))) (pf b a))).trans (p1s b b)).symm).trans ((((cg (fun t => (b ◇ ((a ◇ (((b ◇ b) ◇ (b ◇ b)) ◇ (b ◇ b))) ◇ ((b ◇ b) ◇ a))) ◇ t) (cg (fun t => ((b ◇ b) ◇ b) ◇ t) (p3j a (b ◇ b)))).symm).trans (p26 b ((a ◇ (((b ◇ b) ◇ (b ◇ b)) ◇ (b ◇ b))) ◇ ((b ◇ b) ◇ a)))).trans (cg (fun t => t ◇ ((b ◇ b) ◇ a)) (cg (fun t => a ◇ t) (p1e b))))).symm
  have p3m:=fun (a b:G)=>by
    exact ((cg (fun t => t ◇ (a ◇ ((b ◇ b) ◇ b))) (pj b a)).symm).trans ((((cg (fun t => t ◇ (a ◇ ((b ◇ b) ◇ b))) (cg (fun t => (a ◇ ((b ◇ b) ◇ b)) ◇ t) (cg (fun t => ((b ◇ b) ◇ a) ◇ t) (p3l a b)))).symm).trans (p0 ((b ◇ b) ◇ a) (a ◇ ((b ◇ b) ◇ b)))).trans (cg (fun t => ((b ◇ b) ◇ a) ◇ t) (p3l a b)))
  have p3n:=fun (a b:G)=>by
    exact (((cg (fun t => t ◇ (a ◇ ((b ◇ b) ◇ b))) (p27 a b)).trans (p3m a b)).symm).trans ((((cg (fun t => t ◇ (a ◇ ((b ◇ b) ◇ b))) (cg (fun t => (a ◇ ((b ◇ b) ◇ b)) ◇ t) (cg (fun t => (b ◇ a) ◇ t) (p3k a b)))).symm).trans (p0 (b ◇ a) (a ◇ ((b ◇ b) ◇ b)))).trans (cg (fun t => (b ◇ a) ◇ t) (p3k a b)))
  have p3o:=fun (a b c:G)=>by
    exact (p2p b c a).trans (p3m c b)
  have p3p:=fun (a b c:G)=>by
    exact (((cg (fun t => t ◇ (b ◇ b)) (cg (fun t => t ◇ c) (p2d a b))).symm).trans (p3n c (b ◇ b))).trans (cg (fun t => ((b ◇ b) ◇ c) ◇ t) (p1s b b))
  have p3q:=fun (a b:G)=>by
    exact ((cg (fun t => (((a ◇ a) ◇ a) ◇ b) ◇ t) (p3m b a)).symm).trans (ph a b)
  have p3r:=fun (a b:G)=>by
    exact ((((p3o ((((b ◇ b) ◇ b) ◇ ((a ◇ (b ◇ (b ◇ b))) ◇ ((b ◇ b) ◇ a))) ◇ ((b ◇ b) ◇ b)) b ((a ◇ (b ◇ (b ◇ b))) ◇ ((b ◇ b) ◇ a))).trans (cg (fun t => t ◇ b) (p12 b a))).symm).trans (((cg (fun t => (((b ◇ b) ◇ b) ◇ ((a ◇ (b ◇ (b ◇ b))) ◇ ((b ◇ b) ◇ a))) ◇ t) (cg (fun t => t ◇ b) (p12 b a))).symm).trans (p3q b ((a ◇ (b ◇ (b ◇ b))) ◇ ((b ◇ b) ◇ a))))).symm
  have p3s:=fun (a b c:G)=>by
    exact ((cg (fun t => t ◇ (((a ◇ a) ◇ (a ◇ a)) ◇ b)) (cg (fun t => b ◇ t) (p1s a c))).symm).trans ((((cg (fun t => t ◇ (((a ◇ a) ◇ (a ◇ a)) ◇ b)) (cg (fun t => b ◇ t) (cg (fun t => (a ◇ a) ◇ t) (p2d c a)))).symm).trans (p3r b (a ◇ a))).trans (p1e a))
  have p3t:=fun (a b c:G)=>by
    exact ((cg (fun t => t ◇ (((a ◇ b) ◇ (b ◇ a)) ◇ c)) (cg (fun t => c ◇ t) (p1s b b))).symm).trans ((((cg (fun t => (c ◇ ((b ◇ b) ◇ ((b ◇ b) ◇ (b ◇ b)))) ◇ t) (cg (fun t => t ◇ c) (p2d a b))).symm).trans (p3r c (b ◇ b))).trans (p1e b))
  have p3u:=fun (a b c:G)=>by
    exact (((((cg (fun t => (c ◇ ((a ◇ b) ◇ (b ◇ a))) ◇ t) (cg (fun t => t ◇ c) (cg (fun t => t ◇ (((a ◇ b) ◇ (b ◇ a)) ◇ ((a ◇ b) ◇ (b ◇ a)))) (p1m b)))).trans (cg (fun t => (c ◇ ((a ◇ b) ◇ (b ◇ a))) ◇ t) (cg (fun t => t ◇ c) (cg (fun t => (b ◇ (b ◇ b)) ◇ t) (p2w a a b b))))).trans (cg (fun t => (c ◇ ((a ◇ b) ◇ (b ◇ a))) ◇ t) (cg (fun t => t ◇ c) (cg (fun t => (b ◇ (b ◇ b)) ◇ t) (p1m b))))).trans (cg (fun t => (c ◇ ((a ◇ b) ◇ (b ◇ a))) ◇ t) (cg (fun t => t ◇ c) (p1c b)))).symm).trans ((((cg (fun t => (c ◇ ((a ◇ b) ◇ (b ◇ a))) ◇ t) (cg (fun t => t ◇ c) (cg (fun t => t ◇ (((a ◇ b) ◇ (b ◇ a)) ◇ ((a ◇ b) ◇ (b ◇ a)))) (p2w a a b b)))).symm).trans (p3s ((a ◇ b) ◇ (b ◇ a)) c a)).trans (((cg (fun t => t ◇ ((a ◇ b) ◇ (b ◇ a))) (p2w a a b b)).trans (cg (fun t => t ◇ ((a ◇ b) ◇ (b ◇ a))) (p1m b))).trans (p2i a b)))
  have p3v:=fun (a b:G)=>by
    exact (((cg (fun t => t ◇ ((b ◇ b) ◇ b)) (p3u b a b)).symm).trans (((cg (fun t => ((b ◇ ((b ◇ a) ◇ (a ◇ b))) ◇ (a ◇ b)) ◇ t) (p3u a b ((b ◇ a) ◇ (a ◇ b)))).symm).trans (p3t (b ◇ a) (a ◇ b) (b ◇ ((b ◇ a) ◇ (a ◇ b)))))).symm
  have p3w:=fun (a b c:G)=>by
    exact ((cg (fun t => t ◇ (((a ◇ b) ◇ (b ◇ a)) ◇ c)) (cg (fun t => c ◇ t) (p1m b))).symm).trans ((((cg (fun t => t ◇ (((a ◇ b) ◇ (b ◇ a)) ◇ c)) (cg (fun t => c ◇ t) (p2w a a b b))).symm).trans (p31 c ((a ◇ b) ◇ (b ◇ a)))).trans ((p2w a a b b).trans (p1m b)))
  have p3x:=fun (a b c:G)=>by
    exact ((cg (fun t => (c ◇ (a ◇ b)) ◇ t) (cg (fun t => (((b ◇ b) ◇ a) ◇ c) ◇ t) (p3b a b))).symm).trans ((h (a ◇ b) c ((b ◇ b) ◇ a)).symm)
  have p3y:=fun (a b:G)=>by
    exact ((cg (fun t => (((b ◇ b) ◇ b) ◇ (b ◇ (a ◇ (b ◇ a)))) ◇ t) (cg (fun t => t ◇ (a ◇ (b ◇ a))) (p19 b))).symm).trans (pi a ((b ◇ b) ◇ b) b)
  have p3z:=fun (a b c:G)=>by
    exact (((cg (fun t => (c ◇ ((a ◇ b) ◇ (b ◇ a))) ◇ t) (cg (fun t => t ◇ c) (cg (fun t => t ◇ ((a ◇ b) ◇ (b ◇ a))) (p1m b)))).trans (cg (fun t => (c ◇ ((a ◇ b) ◇ (b ◇ a))) ◇ t) (cg (fun t => t ◇ c) (p2i a b)))).symm).trans ((((cg (fun t => (c ◇ ((a ◇ b) ◇ (b ◇ a))) ◇ t) (cg (fun t => t ◇ c) (cg (fun t => t ◇ ((a ◇ b) ◇ (b ◇ a))) (p2w a a b b)))).symm).trans (p36 c ((a ◇ b) ◇ (b ◇ a)))).trans (((cg (fun t => ((a ◇ b) ◇ (b ◇ a)) ◇ t) (p2w a a b b)).trans (cg (fun t => ((a ◇ b) ◇ (b ◇ a)) ◇ t) (p1m b))).trans (p2h a b)))
  have p40:=fun (a b:G)=>by
    exact ((cg (fun t => t ◇ (((a ◇ a) ◇ (a ◇ a)) ◇ b)) (cg (fun t => b ◇ t) (p1o a))).symm).trans ((((cg (fun t => t ◇ (((a ◇ a) ◇ (a ◇ a)) ◇ b)) (cg (fun t => b ◇ t) (cg (fun t => t ◇ ((a ◇ a) ◇ (a ◇ a))) (p1i a)))).symm).trans (p3k b ((a ◇ a) ◇ (a ◇ a)))).trans ((cg (fun t => ((a ◇ a) ◇ (a ◇ a)) ◇ t) (p1i a)).trans (p1f a)))
  have p41:=fun (a b:G)=>by
    exact ((((((cg (fun t => t ◇ ((((a ◇ a) ◇ (a ◇ a)) ◇ b) ◇ (a ◇ a))) (cg (fun t => t ◇ (b ◇ ((a ◇ a) ◇ a))) (p3v ((a ◇ a) ◇ (a ◇ a)) b))).trans (cg (fun t => t ◇ ((((a ◇ a) ◇ (a ◇ a)) ◇ b) ◇ (a ◇ a))) (cg (fun t => t ◇ (b ◇ ((a ◇ a) ◇ a))) (cg (fun t => t ◇ ((b ◇ b) ◇ b)) (cg (fun t => t ◇ ((a ◇ a) ◇ (a ◇ a))) (p1i a)))))).trans (cg (fun t => t ◇ ((((a ◇ a) ◇ (a ◇ a)) ◇ b) ◇ (a ◇ a))) (cg (fun t => t ◇ (b ◇ ((a ◇ a) ◇ a))) (cg (fun t => t ◇ ((b ◇ b) ◇ b)) (p1o a))))).trans (cg (fun t => ((((a ◇ a) ◇ a) ◇ ((b ◇ b) ◇ b)) ◇ (b ◇ ((a ◇ a) ◇ a))) ◇ t) (p3p a a b))).trans (cg (fun t => t ◇ (((a ◇ a) ◇ b) ◇ a)) (p3k ((a ◇ a) ◇ a) b))).symm).trans (((cg (fun t => ((((((a ◇ a) ◇ (a ◇ a)) ◇ b) ◇ (((a ◇ a) ◇ (a ◇ a)) ◇ b)) ◇ (((a ◇ a) ◇ (a ◇ a)) ◇ b)) ◇ (b ◇ ((a ◇ a) ◇ a))) ◇ t) (cg (fun t => (((a ◇ a) ◇ (a ◇ a)) ◇ b) ◇ t) (p40 a b))).symm).trans (p1t (b ◇ ((a ◇ a) ◇ a)) (((a ◇ a) ◇ (a ◇ a)) ◇ b)))
  have p42:=fun (a b c:G)=>by
    exact (((cg (fun t => t ◇ (((a ◇ b) ◇ (b ◇ a)) ◇ c)) (cg (fun t => c ◇ t) (cg (fun t => t ◇ ((a ◇ b) ◇ (b ◇ a))) (p1m b)))).trans (cg (fun t => t ◇ (((a ◇ b) ◇ (b ◇ a)) ◇ c)) (cg (fun t => c ◇ t) (p2i a b)))).symm).trans ((((cg (fun t => t ◇ (((a ◇ b) ◇ (b ◇ a)) ◇ c)) (cg (fun t => c ◇ t) (cg (fun t => t ◇ ((a ◇ b) ◇ (b ◇ a))) (p2w a a b b)))).symm).trans (p3k c ((a ◇ b) ◇ (b ◇ a)))).trans (((cg (fun t => ((a ◇ b) ◇ (b ◇ a)) ◇ t) (p2w a a b b)).trans (cg (fun t => ((a ◇ b) ◇ (b ◇ a)) ◇ t) (p1m b))).trans (p2h a b)))
  have p43:=fun (a b:G)=>by
    exact ((((cg (fun t => t ◇ (b ◇ b)) (cg (fun t => (((b ◇ b) ◇ b) ◇ ((b ◇ a) ◇ (a ◇ b))) ◇ t) (p3v a b))).trans (cg (fun t => t ◇ (b ◇ b)) (p3z b a ((b ◇ b) ◇ b)))).symm).trans (((cg (fun t => ((((b ◇ b) ◇ b) ◇ ((b ◇ a) ◇ (a ◇ b))) ◇ (((a ◇ b) ◇ (a ◇ b)) ◇ (a ◇ b))) ◇ t) (p3z a b ((b ◇ a) ◇ (a ◇ b)))).symm).trans (p42 (b ◇ a) (a ◇ b) (((b ◇ b) ◇ b) ◇ ((b ◇ a) ◇ (a ◇ b)))))).symm
  have p44:=fun (a b:G)=>by
    exact (((cg (fun t => t ◇ (((b ◇ b) ◇ b) ◇ (b ◇ (a ◇ (b ◇ a))))) (cg (fun t => (((b ◇ b) ◇ b) ◇ (b ◇ (a ◇ (b ◇ a)))) ◇ t) (pc a b))).trans (cg (fun t => t ◇ (((b ◇ b) ◇ b) ◇ (b ◇ (a ◇ (b ◇ a))))) (p3y a b))).symm).trans ((((cg (fun t => t ◇ (((b ◇ b) ◇ b) ◇ (b ◇ (a ◇ (b ◇ a))))) (cg (fun t => (((b ◇ b) ◇ b) ◇ (b ◇ (a ◇ (b ◇ a)))) ◇ t) (cg (fun t => (b ◇ (a ◇ (b ◇ a))) ◇ t) (p3y a b)))).symm).trans (p0 (b ◇ (a ◇ (b ◇ a))) (((b ◇ b) ◇ b) ◇ (b ◇ (a ◇ (b ◇ a)))))).trans ((cg (fun t => (b ◇ (a ◇ (b ◇ a))) ◇ t) (p3y a b)).trans (pc a b)))
  have p45:=fun (a b:G)=>by
    exact ((((cg (fun t => (b ◇ (a ◇ (b ◇ a))) ◇ t) (p3y a b)).trans (pc a b)).symm).trans ((((cg (fun t => t ◇ ((((b ◇ b) ◇ b) ◇ (b ◇ (a ◇ (b ◇ a)))) ◇ (b ◇ (a ◇ (b ◇ a))))) (p44 a b)).symm).trans ((p2d (b ◇ (a ◇ (b ◇ a))) (((b ◇ b) ◇ b) ◇ (b ◇ (a ◇ (b ◇ a))))).symm)).trans (((((((((cg (fun t => t ◇ ((((b ◇ b) ◇ b) ◇ (b ◇ (a ◇ (b ◇ a)))) ◇ (((b ◇ b) ◇ b) ◇ (b ◇ (a ◇ (b ◇ a)))))) (p43 ((b ◇ b) ◇ b) (b ◇ (a ◇ (b ◇ a))))).trans (cg (fun t => t ◇ ((((b ◇ b) ◇ b) ◇ (b ◇ (a ◇ (b ◇ a)))) ◇ (((b ◇ b) ◇ b) ◇ (b ◇ (a ◇ (b ◇ a)))))) (cg (fun t => t ◇ ((b ◇ (a ◇ (b ◇ a))) ◇ (b ◇ (a ◇ (b ◇ a))))) (pa b)))).trans (cg (fun t => t ◇ ((((b ◇ b) ◇ b) ◇ (b ◇ (a ◇ (b ◇ a)))) ◇ (((b ◇ b) ◇ b) ◇ (b ◇ (a ◇ (b ◇ a)))))) (cg (fun t => ((b ◇ b) ◇ b) ◇ t) (pc a b)))).trans (cg (fun t => (((b ◇ b) ◇ b) ◇ (b ◇ (a ◇ (b ◇ a)))) ◇ t) (p43 ((b ◇ b) ◇ b) (b ◇ (a ◇ (b ◇ a)))))).trans (cg (fun t => (((b ◇ b) ◇ b) ◇ (b ◇ (a ◇ (b ◇ a)))) ◇ t) (cg (fun t => t ◇ ((b ◇ (a ◇ (b ◇ a))) ◇ (b ◇ (a ◇ (b ◇ a))))) (pa b)))).trans (cg (fun t => (((b ◇ b) ◇ b) ◇ (b ◇ (a ◇ (b ◇ a)))) ◇ t) (cg (fun t => ((b ◇ b) ◇ b) ◇ t) (pc a b)))).trans (p43 ((b ◇ b) ◇ b) (b ◇ (a ◇ (b ◇ a))))).trans (cg (fun t => t ◇ ((b ◇ (a ◇ (b ◇ a))) ◇ (b ◇ (a ◇ (b ◇ a))))) (pa b))).trans (cg (fun t => ((b ◇ b) ◇ b) ◇ t) (pc a b))))).symm
  have p46:=fun (a b:G)=>by
    exact ((((((p43 (b ◇ (a ◇ (b ◇ a))) (b ◇ (b ◇ b))).trans (cg (fun t => ((b ◇ (a ◇ (b ◇ a))) ◇ (b ◇ (a ◇ (b ◇ a)))) ◇ t) (p1c b))).trans (cg (fun t => t ◇ b) (pc a b))).trans (p0 a b)).symm).trans (((cg (fun t => ((b ◇ (a ◇ (b ◇ a))) ◇ (b ◇ (b ◇ b))) ◇ t) (cg (fun t => t ◇ (b ◇ (b ◇ b))) (p45 a b))).symm).trans (p37 b (b ◇ (a ◇ (b ◇ a)))))).symm
  have p47:=fun (a b c:G)=>by
    exact (((p46 a c).symm).trans (p46 b c)).symm
  have p48:=fun (a b c:G)=>by
    exact (((p1s a c).symm).trans (((cg (fun t => (a ◇ a) ◇ t) (p2d c a)).symm).trans (p46 b (a ◇ a)))).symm
  have p49:=fun (a b:G)=>by
    exact (((((((cg (fun t => ((b ◇ (a ◇ (b ◇ a))) ◇ (b ◇ (a ◇ (b ◇ a)))) ◇ t) (cg (fun t => ((b ◇ b) ◇ b) ◇ t) (cg (fun t => ((b ◇ b) ◇ b) ◇ t) (cg (fun t => (b ◇ (a ◇ (b ◇ a))) ◇ t) (p45 a b))))).trans (cg (fun t => ((b ◇ (a ◇ (b ◇ a))) ◇ (b ◇ (a ◇ (b ◇ a)))) ◇ t) (cg (fun t => ((b ◇ b) ◇ b) ◇ t) (cg (fun t => ((b ◇ b) ◇ b) ◇ t) (pc a b))))).trans (cg (fun t => ((b ◇ (a ◇ (b ◇ a))) ◇ (b ◇ (a ◇ (b ◇ a)))) ◇ t) (cg (fun t => ((b ◇ b) ◇ b) ◇ t) (p45 a b)))).trans (cg (fun t => ((b ◇ (a ◇ (b ◇ a))) ◇ (b ◇ (a ◇ (b ◇ a)))) ◇ t) (p45 a b))).trans (cg (fun t => t ◇ (b ◇ (a ◇ (b ◇ a)))) (pc a b))).trans (pc a b)).symm).trans ((((cg (fun t => t ◇ (((b ◇ b) ◇ b) ◇ (((b ◇ b) ◇ b) ◇ ((b ◇ (a ◇ (b ◇ a))) ◇ (((b ◇ b) ◇ b) ◇ (b ◇ (a ◇ (b ◇ a)))))))) (cg (fun t => (b ◇ (a ◇ (b ◇ a))) ◇ t) (p45 a b))).symm).trans (p2n (b ◇ (a ◇ (b ◇ a))) ((b ◇ b) ◇ b))).trans (((cg (fun t => t ◇ (((b ◇ b) ◇ b) ◇ ((b ◇ b) ◇ b))) (pa b)).trans (cg (fun t => ((b ◇ b) ◇ b) ◇ t) (pa b))).trans (pa b)))
  have p4a:=fun (a b:G)=>by
    exact ((cg (fun t => (a ◇ b) ◇ t) ((p46 b a).symm)).symm).trans ((p46 (a ◇ b) b).symm)
  have p4b:=fun (a b:G)=>by
    exact (((((cg (fun t => (b ◇ (b ◇ b)) ◇ t) (cg (fun t => t ◇ (a ◇ (a ◇ a))) (cg (fun t => t ◇ b) (p1s a a)))).trans (cg (fun t => (b ◇ (b ◇ b)) ◇ t) (p4a a b))).trans (p1c b)).symm).trans ((((cg (fun t => (b ◇ (b ◇ b)) ◇ t) (cg (fun t => t ◇ (a ◇ (a ◇ a))) (cg (fun t => t ◇ b) (p4a a (a ◇ a))))).symm).trans (p41 (a ◇ (a ◇ a)) b)).trans ((cg (fun t => b ◇ t) (cg (fun t => t ◇ (a ◇ (a ◇ a))) (p1c a))).trans (cg (fun t => b ◇ t) (p49 a a))))).symm
  have p4c:=fun (a b c:G)=>by
    exact ((cg (fun t => (b ◇ c) ◇ t) (p47 a c b)).symm).trans ((p46 (b ◇ c) c).symm)
  have p4d:=fun (a b c d:G)=>by
    exact ((cg (fun t => ((c ◇ b) ◇ (a ◇ c)) ◇ t) ((h a b c).symm)).symm).trans (p47 d ((c ◇ b) ◇ (a ◇ c)) (b ◇ a))
  have p4e:=fun (a b c d:G)=>by
    exact ((p4d a b c d).symm).trans (p4d a b c a)
  have p4f:=fun (a b c:G)=>by
    exact (((cg (fun t => (b ◇ a) ◇ t) (p31 a b)).symm).trans (p47 c (b ◇ a) (a ◇ (b ◇ b)))).symm
  have p4g:=fun (a b c:G)=>by
    exact ((cg (fun t => (a ◇ (b ◇ a)) ◇ t) (p1s c c)).symm).trans (((cg (fun t => (a ◇ (b ◇ a)) ◇ t) (p4c a b (c ◇ c))).symm).trans (p4f b c (a ◇ (b ◇ a))))
  have p4h:=fun (a b c:G)=>by
    exact (((cg (fun t => t ◇ b) (cg (fun t => a ◇ t) (p4b a b))).symm).trans ((((cg (fun t => t ◇ b) (cg (fun t => t ◇ (b ◇ ((a ◇ a) ◇ a))) (p4 a))).symm).trans (p4d b (a ◇ a) ((a ◇ a) ◇ a) c)).trans (p4e b (a ◇ a) (c ◇ (((a ◇ a) ◇ b) ◇ c)) c))).symm
  have p4i:=fun (a b:G)=>by
    exact ((cg (fun t => (a ◇ (b ◇ b)) ◇ t) ((p46 (b ◇ b) a).symm)).symm).trans (p48 b (a ◇ (b ◇ b)) a)
  have p4j:=fun (a b:G)=>by
    exact ((((cg (fun t => t ◇ (a ◇ (b ◇ b))) (cg (fun t => t ◇ ((a ◇ a) ◇ b)) (p1s b b))).trans (cg (fun t => t ◇ (a ◇ (b ◇ b))) (p4e a a (b ◇ ((a ◇ a) ◇ b)) b))).trans (cg (fun t => t ◇ (a ◇ (b ◇ b))) (p19 a))).symm).trans (((cg (fun t => (((b ◇ b) ◇ ((b ◇ b) ◇ (b ◇ b))) ◇ ((a ◇ a) ◇ b)) ◇ t) (cg (fun t => t ◇ (b ◇ b)) (p4i (b ◇ b) a))).symm).trans (p3x (a ◇ a) b ((b ◇ b) ◇ ((b ◇ b) ◇ (b ◇ b)))))
  have p4k:=fun (a b c:G)=>by
    exact ((((((cg (fun t => t ◇ (((c ◇ (a ◇ a)) ◇ ((a ◇ a) ◇ c)) ◇ b)) (cg (fun t => b ◇ t) (p1h a))).trans (cg (fun t => (b ◇ a) ◇ t) (cg (fun t => t ◇ b) (p3f a c a)))).trans (cg (fun t => (b ◇ a) ◇ t) (cg (fun t => t ◇ b) (p1m a)))).trans (cg (fun t => (b ◇ a) ◇ t) (p4g a a b))).trans (p4j (b ◇ a) b)).symm).trans ((((cg (fun t => t ◇ (((c ◇ (a ◇ a)) ◇ ((a ◇ a) ◇ c)) ◇ b)) (cg (fun t => b ◇ t) (p4j (a ◇ a) a))).symm).trans (p3w c (a ◇ a) b)).trans (p1s a a))
  have p4l:=fun (a b:G)=>by
    exact (((cg (fun t => b ◇ t) (cg (fun t => t ◇ b) (p4k a b a))).symm).trans (p4h (b ◇ a) b a)).symm
  exact (p47 z x y).trans ((p4l y z).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_19023_to_57619 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_19023_to_57619
