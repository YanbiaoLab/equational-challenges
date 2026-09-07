-- Equation41890 → Equation41953
-- Recorded verdict: true
-- Premise: x ◇ y = y ◇ (x ◇ (x ◇ (z ◇ y)))
-- Conclusion: x ◇ y = y ◇ (y ◇ (z ◇ (w ◇ y)))
-- Original submission SHA-256: 432f4a71f390aeaaca64d26690fb66672ec3093cc4b044db59beb80b053c5574
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ y = y ◇ (x ◇ (x ◇ (z ◇ y)))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x ◇ y = y ◇ (y ◇ (z ◇ (w ◇ y)))
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
                     

def submission : Goal := by
  intro G _ h
  intro x y z w
  have cg : ∀ (f:G → G) {a b:G}, a=b → f a=f b:=by
    intro f a b p
    exact congrArg f p
  have p0:=fun (a b:G)=>by
    exact ((cg (fun t => (a ◇ b) ◇ t) ((h b b a).symm)).symm).trans ((h b (a ◇ b) b).symm)
  have p1:=fun (a b:G)=>by
    exact ((cg (fun t => b ◇ t) (cg (fun t => (a ◇ b) ◇ t) (p0 a b))).symm).trans ((h (a ◇ b) b b).symm)
  have p2:=fun (a b:G)=>by
    exact ((cg (fun t => (b ◇ (a ◇ a)) ◇ t) (p0 a a)).symm).trans (p0 b (a ◇ a))
  have p3:=fun (a b c:G)=>by
    exact ((h a b c).symm).trans (h a b a)
  have p4:=fun (a b:G)=>by
    exact ((p3 a b a).symm).trans ((h a b a).symm)
  have p5:=fun (a b c:G)=>by
    exact ((cg (fun t => (c ◇ (a ◇ b)) ◇ t) (cg (fun t => b ◇ t) ((h c b a).symm))).symm).trans ((h b (c ◇ (a ◇ b)) c).symm)
  have p6:=fun (a:G)=>by
    exact ((p2 a a).symm).trans (((cg (fun t => (a ◇ (a ◇ a)) ◇ t) (cg (fun t => a ◇ t) (p4 a a))).symm).trans (p4 a (a ◇ (a ◇ a))))
  have p7:=fun (a:G)=>by
    exact (((p4 a a).symm).trans (((cg (fun t => a ◇ t) (p6 a)).symm).trans (p1 a a))).symm
  have p8:=fun (a b:G)=>by
    exact ((cg (fun t => b ◇ t) (cg (fun t => a ◇ t) (cg (fun t => a ◇ t) (p7 b)))).symm).trans ((h a b (b ◇ b)).symm)
  have p9:=fun (a b c d:G)=>by
    exact ((cg (fun t => (a ◇ (a ◇ (b ◇ d))) ◇ t) (cg (fun t => c ◇ t) (cg (fun t => c ◇ t) ((h a d b).symm)))).symm).trans ((h c (a ◇ (a ◇ (b ◇ d))) d).symm)
  have pa:=fun (a b:G)=>by
    exact ((cg (fun t => a ◇ t) (p0 (b ◇ a) (b ◇ a))).symm).trans (((cg (fun t => a ◇ t) (cg (fun t => ((b ◇ a) ◇ (b ◇ a)) ◇ t) (p7 (b ◇ a)))).symm).trans ((h ((b ◇ a) ◇ (b ◇ a)) a b).symm))
  have pb:=fun (a b:G)=>by
    exact ((pa a b).symm).trans ((h (b ◇ a) a b).symm)
  have pc:=fun (a b:G)=>by
    exact (pa a b).trans (pb a b)
  have pd:=fun (a b c:G)=>by
    exact ((cg (fun t => (b ◇ b) ◇ t) (cg (fun t => c ◇ t) (cg (fun t => c ◇ t) (p0 a b)))).symm).trans ((h c (b ◇ b) (a ◇ b)).symm)
  have pe:=fun (a b:G)=>by
    exact ((((cg (fun t => (b ◇ (a ◇ b)) ◇ t) (p0 b b)).trans (p5 a b b)).symm).trans (((cg (fun t => (b ◇ (a ◇ b)) ◇ t) (pd a b (b ◇ b))).symm).trans ((h (b ◇ b) (b ◇ (a ◇ b)) (b ◇ b)).symm))).symm
  have pf:=fun (a:G)=>by
    exact (((cg (fun t => t ◇ (a ◇ (a ◇ a))) (p5 a a a)).symm).trans (p7 (a ◇ (a ◇ a)))).trans ((p2 a a).trans (pe a a))
  have pg:=fun (a:G)=>by
    exact ((((((cg (fun t => (a ◇ (a ◇ (a ◇ a))) ◇ t) (p2 a a)).trans (cg (fun t => (a ◇ (a ◇ (a ◇ a))) ◇ t) (pe a a))).trans (p9 a a a a)).trans (p4 a a)).symm).trans ((((cg (fun t => t ◇ ((a ◇ (a ◇ a)) ◇ (a ◇ (a ◇ a)))) (pf a)).symm).trans (p0 (a ◇ (a ◇ (a ◇ a))) (a ◇ (a ◇ a)))).trans (cg (fun t => (a ◇ (a ◇ a)) ◇ t) (pf a)))).symm
  have ph:=fun (a b c:G)=>by
    exact ((cg (fun t => t ◇ ((a ◇ (a ◇ (b ◇ c))) ◇ (a ◇ (a ◇ (b ◇ c))))) ((h a c b).symm)).symm).trans (p0 c (a ◇ (a ◇ (b ◇ c))))
  have pi:=fun (a b:G)=>by
    exact (((p4 a (a ◇ b)).symm).trans ((((cg (fun t => (a ◇ b) ◇ t) (p9 a a a b)).symm).trans (ph a a b)).trans (cg (fun t => (a ◇ (a ◇ (a ◇ b))) ◇ t) (p4 a b)))).symm
  have pj:=fun (a b:G)=>by
    exact ((cg (fun t => (b ◇ (b ◇ (a ◇ b))) ◇ t) (p4 a b)).symm).trans ((((cg (fun t => t ◇ (b ◇ (a ◇ (a ◇ (a ◇ b))))) (cg (fun t => b ◇ t) (cg (fun t => b ◇ t) (p4 a b)))).symm).trans (pi b (a ◇ (a ◇ (a ◇ b))))).trans (cg (fun t => b ◇ t) (p4 a b)))
  have pk:=fun (a b c:G)=>by
    exact ((cg (fun t => (a ◇ b) ◇ t) (cg (fun t => c ◇ t) (cg (fun t => c ◇ t) (pi a b)))).symm).trans ((h c (a ◇ b) (a ◇ (a ◇ (a ◇ b)))).symm)
  have pl:=fun (a b:G)=>by
    exact ((cg (fun t => (b ◇ (a ◇ b)) ◇ t) (cg (fun t => b ◇ t) (p1 a b))).symm).trans ((h b (b ◇ (a ◇ b)) (a ◇ b)).symm)
  have pm:=fun (a b c:G)=>by
    exact ((cg (fun t => (a ◇ b) ◇ t) (cg (fun t => c ◇ t) (cg (fun t => c ◇ t) (pj a b)))).symm).trans ((h c (a ◇ b) (b ◇ (b ◇ (a ◇ b)))).symm)
  have pn:=fun (a b c:G)=>by
    exact ((cg (fun t => c ◇ t) (cg (fun t => b ◇ t) (cg (fun t => b ◇ t) (pb c a)))).symm).trans ((h b c ((a ◇ c) ◇ (a ◇ c))).symm)
  have po:=fun (a b:G)=>by
    exact (((cg (fun t => t ◇ ((a ◇ (a ◇ b)) ◇ (b ◇ (a ◇ (a ◇ b))))) (p4 a b)).symm).trans (p5 a (a ◇ (a ◇ b)) b)).trans (cg (fun t => (a ◇ (a ◇ b)) ◇ t) (p4 a b))
  have pp:=fun (a b c:G)=>by
    exact ((cg (fun t => ((a ◇ c) ◇ (c ◇ (a ◇ c))) ◇ t) (cg (fun t => b ◇ t) (cg (fun t => b ◇ t) (p1 a c)))).symm).trans ((h b ((a ◇ c) ◇ (c ◇ (a ◇ c))) c).symm)
  have pq:=fun (a b c:G)=>by
    exact ((cg (fun t => (a ◇ (a ◇ (b ◇ c))) ◇ t) (cg (fun t => t ◇ ((a ◇ (a ◇ (b ◇ c))) ◇ (c ◇ (a ◇ (a ◇ (b ◇ c)))))) ((h a c b).symm))).symm).trans (p1 c (a ◇ (a ◇ (b ◇ c))))
  have pr:=fun (a b c:G)=>by
    exact ((cg (fun t => (a ◇ (a ◇ (b ◇ c))) ◇ t) (cg (fun t => (c ◇ (a ◇ (a ◇ (b ◇ c)))) ◇ t) (cg (fun t => (a ◇ (a ◇ (b ◇ c))) ◇ t) ((h a c b).symm)))).symm).trans (p1 c (a ◇ (a ◇ (b ◇ c))))
  have ps:=fun (a b:G)=>by
    exact (((cg (fun t => t ◇ (((a ◇ b) ◇ (b ◇ (a ◇ b))) ◇ ((a ◇ b) ◇ (b ◇ (a ◇ b))))) (p1 a b)).symm).trans (p0 b ((a ◇ b) ◇ (b ◇ (a ◇ b))))).trans (cg (fun t => ((a ◇ b) ◇ (b ◇ (a ◇ b))) ◇ t) (p1 a b))
  have pt:=fun (a b:G)=>by
    exact ((cg (fun t => a ◇ t) (cg (fun t => (b ◇ (b ◇ (b ◇ a))) ◇ t) (pi b a))).symm).trans ((h (b ◇ (b ◇ (b ◇ a))) a b).symm)
  have pu:=fun (a b:G)=>by
    exact (((cg (fun t => t ◇ (a ◇ (a ◇ (a ◇ b)))) (p9 a a a b)).symm).trans (p7 (a ◇ (a ◇ (a ◇ b))))).trans (p9 a a a b)
  have pv:=fun (a b:G)=>by
    exact (((p4 b (b ◇ a)).symm).trans (((cg (fun t => (b ◇ a) ◇ t) (pu b a)).symm).trans (pt (b ◇ a) b))).symm
  have pw:=fun (a b:G)=>by
    exact (((cg (fun t => (b ◇ b) ◇ t) (cg (fun t => (b ◇ (a ◇ b)) ◇ t) (cg (fun t => (b ◇ b) ◇ t) (p0 a b)))).trans (cg (fun t => (b ◇ b) ◇ t) (cg (fun t => (b ◇ (a ◇ b)) ◇ t) (pe a b)))).symm).trans ((((cg (fun t => (b ◇ b) ◇ t) (cg (fun t => t ◇ ((b ◇ b) ◇ ((a ◇ b) ◇ (b ◇ b)))) (p0 a b))).symm).trans (p1 (a ◇ b) (b ◇ b))).trans (cg (fun t => t ◇ (b ◇ b)) (p0 a b)))
  have px:=fun (a b:G)=>by
    exact (((cg (fun t => (b ◇ (b ◇ (b ◇ ((a ◇ b) ◇ b)))) ◇ t) (p1 a b)).trans (cg (fun t => t ◇ ((a ◇ b) ◇ b)) (pn a b b))).symm).trans ((((cg (fun t => t ◇ (b ◇ ((a ◇ b) ◇ (b ◇ (a ◇ b))))) (cg (fun t => b ◇ t) (cg (fun t => b ◇ t) (cg (fun t => b ◇ t) (p1 a b))))).symm).trans (pv ((a ◇ b) ◇ (b ◇ (a ◇ b))) b)).trans (cg (fun t => b ◇ t) (p1 a b)))
  have py:=fun (a b:G)=>by
    exact ((((cg (fun t => a ◇ t) (pi b (b ◇ a))).trans (p4 b a)).symm).trans (((cg (fun t => a ◇ t) (cg (fun t => (b ◇ (b ◇ (b ◇ (b ◇ a)))) ◇ t) (pv a b))).symm).trans ((h (b ◇ (b ◇ (b ◇ (b ◇ a)))) a b).symm))).symm
  have pz:=fun (a b:G)=>by
    exact ((cg (fun t => t ◇ (a ◇ b)) (cg (fun t => b ◇ t) ((h b b a).symm))).symm).trans (py (a ◇ b) b)
  have p10:=fun (a b:G)=>by
    exact (((cg (fun t => t ◇ (b ◇ (a ◇ (a ◇ a)))) (pg a)).symm).trans (((cg (fun t => t ◇ (b ◇ (a ◇ (a ◇ a)))) (cg (fun t => (a ◇ (a ◇ a)) ◇ t) (p5 a a a))).symm).trans (pz b (a ◇ (a ◇ a))))).symm
  have p11:=fun (a b:G)=>by
    exact ((cg (fun t => (b ◇ (b ◇ (b ◇ (a ◇ b)))) ◇ t) (p4 a b)).symm).trans ((((cg (fun t => t ◇ (b ◇ (a ◇ (a ◇ (a ◇ b))))) (cg (fun t => b ◇ t) (cg (fun t => b ◇ t) (cg (fun t => b ◇ t) (p4 a b))))).symm).trans (pv (a ◇ (a ◇ (a ◇ b))) b)).trans (cg (fun t => b ◇ t) (p4 a b)))
  have p12:=fun (a b:G)=>by
    exact ((cg (fun t => t ◇ (a ◇ b)) ((h b b a).symm)).symm).trans (p11 a b)
  have p13:=fun (a b:G)=>by
    exact ((cg (fun t => a ◇ t) (pe b a)).symm).trans ((((cg (fun t => a ◇ t) (cg (fun t => (a ◇ a) ◇ t) (p12 b a))).symm).trans ((h (a ◇ a) a b).symm)).trans (p7 a))
  have p14:=fun (a b:G)=>by
    exact ((cg (fun t => t ◇ (b ◇ (a ◇ a))) (p0 a a)).symm).trans (p12 b (a ◇ a))
  have p15:=fun (a b:G)=>by
    exact (((((cg (fun t => ((a ◇ b) ◇ (b ◇ (a ◇ b))) ◇ t) (pe (a ◇ b) b)).trans (pp a b b)).trans (p1 a b)).symm).trans (((cg (fun t => ((a ◇ b) ◇ (b ◇ (a ◇ b))) ◇ t) (cg (fun t => (b ◇ b) ◇ t) (px a b))).symm).trans (pp a (b ◇ b) b))).symm
  have p16:=fun (a b:G)=>by
    exact ((((cg (fun t => ((a ◇ b) ◇ (a ◇ b)) ◇ t) (p12 (a ◇ b) b)).trans (p5 a b (a ◇ b))).symm).trans (((cg (fun t => ((a ◇ b) ◇ (a ◇ b)) ◇ t) (cg (fun t => (b ◇ b) ◇ t) (p15 a b))).symm).trans (pd b (a ◇ b) (b ◇ b)))).symm
  have p17:=fun (a b:G)=>by
    exact ((cg (fun t => t ◇ (b ◇ (b ◇ (a ◇ b)))) (p4 b b)).symm).trans ((((cg (fun t => t ◇ (b ◇ (b ◇ (a ◇ b)))) (cg (fun t => b ◇ t) (cg (fun t => b ◇ t) (cg (fun t => b ◇ t) (p13 b a))))).symm).trans (py (b ◇ (b ◇ (a ◇ b))) b)).trans (p13 b a))
  have p18:=fun (a b:G)=>by
    exact ((cg (fun t => t ◇ (b ◇ (a ◇ b))) (cg (fun t => b ◇ t) ((h b b a).symm))).symm).trans (pv (a ◇ b) b)
  have p19:=fun (a b:G)=>by
    exact ((cg (fun t => (a ◇ (a ◇ (b ◇ (a ◇ a)))) ◇ t) (p4 a a)).symm).trans (p9 a b a (a ◇ a))
  have p1a:=fun (a b:G)=>by
    exact ((cg (fun t => t ◇ (a ◇ (a ◇ (b ◇ b)))) (p13 b a)).symm).trans ((((cg (fun t => t ◇ (a ◇ (a ◇ (b ◇ b)))) (cg (fun t => b ◇ t) (cg (fun t => b ◇ t) (cg (fun t => b ◇ t) (p8 a b))))).symm).trans (py (a ◇ (a ◇ (b ◇ b))) b)).trans (p8 a b))
  have p1b:=fun (a b:G)=>by
    exact ((((cg (fun t => (b ◇ (a ◇ a)) ◇ t) (p12 b a)).trans (p5 a a b)).symm).trans (((cg (fun t => (b ◇ (a ◇ a)) ◇ t) (cg (fun t => (a ◇ a) ◇ t) (p1a b a))).symm).trans ((h (a ◇ a) (b ◇ (a ◇ a)) b).symm))).symm
  have p1c:=fun (a b c:G)=>by
    exact ((cg (fun t => t ◇ (a ◇ (a ◇ (b ◇ c)))) (p13 c a)).symm).trans (((cg (fun t => t ◇ (a ◇ (a ◇ (b ◇ c)))) (cg (fun t => c ◇ t) (cg (fun t => c ◇ t) (cg (fun t => c ◇ t) ((h a c b).symm))))).symm).trans (py (a ◇ (a ◇ (b ◇ c))) c))
  have p1d:=fun (a b:G)=>by
    exact (((cg (fun t => t ◇ (b ◇ (b ◇ (a ◇ b)))) (cg (fun t => b ◇ t) ((h b b a).symm))).symm).trans (pi b (b ◇ (a ◇ b)))).trans (p13 b a)
  have p1e:=fun (a b:G)=>by
    exact (((((cg (fun t => ((a ◇ (a ◇ (a ◇ b))) ◇ (a ◇ (a ◇ (a ◇ b)))) ◇ t) (pi a b)).trans (cg (fun t => t ◇ (a ◇ (a ◇ b))) (p9 a a a b))).trans (pi a (a ◇ b))).symm).trans ((((cg (fun t => ((a ◇ (a ◇ (a ◇ b))) ◇ (a ◇ (a ◇ (a ◇ b)))) ◇ t) (cg (fun t => (a ◇ (a ◇ (a ◇ b))) ◇ t) (p4 a b))).symm).trans (pe b (a ◇ (a ◇ (a ◇ b))))).trans ((cg (fun t => (a ◇ (a ◇ (a ◇ b))) ◇ t) (cg (fun t => (a ◇ (a ◇ (a ◇ b))) ◇ t) (p4 a b))).trans (cg (fun t => (a ◇ (a ◇ (a ◇ b))) ◇ t) (pi a b))))).symm
  have p1f:=fun (a b:G)=>by
    exact (((p4 b a).symm).trans (((cg (fun t => a ◇ t) (p1e b a)).symm).trans (pt a b))).symm
  have p1g:=fun (a b:G)=>by
    exact ((p9 b a a b).symm).trans ((((cg (fun t => t ◇ (a ◇ (a ◇ (b ◇ b)))) (cg (fun t => b ◇ t) (cg (fun t => b ◇ t) (p8 a b)))).symm).trans (p1f (a ◇ (a ◇ (b ◇ b))) b)).trans (p8 a b))
  have p1h:=fun (a b c:G)=>by
    exact (((cg (fun t => b ◇ t) (pi a (c ◇ b))).symm).trans (((cg (fun t => b ◇ t) (cg (fun t => (a ◇ (a ◇ (a ◇ (c ◇ b)))) ◇ t) (p1f (c ◇ b) a))).symm).trans ((h (a ◇ (a ◇ (a ◇ (c ◇ b)))) b c).symm))).symm
  have p1i:=fun (a b:G)=>by
    exact ((cg (fun t => (b ◇ (a ◇ b)) ◇ t) (cg (fun t => a ◇ t) (p1g a b))).symm).trans ((h a (b ◇ (a ◇ b)) b).symm)
  have p1j:=fun (a b c:G)=>by
    exact ((((cg (fun t => (a ◇ (a ◇ (b ◇ c))) ◇ t) (p18 a c)).trans (p9 a b c c)).symm).trans (((cg (fun t => (a ◇ (a ◇ (b ◇ c))) ◇ t) (cg (fun t => (c ◇ (c ◇ c)) ◇ t) (pz a c))).symm).trans (p9 a b (c ◇ (c ◇ c)) c))).symm
  have p1k:=fun (a b c:G)=>by
    exact (((cg (fun t => b ◇ t) (pv (c ◇ b) a)).symm).trans (((cg (fun t => b ◇ t) (cg (fun t => (a ◇ (a ◇ (a ◇ (a ◇ (c ◇ b))))) ◇ t) (py (c ◇ b) a))).symm).trans ((h (a ◇ (a ◇ (a ◇ (a ◇ (c ◇ b))))) b c).symm))).symm
  have p1l:=fun (a b c:G)=>by
    exact ((cg (fun t => t ◇ (c ◇ (a ◇ b))) (p13 b c)).symm).trans ((((cg (fun t => t ◇ (c ◇ (a ◇ b))) (cg (fun t => b ◇ t) (cg (fun t => b ◇ t) (cg (fun t => b ◇ t) ((h c b a).symm))))).symm).trans (p1k b (c ◇ (a ◇ b)) c)).trans (pk c (a ◇ b) b))
  have p1m:=fun (a b c:G)=>by
    exact ((cg (fun t => t ◇ (c ◇ (a ◇ (a ◇ (b ◇ c))))) (p13 c a)).symm).trans (((cg (fun t => t ◇ (c ◇ (a ◇ (a ◇ (b ◇ c))))) (cg (fun t => c ◇ t) (cg (fun t => c ◇ t) (cg (fun t => c ◇ t) ((h a c b).symm))))).symm).trans (pv (a ◇ (a ◇ (b ◇ c))) c))
  have p1n:=fun (a b c:G)=>by
    exact (((p12 a c).symm).trans (((cg (fun t => (c ◇ c) ◇ t) ((h a c b).symm)).symm).trans (p1m a b c))).symm
  have p1o:=fun (a b:G)=>by
    exact ((((cg (fun t => (a ◇ (a ◇ (b ◇ (a ◇ a)))) ◇ t) (p7 a)).trans (p19 a b)).symm).trans (((cg (fun t => (a ◇ (a ◇ (b ◇ (a ◇ a)))) ◇ t) (p15 a a)).symm).trans (p9 a b (a ◇ a) (a ◇ a)))).symm
  have p1p:=fun (a b:G)=>by
    exact ((p1o a b).symm).trans ((h a (a ◇ a) b).symm)
  have p1q:=fun (a b:G)=>by
    exact ((cg (fun t => t ◇ (b ◇ (a ◇ (b ◇ b)))) (p4 b b)).symm).trans (((cg (fun t => t ◇ (b ◇ (a ◇ (b ◇ b)))) (cg (fun t => b ◇ t) (cg (fun t => b ◇ t) (p1p b a)))).symm).trans (py (b ◇ (a ◇ (b ◇ b))) b))
  have p1r:=fun (a b:G)=>by
    exact (p1o a b).trans (p1p a b)
  have p1s:=fun (a b:G)=>by
    exact ((cg (fun t => b ◇ t) (p1q b a)).symm).trans (((cg (fun t => b ◇ t) (cg (fun t => (a ◇ a) ◇ t) (p1b a b))).symm).trans (p1g b (a ◇ a)))
  have p1t:=fun (a b:G)=>by
    exact (((((cg (fun t => ((a ◇ b) ◇ (a ◇ (a ◇ b))) ◇ t) (cg (fun t => (a ◇ (a ◇ (a ◇ b))) ◇ t) (pi a b))).trans (cg (fun t => ((a ◇ b) ◇ (a ◇ (a ◇ b))) ◇ t) (p1e a b))).trans (p1i a (a ◇ b))).symm).trans ((((cg (fun t => t ◇ ((a ◇ (a ◇ (a ◇ b))) ◇ ((a ◇ (a ◇ (a ◇ b))) ◇ (a ◇ b)))) (cg (fun t => (a ◇ b) ◇ t) (pi a b))).symm).trans (p1i (a ◇ (a ◇ (a ◇ b))) (a ◇ b))).trans ((cg (fun t => (a ◇ (a ◇ (a ◇ b))) ◇ t) (cg (fun t => (a ◇ b) ◇ t) (pi a b))).trans (p5 a (a ◇ b) a)))).symm
  have p1u:=fun (a b:G)=>by
    exact ((cg (fun t => (a ◇ b) ◇ t) (cg (fun t => b ◇ t) (cg (fun t => b ◇ t) (p4 a b)))).symm).trans ((((cg (fun t => t ◇ (b ◇ (b ◇ (b ◇ (a ◇ (a ◇ (a ◇ b))))))) (p4 a b)).symm).trans (p1t b (a ◇ (a ◇ (a ◇ b))))).trans (((cg (fun t => b ◇ t) (cg (fun t => (b ◇ (a ◇ (a ◇ (a ◇ b)))) ◇ t) (cg (fun t => b ◇ t) (p4 a b)))).trans (cg (fun t => b ◇ t) (cg (fun t => t ◇ (b ◇ (a ◇ b))) (p4 a b)))).trans (p1 a b)))
  have p1v:=fun (a b:G)=>by
    exact (((((cg (fun t => (b ◇ b) ◇ t) (p18 b (a ◇ b))).trans (pd a b (a ◇ b))).trans (p0 a b)).symm).trans (((cg (fun t => (b ◇ b) ◇ t) (cg (fun t => ((a ◇ b) ◇ ((a ◇ b) ◇ (a ◇ b))) ◇ t) (pz b (a ◇ b)))).symm).trans (pd a b ((a ◇ b) ◇ ((a ◇ b) ◇ (a ◇ b)))))).symm
  have p1w:=fun (a b c:G)=>by
    exact ((((cg (fun t => t ◇ (c ◇ (c ◇ (b ◇ (a ◇ b))))) (cg (fun t => (b ◇ b) ◇ t) (cg (fun t => (b ◇ b) ◇ t) (p1l b b c)))).trans (cg (fun t => t ◇ (c ◇ (c ◇ (b ◇ (a ◇ b))))) (cg (fun t => (b ◇ b) ◇ t) (p1q c b)))).trans (cg (fun t => t ◇ (c ◇ (c ◇ (b ◇ (a ◇ b))))) (p1r b c))).symm).trans ((((cg (fun t => t ◇ (c ◇ (c ◇ (b ◇ (a ◇ b))))) (cg (fun t => (b ◇ b) ◇ t) (cg (fun t => (b ◇ b) ◇ t) (cg (fun t => (b ◇ b) ◇ t) (pd a b c))))).symm).trans (py (c ◇ (c ◇ (b ◇ (a ◇ b)))) (b ◇ b))).trans (pd a b c))
  have p1x:=fun (a b:G)=>by
    exact (((((((((cg (fun t => ((a ◇ (a ◇ a)) ◇ ((a ◇ (a ◇ a)) ◇ (a ◇ (a ◇ a)))) ◇ t) (cg (fun t => b ◇ t) (cg (fun t => b ◇ t) (p10 a a)))).trans (cg (fun t => ((a ◇ (a ◇ a)) ◇ ((a ◇ (a ◇ a)) ◇ (a ◇ (a ◇ a)))) ◇ t) (cg (fun t => b ◇ t) (cg (fun t => b ◇ t) (p17 a a))))).trans (cg (fun t => t ◇ (b ◇ (b ◇ (a ◇ a)))) (cg (fun t => (a ◇ (a ◇ a)) ◇ t) (p5 a a a)))).trans (cg (fun t => t ◇ (b ◇ (b ◇ (a ◇ a)))) (p10 a a))).trans (cg (fun t => t ◇ (b ◇ (b ◇ (a ◇ a)))) (p17 a a))).trans (p1c b a a)).trans (p8 b a)).symm).trans ((((cg (fun t => ((a ◇ (a ◇ a)) ◇ ((a ◇ (a ◇ a)) ◇ (a ◇ (a ◇ a)))) ◇ t) (cg (fun t => b ◇ t) (cg (fun t => b ◇ t) (cg (fun t => (a ◇ (a ◇ a)) ◇ t) (pf a))))).symm).trans (p1w (a ◇ (a ◇ (a ◇ a))) (a ◇ (a ◇ a)) b)).trans (cg (fun t => b ◇ t) (p5 a a a)))).symm
  have p1y:=fun (a b:G)=>by
    exact ((cg (fun t => (b ◇ (b ◇ b)) ◇ t) (cg (fun t => a ◇ t) (p1x b a))).symm).trans ((h a (b ◇ (b ◇ b)) b).symm)
  have p1z:=fun (a b:G)=>by
    exact (((((cg (fun t => t ◇ (a ◇ (a ◇ b))) (cg (fun t => (b ◇ (b ◇ b)) ◇ t) (p5 b b b))).trans (cg (fun t => t ◇ (a ◇ (a ◇ b))) (p10 b b))).trans (cg (fun t => t ◇ (a ◇ (a ◇ b))) (p17 b b))).trans (p1l a b a)).symm).trans ((((cg (fun t => ((b ◇ (b ◇ b)) ◇ ((b ◇ (b ◇ b)) ◇ (b ◇ (b ◇ b)))) ◇ t) (cg (fun t => a ◇ t) (p1x b a))).symm).trans (p1j a b (b ◇ (b ◇ b)))).trans ((cg (fun t => (b ◇ (b ◇ b)) ◇ t) (cg (fun t => a ◇ t) (p1x b a))).trans (p1y a b)))
  have p20:=fun (a b:G)=>by
    exact ((cg (fun t => (b ◇ a) ◇ t) (cg (fun t => a ◇ t) (p1z b a))).symm).trans ((h a (b ◇ a) b).symm)
  have p21:=fun (a b:G)=>by
    exact ((((((cg (fun t => t ◇ ((b ◇ (b ◇ b)) ◇ ((b ◇ (b ◇ b)) ◇ (b ◇ (b ◇ (a ◇ b)))))) (cg (fun t => (b ◇ (a ◇ b)) ◇ t) (pz b b))).trans (cg (fun t => ((b ◇ (a ◇ b)) ◇ (b ◇ (b ◇ b))) ◇ t) (cg (fun t => (b ◇ (b ◇ b)) ◇ t) (p1j b a b)))).trans (cg (fun t => ((b ◇ (a ◇ b)) ◇ (b ◇ (b ◇ b))) ◇ t) (cg (fun t => (b ◇ (b ◇ b)) ◇ t) (p13 b a)))).trans (cg (fun t => ((b ◇ (a ◇ b)) ◇ (b ◇ (b ◇ b))) ◇ t) (pz b b))).trans (cg (fun t => t ◇ (b ◇ (b ◇ b))) (p5 a b b))).symm).trans ((((cg (fun t => t ◇ ((b ◇ (b ◇ b)) ◇ ((b ◇ (b ◇ b)) ◇ (b ◇ (b ◇ (a ◇ b)))))) (cg (fun t => (b ◇ (a ◇ b)) ◇ t) (cg (fun t => (b ◇ (b ◇ b)) ◇ t) (p1d a b)))).symm).trans ((pq (b ◇ (b ◇ b)) b (b ◇ (a ◇ b))).symm)).trans (((((((((((((((cg (fun t => ((b ◇ (b ◇ b)) ◇ ((b ◇ (b ◇ b)) ◇ (b ◇ (b ◇ (a ◇ b))))) ◇ t) (cg (fun t => ((b ◇ (b ◇ b)) ◇ (b ◇ (a ◇ b))) ◇ t) (cg (fun t => ((b ◇ (b ◇ b)) ◇ ((b ◇ (b ◇ b)) ◇ (b ◇ (b ◇ (a ◇ b))))) ◇ t) (cg (fun t => (b ◇ (a ◇ b)) ◇ t) (cg (fun t => (b ◇ (b ◇ b)) ◇ t) (p1j b a b)))))).trans (cg (fun t => ((b ◇ (b ◇ b)) ◇ ((b ◇ (b ◇ b)) ◇ (b ◇ (b ◇ (a ◇ b))))) ◇ t) (cg (fun t => ((b ◇ (b ◇ b)) ◇ (b ◇ (a ◇ b))) ◇ t) (cg (fun t => ((b ◇ (b ◇ b)) ◇ ((b ◇ (b ◇ b)) ◇ (b ◇ (b ◇ (a ◇ b))))) ◇ t) (cg (fun t => (b ◇ (a ◇ b)) ◇ t) (cg (fun t => (b ◇ (b ◇ b)) ◇ t) (p13 b a))))))).trans (cg (fun t => ((b ◇ (b ◇ b)) ◇ ((b ◇ (b ◇ b)) ◇ (b ◇ (b ◇ (a ◇ b))))) ◇ t) (cg (fun t => ((b ◇ (b ◇ b)) ◇ (b ◇ (a ◇ b))) ◇ t) (cg (fun t => ((b ◇ (b ◇ b)) ◇ ((b ◇ (b ◇ b)) ◇ (b ◇ (b ◇ (a ◇ b))))) ◇ t) (cg (fun t => (b ◇ (a ◇ b)) ◇ t) (pz b b)))))).trans (cg (fun t => ((b ◇ (b ◇ b)) ◇ ((b ◇ (b ◇ b)) ◇ (b ◇ (b ◇ (a ◇ b))))) ◇ t) (cg (fun t => ((b ◇ (b ◇ b)) ◇ (b ◇ (a ◇ b))) ◇ t) (cg (fun t => t ◇ ((b ◇ (a ◇ b)) ◇ (b ◇ (b ◇ b)))) (cg (fun t => (b ◇ (b ◇ b)) ◇ t) (p1j b a b)))))).trans (cg (fun t => ((b ◇ (b ◇ b)) ◇ ((b ◇ (b ◇ b)) ◇ (b ◇ (b ◇ (a ◇ b))))) ◇ t) (cg (fun t => ((b ◇ (b ◇ b)) ◇ (b ◇ (a ◇ b))) ◇ t) (cg (fun t => t ◇ ((b ◇ (a ◇ b)) ◇ (b ◇ (b ◇ b)))) (cg (fun t => (b ◇ (b ◇ b)) ◇ t) (p13 b a)))))).trans (cg (fun t => ((b ◇ (b ◇ b)) ◇ ((b ◇ (b ◇ b)) ◇ (b ◇ (b ◇ (a ◇ b))))) ◇ t) (cg (fun t => ((b ◇ (b ◇ b)) ◇ (b ◇ (a ◇ b))) ◇ t) (cg (fun t => t ◇ ((b ◇ (a ◇ b)) ◇ (b ◇ (b ◇ b)))) (pz b b))))).trans (cg (fun t => ((b ◇ (b ◇ b)) ◇ ((b ◇ (b ◇ b)) ◇ (b ◇ (b ◇ (a ◇ b))))) ◇ t) (cg (fun t => ((b ◇ (b ◇ b)) ◇ (b ◇ (a ◇ b))) ◇ t) (cg (fun t => (b ◇ (b ◇ b)) ◇ t) (p5 a b b))))).trans (cg (fun t => ((b ◇ (b ◇ b)) ◇ ((b ◇ (b ◇ b)) ◇ (b ◇ (b ◇ (a ◇ b))))) ◇ t) (cg (fun t => t ◇ ((b ◇ (b ◇ b)) ◇ (b ◇ (b ◇ (a ◇ b))))) (p18 a b)))).trans (cg (fun t => t ◇ ((b ◇ (b ◇ (a ◇ b))) ◇ ((b ◇ (b ◇ b)) ◇ (b ◇ (b ◇ (a ◇ b)))))) (cg (fun t => (b ◇ (b ◇ b)) ◇ t) (p1j b a b)))).trans (cg (fun t => t ◇ ((b ◇ (b ◇ (a ◇ b))) ◇ ((b ◇ (b ◇ b)) ◇ (b ◇ (b ◇ (a ◇ b)))))) (cg (fun t => (b ◇ (b ◇ b)) ◇ t) (p13 b a)))).trans (cg (fun t => ((b ◇ (b ◇ b)) ◇ (b ◇ b)) ◇ t) (cg (fun t => (b ◇ (b ◇ (a ◇ b))) ◇ t) (p1j b a b)))).trans (cg (fun t => ((b ◇ (b ◇ b)) ◇ (b ◇ b)) ◇ t) (cg (fun t => (b ◇ (b ◇ (a ◇ b))) ◇ t) (p13 b a)))).trans (cg (fun t => t ◇ ((b ◇ (b ◇ (a ◇ b))) ◇ (b ◇ b))) (pz b b))).trans (p14 b (b ◇ (b ◇ (a ◇ b))))).trans (p1l b b (b ◇ (b ◇ (a ◇ b))))))
  have p22:=fun (a b c:G)=>by
    exact (((cg (fun t => (a ◇ (a ◇ (a ◇ a))) ◇ t) (cg (fun t => b ◇ t) (cg (fun t => b ◇ t) (p1x a c)))).symm).trans ((h b (a ◇ (a ◇ (a ◇ a))) c).symm)).trans (p1x a b)
  have p23:=fun (a b c:G)=>by
    exact ((p22 a (b ◇ (b ◇ (c ◇ a))) b).symm).trans ((((cg (fun t => (a ◇ (a ◇ (a ◇ a))) ◇ t) (cg (fun t => (b ◇ (b ◇ (c ◇ a))) ◇ t) (cg (fun t => (b ◇ (b ◇ (c ◇ a))) ◇ t) (p22 a b c)))).symm).trans (p1g (a ◇ (a ◇ (a ◇ a))) (b ◇ (b ◇ (c ◇ a))))).trans (p22 a b c))
  have p24:=fun (a b:G)=>by
    exact ((p1i b a).symm).trans (((cg (fun t => t ◇ (b ◇ (b ◇ a))) (cg (fun t => a ◇ t) (p4 b a))).symm).trans (p23 (b ◇ (b ◇ a)) a b))
  have p25:=fun (a b:G)=>by
    exact (((p5 a b a).trans (p1z a b)).symm).trans (((cg (fun t => t ◇ (b ◇ (a ◇ b))) (cg (fun t => a ◇ t) (p1g a b))).symm).trans (p23 (b ◇ (a ◇ b)) a b))
  have p26:=fun (a b:G)=>by
    exact (((cg (fun t => b ◇ t) (p1l a a b)).symm).trans (p24 (a ◇ a) b)).trans ((p1c b a a).trans (p8 b a))
  have p27:=fun (a b c:G)=>by
    exact ((p9 a b c (c ◇ c)).symm).trans ((((cg (fun t => (a ◇ (a ◇ (b ◇ (c ◇ c)))) ◇ t) (cg (fun t => c ◇ t) (cg (fun t => c ◇ t) (p23 (c ◇ c) a b)))).symm).trans (p1s c (a ◇ (a ◇ (b ◇ (c ◇ c)))))).trans (p23 (c ◇ c) a b))
  have p28:=fun (a b c:G)=>by
    exact ((cg (fun t => t ◇ (c ◇ (a ◇ b))) (cg (fun t => b ◇ t) ((h c b a).symm))).symm).trans (p23 (c ◇ (a ◇ b)) b c)
  have p29:=fun (a b:G)=>by
    exact ((((cg (fun t => b ◇ t) (p26 b (b ◇ (b ◇ (a ◇ b))))).trans (cg (fun t => b ◇ t) (p23 b b a))).symm).trans (((cg (fun t => b ◇ t) (cg (fun t => (b ◇ (b ◇ (a ◇ b))) ◇ t) (p21 a b))).symm).trans (p27 (b ◇ (b ◇ (a ◇ b))) b b))).symm
  have p2a:=fun (a b:G)=>by
    exact (((cg (fun t => b ◇ t) (cg (fun t => a ◇ t) (cg (fun t => a ◇ t) (p0 b b)))).trans (cg (fun t => b ◇ t) (cg (fun t => a ◇ t) (p25 a b)))).symm).trans (((cg (fun t => b ◇ t) (cg (fun t => a ◇ t) (cg (fun t => a ◇ t) (p7 (b ◇ b))))).symm).trans (p27 a ((b ◇ b) ◇ (b ◇ b)) b))
  have p2b:=fun (a b:G)=>by
    exact ((cg (fun t => b ◇ t) (cg (fun t => a ◇ t) (p24 b a))).symm).trans (p2a a b)
  have p2c:=fun (a b:G)=>by
    exact ((cg (fun t => (a ◇ b) ◇ t) (cg (fun t => b ◇ t) ((h (a ◇ b) b a).symm))).symm).trans (p27 b (a ◇ b) (a ◇ b))
  have p2d:=fun (a b:G)=>by
    exact ((((cg (fun t => (b ◇ b) ◇ t) (cg (fun t => (a ◇ b) ◇ t) (cg (fun t => (a ◇ b) ◇ t) (pe a b)))).trans (cg (fun t => (b ◇ b) ◇ t) (cg (fun t => (a ◇ b) ◇ t) (p1u a b)))).trans (p1l (a ◇ b) b (a ◇ b))).symm).trans ((((cg (fun t => (b ◇ b) ◇ t) (cg (fun t => (a ◇ b) ◇ t) (cg (fun t => (a ◇ b) ◇ t) (cg (fun t => (b ◇ b) ◇ t) (p0 a b))))).symm).trans (p2a (a ◇ b) (b ◇ b))).trans (cg (fun t => (a ◇ b) ◇ t) (p0 b b)))
  have p2e:=fun (a b:G)=>by
    exact (((p2c a b).symm).trans (p24 b (a ◇ b))).trans (p2d a b)
  have p2f:=fun (a b:G)=>by
    exact (((((cg (fun t => (b ◇ (a ◇ b)) ◇ t) (cg (fun t => (a ◇ (a ◇ (a ◇ b))) ◇ t) (p23 b a a))).trans (cg (fun t => (b ◇ (a ◇ b)) ◇ t) (pi a b))).trans (p28 a b a)).symm).trans ((((cg (fun t => t ◇ ((a ◇ (a ◇ (a ◇ b))) ◇ ((a ◇ (a ◇ (a ◇ b))) ◇ b))) (cg (fun t => b ◇ t) (p1f b a))).symm).trans (p1i (a ◇ (a ◇ (a ◇ b))) b)).trans (cg (fun t => (a ◇ (a ◇ (a ◇ b))) ◇ t) (cg (fun t => b ◇ t) (p23 b a a))))).symm
  have p2g:=fun (a b:G)=>by
    exact ((cg (fun t => (a ◇ a) ◇ t) (cg (fun t => b ◇ t) (p24 a b))).symm).trans (((cg (fun t => (a ◇ a) ◇ t) (cg (fun t => b ◇ t) (p25 b a))).symm).trans (pd a a b))
  have p2h:=fun (a b c:G)=>by
    exact ((cg (fun t => t ◇ (c ◇ (a ◇ (a ◇ (b ◇ c))))) (cg (fun t => c ◇ t) (p13 c a))).symm).trans ((((cg (fun t => t ◇ (c ◇ (a ◇ (a ◇ (b ◇ c))))) (cg (fun t => c ◇ t) (cg (fun t => c ◇ t) (cg (fun t => c ◇ t) (p1n a b c))))).symm).trans (py (c ◇ (a ◇ (a ◇ (b ◇ c)))) c)).trans (p1n a b c))
  have p2i:=fun (a b c d:G)=>by
    exact ((cg (fun t => d ◇ t) (cg (fun t => c ◇ t) (cg (fun t => c ◇ t) (p1h a d b)))).symm).trans ((h c d (a ◇ (a ◇ (a ◇ (b ◇ d))))).symm)
  have p2j:=fun (a b c d:G)=>by
    exact ((cg (fun t => (a ◇ b) ◇ t) (cg (fun t => d ◇ t) (cg (fun t => d ◇ t) (pm a b c)))).symm).trans (((cg (fun t => (a ◇ b) ◇ t) (cg (fun t => d ◇ t) (cg (fun t => d ◇ t) (cg (fun t => (a ◇ b) ◇ t) (cg (fun t => c ◇ t) (cg (fun t => c ◇ t) (p12 a b))))))).symm).trans (p2i c (b ◇ b) d (a ◇ b)))
  have p2k:=fun (a b c:G)=>by
    exact ((((cg (fun t => (c ◇ (a ◇ b)) ◇ t) (p2h c a b)).trans (p5 a b c)).symm).trans (((cg (fun t => (c ◇ (a ◇ b)) ◇ t) (cg (fun t => (b ◇ (b ◇ b)) ◇ t) (p1j c a b))).symm).trans (p2j c (a ◇ b) c (b ◇ (b ◇ b))))).symm
  have p2l:=fun (a b c:G)=>by
    exact ((((cg (fun t => (c ◇ c) ◇ t) (pv (c ◇ (b ◇ c)) a)).trans (pd b c a)).symm).trans (((cg (fun t => (c ◇ c) ◇ t) (cg (fun t => (a ◇ (a ◇ (a ◇ (a ◇ (c ◇ (b ◇ c)))))) ◇ t) (py (c ◇ (b ◇ c)) a))).symm).trans (pd b c (a ◇ (a ◇ (a ◇ (a ◇ (c ◇ (b ◇ c))))))))).symm
  have p2m:=fun (a b:G)=>by
    exact (((cg (fun t => t ◇ ((b ◇ b) ◇ (b ◇ b))) (cg (fun t => a ◇ t) (cg (fun t => a ◇ t) (cg (fun t => a ◇ t) (p1x b a))))).trans (cg (fun t => (a ◇ (a ◇ (a ◇ (a ◇ b)))) ◇ t) (p0 b b))).symm).trans ((((cg (fun t => t ◇ ((b ◇ b) ◇ (b ◇ b))) (cg (fun t => a ◇ t) (cg (fun t => a ◇ t) (cg (fun t => a ◇ t) (cg (fun t => a ◇ t) (pe b b)))))).symm).trans (p2l a b (b ◇ b))).trans ((cg (fun t => a ◇ t) (p0 b b)).trans (p25 a b)))
  have p2n:=fun (a b:G)=>by
    exact ((cg (fun t => t ◇ (b ◇ (a ◇ (b ◇ (a ◇ b))))) (py b a)).symm).trans ((((cg (fun t => ((a ◇ (a ◇ (a ◇ (a ◇ b)))) ◇ b) ◇ t) (cg (fun t => b ◇ t) (p2m a b))).symm).trans (p20 b (a ◇ (a ◇ (a ◇ (a ◇ b)))))).trans (cg (fun t => b ◇ t) (py b a)))
  have p2o:=fun (a b:G)=>by
    exact (((((((((cg (fun t => ((b ◇ b) ◇ (b ◇ b)) ◇ t) (cg (fun t => ((b ◇ b) ◇ (b ◇ (a ◇ b))) ◇ t) (cg (fun t => (b ◇ b) ◇ t) (cg (fun t => (b ◇ b) ◇ t) (p0 a b))))).trans (cg (fun t => ((b ◇ b) ◇ (b ◇ b)) ◇ t) (cg (fun t => ((b ◇ b) ◇ (b ◇ (a ◇ b))) ◇ t) (cg (fun t => (b ◇ b) ◇ t) (pe a b))))).trans (cg (fun t => ((b ◇ b) ◇ (b ◇ b)) ◇ t) (cg (fun t => t ◇ ((b ◇ b) ◇ (b ◇ (b ◇ (a ◇ b))))) (pe a b)))).trans (cg (fun t => ((b ◇ b) ◇ (b ◇ b)) ◇ t) (cg (fun t => (b ◇ (b ◇ (a ◇ b))) ◇ t) (p17 a b)))).trans (cg (fun t => t ◇ ((b ◇ (b ◇ (a ◇ b))) ◇ (b ◇ b))) (p0 b b))).trans (cg (fun t => (b ◇ (b ◇ b)) ◇ t) (p29 a b))).trans (p5 b b b)).symm).trans ((((cg (fun t => ((b ◇ b) ◇ (b ◇ b)) ◇ t) (cg (fun t => t ◇ ((b ◇ b) ◇ ((b ◇ b) ◇ ((a ◇ b) ◇ (b ◇ b))))) (cg (fun t => (b ◇ b) ◇ t) (p0 a b)))).symm).trans (pw (a ◇ b) (b ◇ b))).trans (((cg (fun t => t ◇ ((b ◇ b) ◇ (b ◇ b))) (cg (fun t => (b ◇ b) ◇ t) (p0 a b))).trans (cg (fun t => ((b ◇ b) ◇ (b ◇ (a ◇ b))) ◇ t) (p0 b b))).trans (cg (fun t => t ◇ (b ◇ (b ◇ b))) (pe a b))))).symm
  have p2p:=fun (a b:G)=>by
    exact ((((((cg (fun t => (a ◇ (a ◇ (a ◇ b))) ◇ t) (cg (fun t => (a ◇ (a ◇ b)) ◇ t) (cg (fun t => (a ◇ (a ◇ (a ◇ b))) ◇ t) (cg (fun t => (a ◇ (a ◇ b)) ◇ t) (p1e a b))))).trans (cg (fun t => (a ◇ (a ◇ (a ◇ b))) ◇ t) (p1 a (a ◇ (a ◇ b))))).trans (cg (fun t => (a ◇ (a ◇ (a ◇ b))) ◇ t) (p1e a b))).trans (p9 a a a b)).symm).trans ((((cg (fun t => t ◇ ((a ◇ (a ◇ b)) ◇ ((a ◇ (a ◇ (a ◇ b))) ◇ ((a ◇ (a ◇ b)) ◇ ((a ◇ (a ◇ (a ◇ b))) ◇ (a ◇ (a ◇ b))))))) (p1e a b)).symm).trans (p2n (a ◇ (a ◇ (a ◇ b))) (a ◇ (a ◇ b)))).trans (cg (fun t => (a ◇ (a ◇ b)) ◇ t) (p1e a b)))).symm
  have p2q:=fun (a b c:G)=>by
    exact ((cg (fun t => (b ◇ (a ◇ b)) ◇ t) (cg (fun t => b ◇ t) (p1n a c b))).symm).trans ((((cg (fun t => t ◇ (b ◇ (b ◇ (b ◇ (a ◇ (a ◇ (c ◇ b))))))) (cg (fun t => b ◇ t) ((h a b c).symm))).symm).trans (p2p b (a ◇ (a ◇ (c ◇ b))))).trans ((cg (fun t => b ◇ t) (cg (fun t => b ◇ t) (p1n a c b))).trans (p13 b a)))
  have p2r:=fun (a b:G)=>by
    exact ((((cg (fun t => (b ◇ (a ◇ b)) ◇ t) (cg (fun t => (b ◇ (b ◇ (a ◇ b))) ◇ t) (p29 a b))).trans (cg (fun t => (b ◇ (a ◇ b)) ◇ t) (p2o a b))).trans (p1x b (b ◇ (a ◇ b)))).symm).trans ((((cg (fun t => (b ◇ (a ◇ b)) ◇ t) (cg (fun t => (b ◇ (b ◇ (a ◇ b))) ◇ t) (cg (fun t => (b ◇ (b ◇ (a ◇ b))) ◇ t) (p2q a b a)))).symm).trans (p1g (b ◇ (a ◇ b)) (b ◇ (b ◇ (a ◇ b))))).trans (p2q a b ((b ◇ (a ◇ b)) ◇ (b ◇ (b ◇ (a ◇ b))))))
  have p2s:=fun (a b:G)=>by
    exact ((((cg (fun t => b ◇ t) (p2q a b a)).symm).trans (p24 (b ◇ (a ◇ b)) b)).trans (cg (fun t => (b ◇ (a ◇ b)) ◇ t) (p13 b a))).symm
  have p2t:=fun (a b:G)=>by
    exact (((((cg (fun t => t ◇ ((b ◇ (a ◇ b)) ◇ (b ◇ b))) (cg (fun t => (b ◇ (a ◇ b)) ◇ t) (p5 a b b))).trans (cg (fun t => ((b ◇ (a ◇ b)) ◇ (b ◇ (b ◇ (a ◇ b)))) ◇ t) (p2s a b))).trans (cg (fun t => t ◇ (b ◇ (b ◇ b))) (p2q a b ((b ◇ (a ◇ b)) ◇ (b ◇ (b ◇ (a ◇ b))))))).trans (pe b b)).symm).trans ((((cg (fun t => t ◇ ((b ◇ (a ◇ b)) ◇ (b ◇ b))) (cg (fun t => (b ◇ (a ◇ b)) ◇ t) (cg (fun t => (b ◇ (a ◇ b)) ◇ t) (p2s a b)))).symm).trans (pi (b ◇ (a ◇ b)) (b ◇ b))).trans ((cg (fun t => (b ◇ (a ◇ b)) ◇ t) (p2s a b)).trans (p5 a b b)))
  have p2u:=fun (a b c:G)=>by
    exact ((cg (fun t => c ◇ t) (p2t a b)).symm).trans (p1x b c)
  have p2v:=fun (a b c:G)=>by
    exact ((((cg (fun t => c ◇ t) (cg (fun t => (b ◇ (a ◇ b)) ◇ t) (p2u a b (b ◇ (a ◇ b))))).trans (cg (fun t => c ◇ t) (cg (fun t => (b ◇ (a ◇ b)) ◇ t) (p2r a b)))).trans (cg (fun t => c ◇ t) (p2s a b))).symm).trans (((cg (fun t => c ◇ t) (cg (fun t => (b ◇ (a ◇ b)) ◇ t) (cg (fun t => (b ◇ (a ◇ b)) ◇ t) (pe a b)))).symm).trans (p2u (b ◇ b) (b ◇ (a ◇ b)) c))
  have p2w:=fun (a b c:G)=>by
    exact (((p24 b c).symm).trans (((p25 c b).symm).trans (p2v a b c))).symm
  have p2x:=fun (a b c:G)=>by
    exact ((((cg (fun t => c ◇ t) (pe a a)).trans (p2u a a c)).symm).trans ((((cg (fun t => c ◇ t) (cg (fun t => (a ◇ a) ◇ t) (p0 a a))).symm).trans (p2v b (a ◇ a) c)).trans (cg (fun t => c ◇ t) (p1l a a b)))).symm
  have p2y:=fun (a b:G)=>by
    exact ((((cg (fun t => t ◇ (a ◇ b)) (p5 a b b)).trans (pj a b)).symm).trans (((cg (fun t => t ◇ (a ◇ b)) ((p2v a b (b ◇ (a ◇ b))).symm)).symm).trans (pb (a ◇ b) b))).symm
  have p2z:=fun (a b:G)=>by
    exact (((cg (fun t => ((a ◇ (a ◇ (a ◇ b))) ◇ (a ◇ b)) ◇ t) (p4 a b)).trans (cg (fun t => t ◇ (a ◇ b)) (pi a b))).symm).trans ((((cg (fun t => t ◇ (b ◇ (a ◇ (a ◇ (a ◇ b))))) (cg (fun t => (a ◇ (a ◇ (a ◇ b))) ◇ t) (p4 a b))).symm).trans (p2y b (a ◇ (a ◇ (a ◇ b))))).trans ((cg (fun t => (a ◇ (a ◇ (a ◇ b))) ◇ t) (p4 a b)).trans (pi a b)))
  have p30:=fun (a b:G)=>by
    exact (((((cg (fun t => t ◇ (b ◇ (a ◇ b))) (p2u a b (b ◇ (a ◇ b)))).trans (cg (fun t => t ◇ (b ◇ (a ◇ b))) (p2r a b))).trans (pe a b)).symm).trans (((cg (fun t => t ◇ (b ◇ (a ◇ b))) (cg (fun t => (b ◇ (a ◇ b)) ◇ t) (pe a b))).symm).trans (p2r (b ◇ b) (b ◇ (a ◇ b))))).symm
  have p31:=fun (a b c:G)=>by
    exact (((((((cg (fun t => t ◇ (c ◇ (b ◇ (b ◇ (a ◇ b))))) (cg (fun t => (b ◇ (a ◇ b)) ◇ t) (p30 a b))).trans (cg (fun t => ((b ◇ (a ◇ b)) ◇ (b ◇ (b ◇ (a ◇ b)))) ◇ t) (p2u a b c))).trans (cg (fun t => t ◇ (c ◇ b)) (p2u a b (b ◇ (a ◇ b))))).trans (cg (fun t => t ◇ (c ◇ b)) (p2r a b))).trans (p12 c b)).symm).trans ((((cg (fun t => ((b ◇ (a ◇ b)) ◇ ((b ◇ (a ◇ b)) ◇ (b ◇ (a ◇ b)))) ◇ t) (cg (fun t => c ◇ t) (p30 a b))).symm).trans (p2k (b ◇ (a ◇ b)) (b ◇ (a ◇ b)) c)).trans ((cg (fun t => (b ◇ (a ◇ b)) ◇ t) (cg (fun t => c ◇ t) (p30 a b))).trans (cg (fun t => (b ◇ (a ◇ b)) ◇ t) (p2u a b c))))).symm
  have p32:=fun (a b:G)=>by
    exact ((((cg (fun t => t ◇ (a ◇ (a ◇ b))) (p2p a b)).trans (pi a (a ◇ b))).symm).trans (((cg (fun t => t ◇ (a ◇ (a ◇ b))) (cg (fun t => (a ◇ (a ◇ b)) ◇ t) (p1e a b))).symm).trans (p2r (a ◇ (a ◇ (a ◇ b))) (a ◇ (a ◇ b))))).symm
  have p33:=fun (a b:G)=>by
    exact ((((((cg (fun t => t ◇ ((a ◇ b) ◇ (a ◇ b))) (cg (fun t => (b ◇ (a ◇ b)) ◇ t) (p5 a b b))).trans (cg (fun t => t ◇ ((a ◇ b) ◇ (a ◇ b))) (p2u a b (b ◇ (a ◇ b))))).trans (cg (fun t => t ◇ ((a ◇ b) ◇ (a ◇ b))) (p2r a b))).trans (p16 a b)).trans (p2e a b)).symm).trans (((cg (fun t => t ◇ ((a ◇ b) ◇ (a ◇ b))) (cg (fun t => (b ◇ (a ◇ b)) ◇ t) ((p2v a b (b ◇ (a ◇ b))).symm))).symm).trans (p1v b (a ◇ b)))
  have p34:=fun (a b c:G)=>by
    exact ((((cg (fun t => b ◇ t) (cg (fun t => (c ◇ b) ◇ t) (p2r a (c ◇ b)))).trans (pc b c)).symm).trans (((cg (fun t => b ◇ t) (p31 a (c ◇ b) ((c ◇ b) ◇ (a ◇ (c ◇ b))))).symm).trans ((h ((c ◇ b) ◇ (a ◇ (c ◇ b))) b c).symm))).symm
  have p35:=fun (a b:G)=>by
    exact ((p27 (a ◇ (b ◇ (a ◇ (a ◇ b)))) a b).symm).trans ((((cg (fun t => b ◇ t) (cg (fun t => (a ◇ (b ◇ (a ◇ (a ◇ b)))) ◇ t) (cg (fun t => (a ◇ (b ◇ (a ◇ (a ◇ b)))) ◇ t) (p2b a b)))).symm).trans (p1g b (a ◇ (b ◇ (a ◇ (a ◇ b)))))).trans (p2b a b))
  have p36:=fun (a b:G)=>by
    exact (((((((((cg (fun t => t ◇ (((a ◇ (a ◇ b)) ◇ (b ◇ (a ◇ (a ◇ b)))) ◇ ((a ◇ (a ◇ b)) ◇ (b ◇ (a ◇ (a ◇ b)))))) (cg (fun t => (a ◇ b) ◇ t) (cg (fun t => ((a ◇ (a ◇ b)) ◇ (b ◇ (a ◇ (a ◇ b)))) ◇ t) (cg (fun t => (a ◇ b) ◇ t) (p2z a b))))).trans (cg (fun t => t ◇ (((a ◇ (a ◇ b)) ◇ (b ◇ (a ◇ (a ◇ b)))) ◇ ((a ◇ (a ◇ b)) ◇ (b ◇ (a ◇ (a ◇ b)))))) (cg (fun t => (a ◇ b) ◇ t) (p31 b (a ◇ (a ◇ b)) (a ◇ b))))).trans (cg (fun t => t ◇ (((a ◇ (a ◇ b)) ◇ (b ◇ (a ◇ (a ◇ b)))) ◇ ((a ◇ (a ◇ b)) ◇ (b ◇ (a ◇ (a ◇ b)))))) (p1 a (a ◇ b)))).trans (cg (fun t => t ◇ (((a ◇ (a ◇ b)) ◇ (b ◇ (a ◇ (a ◇ b)))) ◇ ((a ◇ (a ◇ b)) ◇ (b ◇ (a ◇ (a ◇ b)))))) (p2z a b))).trans (cg (fun t => (a ◇ (a ◇ b)) ◇ t) (p30 b (a ◇ (a ◇ b))))).trans (p13 (a ◇ (a ◇ b)) b)).trans (p32 a b)).symm).trans ((((cg (fun t => t ◇ (((a ◇ (a ◇ b)) ◇ (b ◇ (a ◇ (a ◇ b)))) ◇ ((a ◇ (a ◇ b)) ◇ (b ◇ (a ◇ (a ◇ b)))))) (cg (fun t => (a ◇ b) ◇ t) (cg (fun t => ((a ◇ (a ◇ b)) ◇ (b ◇ (a ◇ (a ◇ b)))) ◇ t) (cg (fun t => (a ◇ b) ◇ t) (po a b))))).symm).trans (p35 (a ◇ b) ((a ◇ (a ◇ b)) ◇ (b ◇ (a ◇ (a ◇ b)))))).trans ((cg (fun t => (a ◇ b) ◇ t) (p30 b (a ◇ (a ◇ b)))).trans (p2u b (a ◇ (a ◇ b)) (a ◇ b))))).symm
  have p37:=fun (a b:G)=>by
    exact (((p23 b a a).symm).trans (((cg (fun t => t ◇ b) (p36 a b)).symm).trans (p34 a b a))).symm
  have p38:=fun (a b c:G)=>by
    exact (((((cg (fun t => (b ◇ (a ◇ a)) ◇ t) (cg (fun t => (a ◇ a) ◇ t) (cg (fun t => (a ◇ a) ◇ t) (cg (fun t => b ◇ t) (p2w c a b))))).trans (cg (fun t => (b ◇ (a ◇ a)) ◇ t) (cg (fun t => (a ◇ a) ◇ t) (p2g a b)))).trans (cg (fun t => (b ◇ (a ◇ a)) ◇ t) (p1l a a b))).trans (p2x a b (b ◇ (a ◇ a)))).symm).trans ((((cg (fun t => t ◇ ((a ◇ a) ◇ ((a ◇ a) ◇ (b ◇ (b ◇ (a ◇ (c ◇ a))))))) (pd c a b)).symm).trans (p36 (a ◇ a) (b ◇ (b ◇ (a ◇ (c ◇ a)))))).trans (((((cg (fun t => (a ◇ a) ◇ t) (cg (fun t => (a ◇ a) ◇ t) (cg (fun t => (a ◇ a) ◇ t) (cg (fun t => b ◇ t) (p2w c a b))))).trans (cg (fun t => (a ◇ a) ◇ t) (cg (fun t => (a ◇ a) ◇ t) (p2g a b)))).trans (cg (fun t => (a ◇ a) ◇ t) (p1l a a b))).trans (p2x a b (a ◇ a))).trans (p7 a)))
  have p39:=fun (a b:G)=>by
    exact ((((cg (fun t => (b ◇ (b ◇ b)) ◇ t) (p5 b b b)).trans (p10 b b)).trans (p17 b b)).symm).trans ((((cg (fun t => (b ◇ (b ◇ b)) ◇ t) (p38 (b ◇ (b ◇ b)) a a)).symm).trans (p10 b (a ◇ ((b ◇ (b ◇ b)) ◇ (b ◇ (b ◇ b)))))).trans (((((cg (fun t => (b ◇ b) ◇ t) (cg (fun t => t ◇ (b ◇ (b ◇ b))) (cg (fun t => a ◇ t) (p5 b b b)))).trans (cg (fun t => (b ◇ b) ◇ t) (cg (fun t => t ◇ (b ◇ (b ◇ b))) (p2u b b a)))).trans (cg (fun t => (b ◇ b) ◇ t) (p33 a b))).trans (p15 a b)).trans (p37 a b)))
  have p3a:=fun (a b c:G)=>by
    exact (((p39 a c).symm).trans (p39 b c)).symm
  have p3b:=fun (a b:G)=>by
    exact ((((cg (fun t => b ◇ t) (cg (fun t => (a ◇ (b ◇ b)) ◇ t) (cg (fun t => b ◇ t) (p37 a (b ◇ b))))).trans (cg (fun t => b ◇ t) (p2x b a (a ◇ (b ◇ b))))).trans (cg (fun t => b ◇ t) (p38 b a ((a ◇ (b ◇ b)) ◇ b)))).symm).trans ((((cg (fun t => b ◇ t) (cg (fun t => (a ◇ (b ◇ b)) ◇ t) (cg (fun t => b ◇ t) (cg (fun t => (a ◇ (b ◇ b)) ◇ t) (p38 b a a))))).symm).trans (p2b (a ◇ (b ◇ b)) b)).trans (p37 a (b ◇ b)))
  have p3c:=fun (a b c:G)=>by
    exact (((((cg (fun t => (a ◇ a) ◇ t) (cg (fun t => b ◇ t) (p30 c a))).trans (cg (fun t => (a ◇ a) ◇ t) (p2u c a b))).trans (p12 b a)).symm).trans (((cg (fun t => (a ◇ a) ◇ t) (cg (fun t => b ◇ t) ((p39 b (a ◇ (c ◇ a))).symm))).symm).trans (pd c a b))).symm
  have p3d:=fun (a b c:G)=>by
    exact (((cg (fun t => b ◇ t) (p39 a c)).symm).trans ((p3b b c).symm)).symm
  have p3e:=fun (a b c:G)=>by
    exact (((p3a a (b ◇ (b ◇ (b ◇ c))) (b ◇ c)).symm).trans (pi b c)).symm
  have p3f:=fun (a b c:G)=>by
    exact ((cg (fun t => c ◇ t) (p39 a b)).symm).trans (p3c b c a)
  have p3g:=fun (a b c d:G)=>by
    exact ((cg (fun t => d ◇ t) (p39 a d)).symm).trans (p3d b c d)
  have p3h:=fun (a b c:G)=>by
    exact ((cg (fun t => b ◇ t) ((p39 b c).symm)).symm).trans (p3e a b c)
  have p3i:=fun (a b c:G)=>by
    exact ((((cg (fun t => (a ◇ b) ◇ t) (p2u c b (a ◇ (a ◇ b)))).trans (p3f (a ◇ (a ◇ b)) b (a ◇ b))).trans (cg (fun t => b ◇ t) (p37 a b))).symm).trans ((((cg (fun t => (a ◇ b) ◇ t) (cg (fun t => (a ◇ (a ◇ b)) ◇ t) (cg (fun t => b ◇ t) ((p3g c a a b).symm)))).symm).trans (po a b)).trans (p37 a (a ◇ b)))
  have p3j:=fun (a b c:G)=>by
    exact (((cg (fun t => t ◇ b) (p39 a (c ◇ b))).symm).trans (pb b c)).trans (p37 c b)
  have p3k:=fun (a b:G)=>by
    exact (p3h (a ◇ (a ◇ (a ◇ b))) a b).trans (pi a b)
  have p3l:=fun (a b c:G)=>by
    exact (((cg (fun t => (b ◇ c) ◇ t) (p39 a c)).symm).trans (p0 b c)).trans (p3i b c (c ◇ (b ◇ c)))
  have p3m:=fun (a b:G)=>by
    exact ((cg (fun t => t ◇ (b ◇ (b ◇ b))) (p3k a b)).symm).trans ((((cg (fun t => t ◇ (b ◇ (b ◇ b))) (p39 a (b ◇ b))).symm).trans (p2 b (b ◇ b))).trans ((cg (fun t => (b ◇ b) ◇ t) (p0 b b)).trans (pe b b)))
  have p3n:=fun (a b:G)=>by
    exact (((((cg (fun t => t ◇ (b ◇ (a ◇ b))) (p3i a b (b ◇ (a ◇ b)))).trans (cg (fun t => (a ◇ (a ◇ b)) ◇ t) (p3i a b (b ◇ (a ◇ b))))).trans (p3l a a (a ◇ b))).symm).trans ((p39 (a ◇ (a ◇ (a ◇ b))) (b ◇ (a ◇ b))).trans (p2f a b))).symm
  have p3o:=fun (a b c:G)=>by
    exact ((((((cg (fun t => a ◇ t) (cg (fun t => t ◇ ((b ◇ c) ◇ (c ◇ (b ◇ c)))) (cg (fun t => (b ◇ c) ◇ t) (p3i b c (c ◇ (b ◇ c)))))).trans (cg (fun t => a ◇ t) (cg (fun t => ((b ◇ c) ◇ (b ◇ (b ◇ c))) ◇ t) (cg (fun t => (b ◇ c) ◇ t) (p3i b c (c ◇ (b ◇ c))))))).trans (cg (fun t => a ◇ t) (cg (fun t => t ◇ ((b ◇ c) ◇ (b ◇ (b ◇ c)))) (p3i b (b ◇ c) ((b ◇ c) ◇ (b ◇ (b ◇ c))))))).trans (cg (fun t => a ◇ t) (cg (fun t => (b ◇ (b ◇ (b ◇ c))) ◇ t) (p3i b (b ◇ c) ((b ◇ c) ◇ (b ◇ (b ◇ c))))))).trans (cg (fun t => a ◇ t) (p9 b b b c))).symm).trans ((((p3a a ((b ◇ c) ◇ c) (((b ◇ c) ◇ (c ◇ (b ◇ c))) ◇ ((b ◇ c) ◇ (c ◇ (b ◇ c))))).symm).trans (ps b c)).trans ((((cg (fun t => t ◇ ((b ◇ c) ◇ c)) (cg (fun t => (b ◇ c) ◇ t) (p3i b c (c ◇ (b ◇ c))))).trans (cg (fun t => ((b ◇ c) ◇ (b ◇ (b ◇ c))) ◇ t) (p37 b c))).trans (cg (fun t => t ◇ (b ◇ c)) (p3i b (b ◇ c) ((b ◇ c) ◇ (b ◇ (b ◇ c)))))).trans (pi b c)))
  have p3p:=fun (a b c:G)=>by
    exact (((cg (fun t => t ◇ (a ◇ (a ◇ (b ◇ c)))) (cg (fun t => (c ◇ (a ◇ (a ◇ (b ◇ c)))) ◇ t) ((h a c b).symm))).symm).trans (pb (a ◇ (a ◇ (b ◇ c))) c)).trans (p37 c (a ◇ (a ◇ (b ◇ c))))
  have p3q:=fun (a b c:G)=>by
    exact ((((cg (fun t => t ◇ (c ◇ (a ◇ (a ◇ (b ◇ c))))) (p3l a a (a ◇ (b ◇ c)))).trans (p3l c a (a ◇ (a ◇ (b ◇ c))))).symm).trans ((((cg (fun t => ((a ◇ (a ◇ (b ◇ c))) ◇ (a ◇ (a ◇ (b ◇ c)))) ◇ t) (p3p a b c)).symm).trans (p12 ((c ◇ (a ◇ (a ◇ (b ◇ c)))) ◇ (a ◇ c)) (a ◇ (a ◇ (b ◇ c))))).trans ((cg (fun t => (a ◇ (a ◇ (b ◇ c))) ◇ t) (p3p a b c)).trans (p3i c (a ◇ (a ◇ (b ◇ c))) ((a ◇ (a ◇ (b ◇ c))) ◇ (c ◇ (a ◇ (a ◇ (b ◇ c))))))))).symm
  have p3r:=fun (a b c:G)=>by
    exact ((((cg (fun t => (a ◇ (a ◇ (a ◇ c))) ◇ t) (p9 a a b c)).trans (p3i b (a ◇ (a ◇ (a ◇ c))) ((a ◇ (a ◇ (a ◇ c))) ◇ (b ◇ (a ◇ (a ◇ (a ◇ c))))))).symm).trans ((((cg (fun t => (a ◇ (a ◇ (a ◇ c))) ◇ t) (cg (fun t => (a ◇ (a ◇ (a ◇ c))) ◇ t) (cg (fun t => b ◇ t) (cg (fun t => b ◇ t) (p4 a c))))).symm).trans (p3q b c (a ◇ (a ◇ (a ◇ c))))).trans (cg (fun t => b ◇ t) (cg (fun t => b ◇ t) (cg (fun t => b ◇ t) (cg (fun t => b ◇ t) (p4 a c))))))).symm
  have p3s:=fun (a b c:G)=>by
    exact (((((((cg (fun t => (a ◇ (a ◇ (b ◇ c))) ◇ t) (cg (fun t => (a ◇ (a ◇ (b ◇ c))) ◇ t) (cg (fun t => (a ◇ (a ◇ (b ◇ c))) ◇ t) (p37 c (a ◇ (a ◇ (b ◇ c))))))).trans (cg (fun t => (a ◇ (a ◇ (b ◇ c))) ◇ t) (cg (fun t => (a ◇ (a ◇ (b ◇ c))) ◇ t) (p3i c (a ◇ (a ◇ (b ◇ c))) ((a ◇ (a ◇ (b ◇ c))) ◇ (c ◇ (a ◇ (a ◇ (b ◇ c))))))))).trans (cg (fun t => (a ◇ (a ◇ (b ◇ c))) ◇ t) (cg (fun t => (a ◇ (a ◇ (b ◇ c))) ◇ t) (p3q a b c)))).trans (cg (fun t => (a ◇ (a ◇ (b ◇ c))) ◇ t) (p3n a (a ◇ (a ◇ (b ◇ c)))))).trans (cg (fun t => (a ◇ (a ◇ (b ◇ c))) ◇ t) (p3o a a (b ◇ c)))).trans (p3l a a (a ◇ (b ◇ c)))).symm).trans ((((cg (fun t => (a ◇ (a ◇ (b ◇ c))) ◇ t) (cg (fun t => (a ◇ (a ◇ (b ◇ c))) ◇ t) (cg (fun t => (a ◇ (a ◇ (b ◇ c))) ◇ t) (pr a b c)))).symm).trans (p3r (c ◇ (a ◇ (a ◇ (b ◇ c)))) (a ◇ (a ◇ (b ◇ c))) ((a ◇ (a ◇ (b ◇ c))) ◇ (a ◇ c)))).trans (((((((((((((cg (fun t => (a ◇ (a ◇ (b ◇ c))) ◇ t) (cg (fun t => (a ◇ (a ◇ (b ◇ c))) ◇ t) (cg (fun t => (c ◇ (a ◇ (a ◇ (b ◇ c)))) ◇ t) (cg (fun t => (c ◇ (a ◇ (a ◇ (b ◇ c)))) ◇ t) (p3f (a ◇ (a ◇ (b ◇ c))) (a ◇ c) (c ◇ (a ◇ (a ◇ (b ◇ c))))))))).trans (cg (fun t => (a ◇ (a ◇ (b ◇ c))) ◇ t) (cg (fun t => (a ◇ (a ◇ (b ◇ c))) ◇ t) (cg (fun t => (c ◇ (a ◇ (a ◇ (b ◇ c)))) ◇ t) (cg (fun t => (c ◇ (a ◇ (a ◇ (b ◇ c)))) ◇ t) (p3f (c ◇ (a ◇ (a ◇ (b ◇ c)))) (a ◇ c) (a ◇ c))))))).trans (cg (fun t => (a ◇ (a ◇ (b ◇ c))) ◇ t) (cg (fun t => (a ◇ (a ◇ (b ◇ c))) ◇ t) (cg (fun t => (c ◇ (a ◇ (a ◇ (b ◇ c)))) ◇ t) (cg (fun t => (c ◇ (a ◇ (a ◇ (b ◇ c)))) ◇ t) (cg (fun t => (a ◇ c) ◇ t) (p3l a a c))))))).trans (cg (fun t => (a ◇ (a ◇ (b ◇ c))) ◇ t) (cg (fun t => (a ◇ (a ◇ (b ◇ c))) ◇ t) (cg (fun t => (c ◇ (a ◇ (a ◇ (b ◇ c)))) ◇ t) (cg (fun t => (c ◇ (a ◇ (a ◇ (b ◇ c)))) ◇ t) (p3i a (a ◇ c) ((a ◇ c) ◇ (a ◇ (a ◇ c))))))))).trans (cg (fun t => (a ◇ (a ◇ (b ◇ c))) ◇ t) (cg (fun t => (a ◇ (a ◇ (b ◇ c))) ◇ t) (p3f (c ◇ (a ◇ (a ◇ (b ◇ c)))) (a ◇ (a ◇ (a ◇ c))) (c ◇ (a ◇ (a ◇ (b ◇ c)))))))).trans (cg (fun t => (a ◇ (a ◇ (b ◇ c))) ◇ t) (cg (fun t => (a ◇ (a ◇ (b ◇ c))) ◇ t) (p3f (c ◇ (a ◇ (a ◇ (b ◇ c)))) (a ◇ (a ◇ (a ◇ c))) (a ◇ (a ◇ (a ◇ c))))))).trans (cg (fun t => (a ◇ (a ◇ (b ◇ c))) ◇ t) (cg (fun t => (a ◇ (a ◇ (b ◇ c))) ◇ t) (cg (fun t => (a ◇ (a ◇ (a ◇ c))) ◇ t) (p9 a a a c))))).trans (cg (fun t => (a ◇ (a ◇ (b ◇ c))) ◇ t) (cg (fun t => (a ◇ (a ◇ (b ◇ c))) ◇ t) (p3i a (a ◇ (a ◇ (a ◇ c))) ((a ◇ (a ◇ (a ◇ c))) ◇ (a ◇ (a ◇ (a ◇ (a ◇ c))))))))).trans (cg (fun t => (a ◇ (a ◇ (b ◇ c))) ◇ t) (cg (fun t => (a ◇ (a ◇ (b ◇ c))) ◇ t) (p3o a a c)))).trans (p3f (a ◇ (a ◇ (b ◇ c))) (a ◇ (a ◇ c)) (a ◇ (a ◇ (b ◇ c))))).trans (p3f (a ◇ (a ◇ (b ◇ c))) (a ◇ (a ◇ c)) (a ◇ (a ◇ c)))).trans (cg (fun t => (a ◇ (a ◇ c)) ◇ t) (p3l a a (a ◇ c)))).trans (p3i a (a ◇ (a ◇ c)) ((a ◇ (a ◇ c)) ◇ (a ◇ (a ◇ (a ◇ c)))))))
  have p3t:=fun (a b c d:G)=>by
    exact (((cg (fun t => b ◇ t) (cg (fun t => b ◇ t) (cg (fun t => b ◇ t) ((h a c d).symm)))).symm).trans (p3s b c (a ◇ (a ◇ (d ◇ c))))).trans (((p3r a b (a ◇ (d ◇ c))).trans (cg (fun t => b ◇ t) (cg (fun t => b ◇ t) (cg (fun t => a ◇ t) (p3s a d c))))).trans (cg (fun t => b ◇ t) (cg (fun t => b ◇ t) (p3o a a c))))
  have p3u:=fun (a b c:G)=>by
    exact ((cg (fun t => b ◇ t) (cg (fun t => b ◇ t) (p3k b c))).symm).trans ((((cg (fun t => b ◇ t) (cg (fun t => b ◇ t) (cg (fun t => b ◇ t) (p13 c a)))).symm).trans (p3s b c (c ◇ (c ◇ (a ◇ c))))).trans ((((cg (fun t => b ◇ t) (cg (fun t => b ◇ t) (cg (fun t => b ◇ t) (cg (fun t => b ◇ t) (cg (fun t => c ◇ t) (p3i a c (c ◇ (a ◇ c)))))))).trans (cg (fun t => b ◇ t) (cg (fun t => b ◇ t) (cg (fun t => b ◇ t) (cg (fun t => b ◇ t) (p3n a c)))))).trans (cg (fun t => b ◇ t) (p3t a b (a ◇ (a ◇ c)) (b ◇ (b ◇ (b ◇ (a ◇ (a ◇ (a ◇ c))))))))).trans (cg (fun t => b ◇ t) (cg (fun t => b ◇ t) (p3o b a c)))))
  have p3v:=fun (a b c:G)=>by
    exact (((cg (fun t => c ◇ t) ((h c c a).symm)).symm).trans (p3u b c (a ◇ c))).symm
  have p3w:=fun (a b c:G)=>by
    exact ((((((((cg (fun t => t ◇ ((a ◇ (a ◇ (b ◇ c))) ◇ (c ◇ (a ◇ (a ◇ (b ◇ c)))))) (cg (fun t => (a ◇ (a ◇ (b ◇ c))) ◇ t) (p3l a a (a ◇ (b ◇ c))))).trans (cg (fun t => t ◇ ((a ◇ (a ◇ (b ◇ c))) ◇ (c ◇ (a ◇ (a ◇ (b ◇ c)))))) (cg (fun t => (a ◇ (a ◇ (b ◇ c))) ◇ t) (p3s a b c)))).trans (cg (fun t => t ◇ ((a ◇ (a ◇ (b ◇ c))) ◇ (c ◇ (a ◇ (a ◇ (b ◇ c)))))) (p3o (a ◇ (a ◇ (b ◇ c))) a c))).trans (cg (fun t => (a ◇ (a ◇ c)) ◇ t) (p3i c (a ◇ (a ◇ (b ◇ c))) ((a ◇ (a ◇ (b ◇ c))) ◇ (c ◇ (a ◇ (a ◇ (b ◇ c)))))))).trans (cg (fun t => (a ◇ (a ◇ c)) ◇ t) (p3v b a c))).trans (p3m a c)).symm).trans ((((cg (fun t => ((a ◇ (a ◇ (b ◇ c))) ◇ ((a ◇ (a ◇ (b ◇ c))) ◇ (a ◇ (a ◇ (b ◇ c))))) ◇ t) (cg (fun t => (a ◇ (a ◇ (b ◇ c))) ◇ t) (p3p a b c))).symm).trans (p18 ((c ◇ (a ◇ (a ◇ (b ◇ c)))) ◇ (a ◇ c)) (a ◇ (a ◇ (b ◇ c))))).trans (((cg (fun t => (a ◇ (a ◇ (b ◇ c))) ◇ t) (cg (fun t => (a ◇ (a ◇ (b ◇ c))) ◇ t) (p3p a b c))).trans (cg (fun t => (a ◇ (a ◇ (b ◇ c))) ◇ t) (p3i c (a ◇ (a ◇ (b ◇ c))) ((a ◇ (a ◇ (b ◇ c))) ◇ (c ◇ (a ◇ (a ◇ (b ◇ c)))))))).trans (cg (fun t => (a ◇ (a ◇ (b ◇ c))) ◇ t) (p3v b a c))))).symm
  have p3x:=fun (a b c:G)=>by
    exact (((((((((((((((((((((cg (fun t => t ◇ ((b ◇ (a ◇ b)) ◇ ((b ◇ (a ◇ b)) ◇ (c ◇ (b ◇ ((a ◇ b) ◇ b)))))) (cg (fun t => t ◇ (b ◇ (b ◇ (a ◇ b)))) (cg (fun t => (b ◇ ((a ◇ b) ◇ b)) ◇ t) (cg (fun t => (b ◇ (a ◇ b)) ◇ t) (cg (fun t => (b ◇ (a ◇ b)) ◇ t) (cg (fun t => c ◇ t) (cg (fun t => b ◇ t) (p37 a b)))))))).trans (cg (fun t => t ◇ ((b ◇ (a ◇ b)) ◇ ((b ◇ (a ◇ b)) ◇ (c ◇ (b ◇ ((a ◇ b) ◇ b)))))) (cg (fun t => t ◇ (b ◇ (b ◇ (a ◇ b)))) (cg (fun t => (b ◇ ((a ◇ b) ◇ b)) ◇ t) (cg (fun t => (b ◇ (a ◇ b)) ◇ t) (cg (fun t => (b ◇ (a ◇ b)) ◇ t) (cg (fun t => c ◇ t) (p3i a b (b ◇ (a ◇ b)))))))))).trans (cg (fun t => (((b ◇ ((a ◇ b) ◇ b)) ◇ ((b ◇ (a ◇ b)) ◇ ((b ◇ (a ◇ b)) ◇ (c ◇ (a ◇ (a ◇ b)))))) ◇ (b ◇ (b ◇ (a ◇ b)))) ◇ t) (cg (fun t => (b ◇ (a ◇ b)) ◇ t) (cg (fun t => (b ◇ (a ◇ b)) ◇ t) (cg (fun t => c ◇ t) (cg (fun t => b ◇ t) (p37 a b))))))).trans (cg (fun t => t ◇ ((b ◇ (a ◇ b)) ◇ ((b ◇ (a ◇ b)) ◇ (c ◇ (b ◇ (a ◇ b)))))) (cg (fun t => t ◇ (b ◇ (b ◇ (a ◇ b)))) (cg (fun t => (b ◇ ((a ◇ b) ◇ b)) ◇ t) (cg (fun t => (b ◇ (a ◇ b)) ◇ t) (cg (fun t => t ◇ (c ◇ (a ◇ (a ◇ b)))) (p3i a b (b ◇ (a ◇ b))))))))).trans (cg (fun t => t ◇ ((b ◇ (a ◇ b)) ◇ ((b ◇ (a ◇ b)) ◇ (c ◇ (b ◇ (a ◇ b)))))) (cg (fun t => t ◇ (b ◇ (b ◇ (a ◇ b)))) (cg (fun t => t ◇ ((b ◇ (a ◇ b)) ◇ ((a ◇ (a ◇ b)) ◇ (c ◇ (a ◇ (a ◇ b)))))) (cg (fun t => b ◇ t) (p37 a b)))))).trans (cg (fun t => t ◇ ((b ◇ (a ◇ b)) ◇ ((b ◇ (a ◇ b)) ◇ (c ◇ (b ◇ (a ◇ b)))))) (cg (fun t => t ◇ (b ◇ (b ◇ (a ◇ b)))) (cg (fun t => (b ◇ (a ◇ b)) ◇ t) (cg (fun t => t ◇ ((a ◇ (a ◇ b)) ◇ (c ◇ (a ◇ (a ◇ b))))) (p3i a b (b ◇ (a ◇ b)))))))).trans (cg (fun t => (((b ◇ (a ◇ b)) ◇ ((a ◇ (a ◇ b)) ◇ ((a ◇ (a ◇ b)) ◇ (c ◇ (a ◇ (a ◇ b)))))) ◇ (b ◇ (b ◇ (a ◇ b)))) ◇ t) (cg (fun t => (b ◇ (a ◇ b)) ◇ t) (cg (fun t => (b ◇ (a ◇ b)) ◇ t) (cg (fun t => c ◇ t) (p3i a b (b ◇ (a ◇ b)))))))).trans (cg (fun t => t ◇ ((b ◇ (a ◇ b)) ◇ ((b ◇ (a ◇ b)) ◇ (c ◇ (a ◇ (a ◇ b)))))) (cg (fun t => t ◇ (b ◇ (b ◇ (a ◇ b)))) (cg (fun t => (b ◇ (a ◇ b)) ◇ t) (cg (fun t => (a ◇ (a ◇ b)) ◇ t) (p3i c (a ◇ (a ◇ b)) ((a ◇ (a ◇ b)) ◇ (c ◇ (a ◇ (a ◇ b)))))))))).trans (cg (fun t => t ◇ ((b ◇ (a ◇ b)) ◇ ((b ◇ (a ◇ b)) ◇ (c ◇ (a ◇ (a ◇ b)))))) (cg (fun t => t ◇ (b ◇ (b ◇ (a ◇ b)))) (cg (fun t => t ◇ ((a ◇ (a ◇ b)) ◇ (c ◇ (c ◇ (a ◇ (a ◇ b)))))) (p3i a b (b ◇ (a ◇ b))))))).trans (cg (fun t => t ◇ ((b ◇ (a ◇ b)) ◇ ((b ◇ (a ◇ b)) ◇ (c ◇ (a ◇ (a ◇ b)))))) (cg (fun t => ((a ◇ (a ◇ b)) ◇ ((a ◇ (a ◇ b)) ◇ (c ◇ (c ◇ (a ◇ (a ◇ b)))))) ◇ t) (cg (fun t => b ◇ t) (p3i a b (b ◇ (a ◇ b))))))).trans (cg (fun t => (((a ◇ (a ◇ b)) ◇ ((a ◇ (a ◇ b)) ◇ (c ◇ (c ◇ (a ◇ (a ◇ b)))))) ◇ (b ◇ (a ◇ (a ◇ b)))) ◇ t) (cg (fun t => (b ◇ (a ◇ b)) ◇ t) (cg (fun t => t ◇ (c ◇ (a ◇ (a ◇ b)))) (p3i a b (b ◇ (a ◇ b))))))).trans (cg (fun t => t ◇ ((b ◇ (a ◇ b)) ◇ ((a ◇ (a ◇ b)) ◇ (c ◇ (a ◇ (a ◇ b)))))) (cg (fun t => t ◇ (b ◇ (a ◇ (a ◇ b)))) (cg (fun t => (a ◇ (a ◇ b)) ◇ t) (p3n c (a ◇ (a ◇ b))))))).trans (cg (fun t => t ◇ ((b ◇ (a ◇ b)) ◇ ((a ◇ (a ◇ b)) ◇ (c ◇ (a ◇ (a ◇ b)))))) (cg (fun t => t ◇ (b ◇ (a ◇ (a ◇ b)))) (cg (fun t => (a ◇ (a ◇ b)) ◇ t) (p3t a c (a ◇ b) (c ◇ (c ◇ (c ◇ (a ◇ (a ◇ b)))))))))).trans (cg (fun t => (((a ◇ (a ◇ b)) ◇ (c ◇ (c ◇ (a ◇ (a ◇ (a ◇ b)))))) ◇ (b ◇ (a ◇ (a ◇ b)))) ◇ t) (cg (fun t => t ◇ ((a ◇ (a ◇ b)) ◇ (c ◇ (a ◇ (a ◇ b))))) (p3i a b (b ◇ (a ◇ b)))))).trans (cg (fun t => t ◇ ((a ◇ (a ◇ b)) ◇ ((a ◇ (a ◇ b)) ◇ (c ◇ (a ◇ (a ◇ b)))))) (cg (fun t => ((a ◇ (a ◇ b)) ◇ (c ◇ (c ◇ (a ◇ (a ◇ (a ◇ b)))))) ◇ t) (p3n a b)))).trans (cg (fun t => (((a ◇ (a ◇ b)) ◇ (c ◇ (c ◇ (a ◇ (a ◇ (a ◇ b)))))) ◇ (a ◇ (a ◇ (a ◇ b)))) ◇ t) (cg (fun t => (a ◇ (a ◇ b)) ◇ t) (p3i c (a ◇ (a ◇ b)) ((a ◇ (a ◇ b)) ◇ (c ◇ (a ◇ (a ◇ b)))))))).trans (cg (fun t => t ◇ ((a ◇ (a ◇ b)) ◇ (c ◇ (c ◇ (a ◇ (a ◇ b)))))) (cg (fun t => t ◇ (a ◇ (a ◇ (a ◇ b)))) (pk a (a ◇ b) c)))).trans (cg (fun t => t ◇ ((a ◇ (a ◇ b)) ◇ (c ◇ (c ◇ (a ◇ (a ◇ b)))))) (p3l a c (a ◇ (a ◇ b))))).trans (cg (fun t => (c ◇ (c ◇ (a ◇ (a ◇ b)))) ◇ t) (p3n c (a ◇ (a ◇ b))))).trans (cg (fun t => (c ◇ (c ◇ (a ◇ (a ◇ b)))) ◇ t) (p3t a c (a ◇ b) (c ◇ (c ◇ (c ◇ (a ◇ (a ◇ b)))))))).symm).trans ((((cg (fun t => t ◇ ((b ◇ (a ◇ b)) ◇ ((b ◇ (a ◇ b)) ◇ (c ◇ (b ◇ ((a ◇ b) ◇ b)))))) (cg (fun t => ((b ◇ ((a ◇ b) ◇ b)) ◇ ((b ◇ (a ◇ b)) ◇ ((b ◇ (a ◇ b)) ◇ (c ◇ (b ◇ ((a ◇ b) ◇ b)))))) ◇ t) (pl a b))).symm).trans (p3p (b ◇ (a ◇ b)) c (b ◇ ((a ◇ b) ◇ b)))).trans ((((((((((cg (fun t => (b ◇ ((a ◇ b) ◇ b)) ◇ t) (cg (fun t => (b ◇ (a ◇ b)) ◇ t) (cg (fun t => (b ◇ (a ◇ b)) ◇ t) (cg (fun t => c ◇ t) (cg (fun t => b ◇ t) (p37 a b)))))).trans (cg (fun t => (b ◇ ((a ◇ b) ◇ b)) ◇ t) (cg (fun t => (b ◇ (a ◇ b)) ◇ t) (cg (fun t => (b ◇ (a ◇ b)) ◇ t) (cg (fun t => c ◇ t) (p3i a b (b ◇ (a ◇ b)))))))).trans (cg (fun t => (b ◇ ((a ◇ b) ◇ b)) ◇ t) (cg (fun t => (b ◇ (a ◇ b)) ◇ t) (cg (fun t => t ◇ (c ◇ (a ◇ (a ◇ b)))) (p3i a b (b ◇ (a ◇ b))))))).trans (cg (fun t => t ◇ ((b ◇ (a ◇ b)) ◇ ((a ◇ (a ◇ b)) ◇ (c ◇ (a ◇ (a ◇ b)))))) (cg (fun t => b ◇ t) (p37 a b)))).trans (cg (fun t => (b ◇ (a ◇ b)) ◇ t) (cg (fun t => t ◇ ((a ◇ (a ◇ b)) ◇ (c ◇ (a ◇ (a ◇ b))))) (p3i a b (b ◇ (a ◇ b)))))).trans (cg (fun t => (b ◇ (a ◇ b)) ◇ t) (cg (fun t => (a ◇ (a ◇ b)) ◇ t) (p3i c (a ◇ (a ◇ b)) ((a ◇ (a ◇ b)) ◇ (c ◇ (a ◇ (a ◇ b)))))))).trans (cg (fun t => t ◇ ((a ◇ (a ◇ b)) ◇ (c ◇ (c ◇ (a ◇ (a ◇ b)))))) (p3i a b (b ◇ (a ◇ b))))).trans (cg (fun t => (a ◇ (a ◇ b)) ◇ t) (p3n c (a ◇ (a ◇ b))))).trans (cg (fun t => (a ◇ (a ◇ b)) ◇ t) (p3t a c (a ◇ b) (c ◇ (c ◇ (c ◇ (a ◇ (a ◇ b)))))))).trans (pk a (a ◇ b) c)))
  have p3y:=fun (a b c d:G)=>by
    exact (((((((cg (fun t => (d ◇ (d ◇ (c ◇ (a ◇ (a ◇ b))))) ◇ t) (cg (fun t => (c ◇ (c ◇ (a ◇ (a ◇ (a ◇ b))))) ◇ t) (p3l c c (c ◇ (a ◇ (a ◇ (a ◇ b))))))).trans (cg (fun t => (d ◇ (d ◇ (c ◇ (a ◇ (a ◇ b))))) ◇ t) (cg (fun t => (c ◇ (c ◇ (a ◇ (a ◇ (a ◇ b))))) ◇ t) (p3t a c (a ◇ (a ◇ b)) (c ◇ (c ◇ (c ◇ (a ◇ (a ◇ (a ◇ b)))))))))).trans (cg (fun t => (d ◇ (d ◇ (c ◇ (a ◇ (a ◇ b))))) ◇ t) (cg (fun t => (c ◇ (c ◇ (a ◇ (a ◇ (a ◇ b))))) ◇ t) (cg (fun t => c ◇ t) (p3o c a b))))).trans (p3f (c ◇ (c ◇ (a ◇ (a ◇ (a ◇ b))))) (c ◇ (a ◇ (a ◇ b))) (d ◇ (d ◇ (c ◇ (a ◇ (a ◇ b))))))).trans (cg (fun t => (c ◇ (a ◇ (a ◇ b))) ◇ t) (p3j d (c ◇ (a ◇ (a ◇ b))) d))).trans (p3i d (c ◇ (a ◇ (a ◇ b))) ((c ◇ (a ◇ (a ◇ b))) ◇ (d ◇ (c ◇ (a ◇ (a ◇ b))))))).symm).trans ((((cg (fun t => t ◇ ((c ◇ (c ◇ (a ◇ (a ◇ (a ◇ b))))) ◇ ((c ◇ (c ◇ (a ◇ (a ◇ (a ◇ b))))) ◇ (c ◇ (c ◇ (a ◇ (a ◇ (a ◇ b)))))))) (cg (fun t => d ◇ t) (cg (fun t => d ◇ t) (p3x a b c)))).symm).trans (p3w d (c ◇ (c ◇ (a ◇ (a ◇ b)))) (c ◇ (c ◇ (a ◇ (a ◇ (a ◇ b))))))).trans ((((((((cg (fun t => (c ◇ (c ◇ (a ◇ (a ◇ (a ◇ b))))) ◇ t) (cg (fun t => (c ◇ (c ◇ (a ◇ (a ◇ (a ◇ b))))) ◇ t) (p3l c c (c ◇ (a ◇ (a ◇ (a ◇ b))))))).trans (cg (fun t => (c ◇ (c ◇ (a ◇ (a ◇ (a ◇ b))))) ◇ t) (cg (fun t => (c ◇ (c ◇ (a ◇ (a ◇ (a ◇ b))))) ◇ t) (p3t a c (a ◇ (a ◇ b)) (c ◇ (c ◇ (c ◇ (a ◇ (a ◇ (a ◇ b)))))))))).trans (cg (fun t => (c ◇ (c ◇ (a ◇ (a ◇ (a ◇ b))))) ◇ t) (cg (fun t => (c ◇ (c ◇ (a ◇ (a ◇ (a ◇ b))))) ◇ t) (cg (fun t => c ◇ t) (p3o c a b))))).trans (p3f (c ◇ (c ◇ (a ◇ (a ◇ (a ◇ b))))) (c ◇ (a ◇ (a ◇ b))) (c ◇ (c ◇ (a ◇ (a ◇ (a ◇ b))))))).trans (p3f (c ◇ (c ◇ (a ◇ (a ◇ (a ◇ b))))) (c ◇ (a ◇ (a ◇ b))) (c ◇ (a ◇ (a ◇ b))))).trans (cg (fun t => (c ◇ (a ◇ (a ◇ b))) ◇ t) (p3l c c (a ◇ (a ◇ b))))).trans (p3i c (c ◇ (a ◇ (a ◇ b))) ((c ◇ (a ◇ (a ◇ b))) ◇ (c ◇ (c ◇ (a ◇ (a ◇ b))))))).trans (p3t a c (a ◇ b) (c ◇ (c ◇ (c ◇ (a ◇ (a ◇ b))))))))
  have p3z:=fun (a b c d:G)=>by
    exact ((((cg (fun t => ((a ◇ (d ◇ (b ◇ (b ◇ c)))) ◇ (a ◇ (d ◇ (b ◇ (b ◇ c))))) ◇ t) (p37 a (d ◇ (b ◇ (b ◇ c))))).trans (cg (fun t => t ◇ (a ◇ (d ◇ (b ◇ (b ◇ c))))) (p3l a a (d ◇ (b ◇ (b ◇ c)))))).trans (p37 a (a ◇ (d ◇ (b ◇ (b ◇ c)))))).symm).trans ((((cg (fun t => ((a ◇ (d ◇ (b ◇ (b ◇ c)))) ◇ (a ◇ (d ◇ (b ◇ (b ◇ c))))) ◇ t) (pb (d ◇ (b ◇ (b ◇ c))) a)).symm).trans (p3y b c d ((a ◇ (d ◇ (b ◇ (b ◇ c)))) ◇ (a ◇ (d ◇ (b ◇ (b ◇ c))))))).trans ((p3y b c b d).trans (p3o b b c)))
  have p40:=fun (a b c d:G)=>by
    exact (((cg (fun t => b ◇ t) (cg (fun t => b ◇ t) ((h c d a).symm))).symm).trans (p3z b c (a ◇ d) d)).symm
  have p41:=fun (a b c d e:G)=>by
    exact ((((cg (fun t => c ◇ t) (p40 e a c b)).symm).trans (p40 c d c (e ◇ b))).trans ((cg (fun t => d ◇ t) (cg (fun t => d ◇ t) (p3f e b c))).trans (cg (fun t => d ◇ t) (cg (fun t => d ◇ t) (p3f c b b))))).symm
  have p42:=fun (a b c d:G)=>by
    exact ((p40 a c b (b ◇ d)).trans ((p3u b c d).symm)).symm
  have p43:=fun (a b c d e:G)=>by
    exact (((cg (fun t => d ◇ t) (p3o d b c)).symm).trans ((((cg (fun t => d ◇ t) (cg (fun t => d ◇ t) ((p42 a d b c).symm))).symm).trans ((p41 d (a ◇ (d ◇ c)) d e a).symm)).trans ((((cg (fun t => e ◇ t) (cg (fun t => e ◇ t) (cg (fun t => (a ◇ (d ◇ c)) ◇ t) (p3l a a (d ◇ c))))).trans (cg (fun t => e ◇ t) (cg (fun t => e ◇ t) (p3i a (a ◇ (d ◇ c)) ((a ◇ (d ◇ c)) ◇ (a ◇ (a ◇ (d ◇ c)))))))).trans (cg (fun t => e ◇ t) (cg (fun t => e ◇ t) (p3s a d c)))).trans (cg (fun t => e ◇ t) (p3o e a c))))).symm
  have p44:=fun (a b c d:G)=>by
    exact ((p43 c a (c ◇ d) b d).symm).trans (p4 c d)
  have p45:=fun (a b c:G)=>by
    exact (((((((cg (fun t => (c ◇ (a ◇ c)) ◇ t) (cg (fun t => c ◇ t) (p3i a c (c ◇ (a ◇ c))))).trans (cg (fun t => t ◇ (c ◇ (a ◇ (a ◇ c)))) (p3i a c (c ◇ (a ◇ c))))).trans (cg (fun t => (a ◇ (a ◇ c)) ◇ t) (p3n a c))).trans (p3i a (a ◇ (a ◇ c)) ((a ◇ (a ◇ c)) ◇ (a ◇ (a ◇ (a ◇ c)))))).trans (p44 a a a c)).symm).trans ((((cg (fun t => (c ◇ (a ◇ c)) ◇ t) (pl a c)).symm).trans ((p40 b (c ◇ (a ◇ c)) c ((a ◇ c) ◇ c)).symm)).trans (cg (fun t => c ◇ t) (cg (fun t => c ◇ t) (cg (fun t => b ◇ t) (p37 a c)))))).symm
  exact (p3a w x y).trans ((p45 w z y).symm)

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_41890_to_41953 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_41890_to_41953
