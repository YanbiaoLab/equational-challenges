-- Equation19023 → Equation57632
-- Recorded verdict: true
-- Premise: x = (y ◇ x) ◇ ((z ◇ y) ◇ (x ◇ z))
-- Conclusion: x ◇ (y ◇ x) = ((z ◇ z) ◇ y) ◇ z
-- Original submission SHA-256: b51483d1ea5c56cebeb045bd0df5bec544db94ccc2de3b2272a1704fc48d123b
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
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x ◇ (y ◇ x) = ((z ◇ z) ◇ y) ◇ z
abbrev Goal : Prop := ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G
end

-- Original submission body
                   
def submission : Goal := by
 intro G _ h
 have t : ∀ {a b : G} (P : G → Prop), P a → a = b → P b :=
  fun {a b} P hp e => @Eq.ndrec G a P hp b e
 have h3 (x y z : G) :
   ((x◇y)◇((z◇x)◇(y◇z))) = y := by
  exact (h y x z).symm
 have h5 (x y z u : G):(x◇((y◇(z◇x))◇(((u◇z)◇(x◇u))◇y))) = ((u◇z)◇(x◇u)):=by
  have s0:=(t (fun q => (q◇((y◇(z◇x))◇(((u◇z)◇(x◇u))◇y))) = ((u◇z)◇(x◇u))) (h3 (z◇x) ((u◇z)◇(x◇u)) y) (h3 z x u))
  exact s0
 have h6 (x y z u : G):((((x◇y)◇(z◇x))◇u)◇(z◇(u◇(y◇z)))) = u:=by
  have s0:=(t (fun q => ((((x◇y)◇(z◇x))◇u)◇(q◇(u◇(y◇z)))) = u) (h3 ((x◇y)◇(z◇x)) u (y◇z)) (h3 y z x))
  exact s0
 have h7 (x y z u : G):((x◇(y◇z))◇((((u◇y)◇(z◇u))◇x)◇z)) = (y◇z):=by
  have s0:=(t (fun q => ((x◇(y◇z))◇((((u◇y)◇(z◇u))◇x)◇q)) = (y◇z)) (h3 x (y◇z) ((u◇y)◇(z◇u))) (h3 y z u))
  exact s0
 have h8 (x y : G):((x◇(y◇(x◇y)))◇x) = (y◇(x◇y)):=by
  have s0:=(t (fun q => ((x◇(y◇(x◇y)))◇q) = (y◇(x◇y))) (h3 x (y◇(x◇y)) (x◇y)) (h3 (x◇y) x y))
  exact s0
 have h9 (x y z u w : G):(((x◇y)◇(z◇x))◇((u◇z)◇(((w◇(y◇z))◇(((x◇y)◇(z◇x))◇w))◇u))) = ((w◇(y◇z))◇(((x◇y)◇(z◇x))◇w)):=by
  have s0:=(t (fun q => (q◇((u◇z)◇(((w◇(y◇z))◇(((x◇y)◇(z◇x))◇w))◇u))) = ((w◇(y◇z))◇(((x◇y)◇(z◇x))◇w))) (h3 z ((w◇(y◇z))◇(((x◇y)◇(z◇x))◇w)) u) (h5 z w y x))
  exact s0
 have h10 (x y z u w : G):((((x◇(y◇z))◇(((u◇y)◇(z◇u))◇x))◇w)◇(((u◇y)◇(z◇u))◇(w◇z))) = w:=by
  have s0:=(t (fun q => ((((x◇(y◇z))◇(((u◇y)◇(z◇u))◇x))◇w)◇(q◇(w◇z))) = w) (h3 ((x◇(y◇z))◇(((u◇y)◇(z◇u))◇x)) w z) (h5 z x y u))
  exact s0
 have h11 (x y z u w : G):((x◇y)◇((((z◇(u◇y))◇(((w◇u)◇(y◇w))◇z))◇x)◇((w◇u)◇(y◇w)))) = y:=by
  have s0:=(t (fun q => ((x◇y)◇((((z◇(u◇y))◇(((w◇u)◇(y◇w))◇z))◇x)◇q)) = y) (h3 x y ((z◇(u◇y))◇(((w◇u)◇(y◇w))◇z))) (h5 y z u w))
  exact s0
 have h12 (x y z u : G):((x◇y)◇(x◇(((z◇(y◇u))◇((x◇y)◇z))◇(u◇x)))) = ((z◇(y◇u))◇((x◇y)◇z)):=by
  have s0:=(t (fun q => ((x◇y)◇(q◇(((z◇(y◇u))◇((x◇y)◇z))◇(u◇x)))) = ((z◇(y◇u))◇((x◇y)◇z))) (h5 (x◇y) (u◇x) (y◇u) z) (h3 u x y))
  exact s0
 have h15 (x y z : G):((x◇(y◇x))◇((z◇(y◇(x◇(y◇x))))◇(y◇z))) = y:=by
  have s0:=(t (fun q => ((x◇(y◇x))◇((z◇(y◇(x◇(y◇x))))◇(q◇z))) = (((y◇x)◇y)◇((x◇(y◇x))◇(y◇x)))) (h5 (x◇(y◇x)) z y (y◇x)) (h3 (y◇x) y x))
  have s1:=(t (fun q => ((x◇(y◇x))◇((z◇(y◇(x◇(y◇x))))◇(y◇z))) = q) s0 (h3 (y◇x) y x))
  exact s1
 have h16 (x y z u : G):(x◇((((y◇(z◇u))◇((x◇z)◇y))◇(u◇x))◇(x◇z))) = ((z◇u)◇(x◇z)):=by
  have s0:=(t (fun q => (x◇((((y◇(z◇u))◇((x◇z)◇y))◇(u◇x))◇q)) = ((z◇u)◇(x◇z))) (h5 x ((y◇(z◇u))◇((x◇z)◇y)) u z) (h3 (z◇u) (x◇z) y))
  exact s0
 have h18 (x y z u w : G):((((x◇y)◇(z◇x))◇u)◇(((x◇y)◇(z◇x))◇(((w◇(u◇(y◇z)))◇((((x◇y)◇(z◇x))◇u)◇w))◇z))) = ((w◇(u◇(y◇z)))◇((((x◇y)◇(z◇x))◇u)◇w)):=by
  have s0:=(t (fun q => ((((x◇y)◇(z◇x))◇u)◇(q◇(((w◇(u◇(y◇z)))◇((((x◇y)◇(z◇x))◇u)◇w))◇z))) = ((w◇(u◇(y◇z)))◇((((x◇y)◇(z◇x))◇u)◇w))) (h5 (((x◇y)◇(z◇x))◇u) z (u◇(y◇z)) w) (h5 z u y x))
  exact s0
 have h21 (x y z u w v5 : G):(x◇((((y◇(z◇((u◇w)◇(x◇u))))◇(((v5◇z)◇(((u◇w)◇(x◇u))◇v5))◇y))◇(w◇x))◇((v5◇z)◇(((u◇w)◇(x◇u))◇v5)))) = ((u◇w)◇(x◇u)):=by
  have s0:=(t (fun q => (x◇((((y◇(z◇((u◇w)◇(x◇u))))◇(((v5◇z)◇(((u◇w)◇(x◇u))◇v5))◇y))◇(w◇x))◇q)) = ((u◇w)◇(x◇u))) (h5 x ((y◇(z◇((u◇w)◇(x◇u))))◇(((v5◇z)◇(((u◇w)◇(x◇u))◇v5))◇y)) w u) (h5 ((u◇w)◇(x◇u)) y z v5))
  exact s0
 have h22 (x y z : G):((x◇y)◇((z◇(x◇z))◇(y◇(x◇(z◇(x◇z)))))) = y:=by
  have s0:=(t (fun q => ((x◇y)◇(q◇(y◇(x◇(z◇(x◇z)))))) = y) (h3 x y (x◇(z◇(x◇z)))) (h8 x z))
  exact s0
 have h23 (x y z : G):((x◇(y◇(z◇(y◇z))))◇((y◇x)◇(z◇(y◇z)))) = (y◇(z◇(y◇z))):=by
  have s0:=(t (fun q => ((x◇(y◇(z◇(y◇z))))◇((y◇x)◇q)) = (y◇(z◇(y◇z)))) (h3 x (y◇(z◇(y◇z))) y) (h8 y z))
  exact s0
 have h24 (x y z : G):(((x◇y)◇(((z◇x)◇(y◇z))◇y))◇(x◇y)) = (((z◇x)◇(y◇z))◇y):=by
  have s0:=(t (fun q => (((x◇y)◇(((z◇x)◇(y◇z))◇q))◇(x◇y)) = (((z◇x)◇(y◇z))◇((x◇y)◇((z◇x)◇(y◇z))))) (h8 (x◇y) ((z◇x)◇(y◇z))) (h3 x y z))
  have s1:=(t (fun q => (((x◇y)◇(((z◇x)◇(y◇z))◇y))◇(x◇y)) = (((z◇x)◇(y◇z))◇q)) s0 (h3 x y z))
  exact s1
 have h25 (x : G):(((x◇x)◇x)◇(x◇x)) = x:=by
  have s0:=(t (fun q => (((x◇x)◇q)◇(x◇x)) = ((x◇x)◇((x◇x)◇(x◇x)))) (h8 (x◇x) (x◇x)) (h3 x x x))
  have s1:=(t (fun q => (((x◇x)◇x)◇(x◇x)) = q) s0 (h3 x x x))
  exact s1
 have h28 (x y z u : G):(x◇((y◇(z◇x))◇(((u◇(z◇u))◇(x◇(z◇(u◇(z◇u)))))◇y))) = ((u◇(z◇u))◇(x◇(z◇(u◇(z◇u))))):=by
  have s0:=(t (fun q => (x◇((y◇(z◇x))◇((q◇(x◇(z◇(u◇(z◇u)))))◇y))) = (((z◇(u◇(z◇u)))◇z)◇(x◇(z◇(u◇(z◇u)))))) (h5 x y z (z◇(u◇(z◇u)))) (h8 z u))
  have s1:=(t (fun q => (x◇((y◇(z◇x))◇(((u◇(z◇u))◇(x◇(z◇(u◇(z◇u)))))◇y))) = (q◇(x◇(z◇(u◇(z◇u)))))) s0 (h8 z u))
  exact s1
 have h29 (x y z u : G):((x◇(y◇(x◇y)))◇((z◇(u◇(x◇(y◇(x◇y)))))◇(((x◇u)◇(y◇(x◇y)))◇z))) = ((x◇u)◇(y◇(x◇y))):=by
  have s0:=(t (fun q => ((x◇(y◇(x◇y)))◇((z◇(u◇(x◇(y◇(x◇y)))))◇(((x◇u)◇q)◇z))) = ((x◇u)◇((x◇(y◇(x◇y)))◇x))) (h5 (x◇(y◇(x◇y))) z u x) (h8 x y))
  have s1:=(t (fun q => ((x◇(y◇(x◇y)))◇((z◇(u◇(x◇(y◇(x◇y)))))◇(((x◇u)◇(y◇(x◇y)))◇z))) = ((x◇u)◇q)) s0 (h8 x y))
  exact s1
 have h31 (x y : G):(((x◇(y◇(x◇y)))◇(x◇(y◇(x◇y))))◇(x◇(y◇(x◇y)))) = (x◇(y◇(x◇y))):=by
  have s0:=(t (fun q => (((x◇(y◇(x◇y)))◇(x◇q))◇(x◇(y◇(x◇y)))) = (x◇((x◇(y◇(x◇y)))◇x))) (h8 (x◇(y◇(x◇y))) x) (h8 x y))
  have s1:=(t (fun q => (((x◇(y◇(x◇y)))◇(x◇(y◇(x◇y))))◇(x◇(y◇(x◇y)))) = (x◇q)) s0 (h8 x y))
  exact s1
 have h32 (x y : G):(x◇((y◇((x◇x)◇x))◇((x◇x)◇y))) = (x◇x):=by
  have s0:=(t (fun q => (q◇((y◇((x◇x)◇x))◇((x◇x)◇y))) = (x◇x)) (h3 ((x◇x)◇x) (x◇x) y) (h25 x))
  exact s0
 have h33 (x y : G):(((x◇x)◇y)◇(x◇(y◇((x◇x)◇x)))) = y:=by
  have s0:=(t (fun q => (((x◇x)◇y)◇(q◇(y◇((x◇x)◇x)))) = y) (h3 (x◇x) y ((x◇x)◇x)) (h25 x))
  exact s0
 have h34 (x y : G):((x◇((y◇y)◇y))◇(((y◇y)◇x)◇y)) = ((y◇y)◇y):=by
  have s0:=(t (fun q => ((x◇((y◇y)◇y))◇(((y◇y)◇x)◇q)) = ((y◇y)◇y)) (h3 x ((y◇y)◇y) (y◇y)) (h25 y))
  exact s0
 have h39 (x : G):((((x◇x)◇x)◇((x◇x)◇x))◇((x◇x)◇x)) = ((x◇x)◇x):=by
  have s0:=(t (fun q => ((((x◇x)◇x)◇((x◇x)◇q))◇((x◇x)◇x)) = ((x◇x)◇(((x◇x)◇x)◇(x◇x)))) (h8 ((x◇x)◇x) (x◇x)) (h25 x))
  have s1:=(t (fun q => ((((x◇x)◇x)◇((x◇x)◇x))◇((x◇x)◇x)) = ((x◇x)◇q)) s0 (h25 x))
  exact s1
 have h40 (x y z : G):(((x◇(y◇((x◇x)◇x)))◇z)◇(y◇(z◇((x◇x)◇y)))) = z:=by
  have s0:=(t (fun q => (((x◇(y◇((x◇x)◇x)))◇z)◇(q◇(z◇((x◇x)◇y)))) = z) (h3 (x◇(y◇((x◇x)◇x))) z ((x◇x)◇y)) (h33 x y))
  exact s0
 have h51 (x y z u w : G):(((x◇(y◇(z◇x)))◇u)◇(y◇(u◇(((w◇z)◇(x◇w))◇y)))) = u:=by
  have s0:=(t (fun q => (((x◇(y◇(z◇x)))◇u)◇(q◇(u◇(((w◇z)◇(x◇w))◇y)))) = u) (h3 (x◇(y◇(z◇x))) u (((w◇z)◇(x◇w))◇y)) (h6 w z x y))
  exact s0
 have h52 (x y z u w : G):((x◇(((y◇z)◇(u◇y))◇w))◇(((u◇(w◇(z◇u)))◇x)◇w)) = (((y◇z)◇(u◇y))◇w):=by
  have s0:=(t (fun q => ((x◇(((y◇z)◇(u◇y))◇w))◇(((u◇(w◇(z◇u)))◇x)◇q)) = (((y◇z)◇(u◇y))◇w)) (h3 x (((y◇z)◇(u◇y))◇w) (u◇(w◇(z◇u)))) (h6 y z u w))
  exact s0
 have h54 (x y z u : G):((((x◇(y◇z))◇((u◇y)◇x))◇(z◇u))◇((u◇y)◇u)) = (z◇u):=by
  have s0:=(t (fun q => ((((x◇(y◇z))◇((u◇y)◇x))◇(z◇u))◇((u◇y)◇q)) = (z◇u)) (h6 x (y◇z) (u◇y) (z◇u)) (h3 z u y))
  exact s0
 have h55 (x y z : G):((((x◇y)◇((z◇y)◇x))◇((z◇y)◇z))◇y) = ((z◇y)◇z):=by
  have s0:=(t (fun q => ((((x◇y)◇((z◇y)◇x))◇((z◇y)◇z))◇q) = ((z◇y)◇z)) (h6 x y (z◇y) ((z◇y)◇z)) (h3 z y (z◇y)))
  exact s0
 have h64 (x y z u w v5 : G):((((x◇y)◇(((z◇(u◇y))◇(((w◇u)◇(y◇w))◇z))◇x))◇v5)◇(((z◇(u◇y))◇(((w◇u)◇(y◇w))◇z))◇(v5◇((w◇u)◇(y◇w))))) = v5:=by
  have s0:=(t (fun q => ((((x◇y)◇(((z◇(u◇y))◇(((w◇u)◇(y◇w))◇z))◇x))◇v5)◇(((z◇(u◇y))◇(((w◇u)◇(y◇w))◇z))◇(v5◇q))) = v5) (h6 x y ((z◇(u◇y))◇(((w◇u)◇(y◇w))◇z)) v5) (h5 y z u w))
  exact s0
 have h74 (x y : G):((((x◇y)◇(y◇x))◇((y◇y)◇y))◇(y◇y)) = ((y◇y)◇y):=by
  have s0:=(t (fun q => ((((x◇y)◇(y◇x))◇((y◇y)◇y))◇(y◇q)) = ((y◇y)◇y)) (h6 x y y ((y◇y)◇y)) (h25 y))
  exact s0
 have h81 (x y : G):((((x◇y)◇(((y◇y)◇y)◇x))◇y)◇y) = y:=by
  have s0:=(t (fun q => ((((x◇y)◇(((y◇y)◇y)◇x))◇y)◇q) = y) (h6 x y ((y◇y)◇y) y) (h33 y y))
  exact s0
 have h93 (x y z u : G):(x◇((((((y◇x)◇(z◇y))◇(z◇u))◇z)◇(u◇x))◇(x◇z))) = ((z◇u)◇(x◇z)):=by
  have s0:=(t (fun q => (x◇((((((y◇x)◇(z◇y))◇(z◇u))◇z)◇(u◇x))◇q)) = ((z◇u)◇(x◇z))) (h5 x ((((y◇x)◇(z◇y))◇(z◇u))◇z) u z) (h7 (z◇u) x z y))
  exact s0
 have h104 (x y z : G):((x◇y)◇((((z◇((y◇y)◇y))◇((y◇y)◇z))◇x)◇(y◇y))) = y:=by
  have s0:=(t (fun q => ((x◇q)◇((((z◇((y◇y)◇y))◇((y◇y)◇z))◇x)◇(y◇y))) = (((y◇y)◇y)◇(y◇y))) (h7 x ((y◇y)◇y) (y◇y) z) (h25 y))
  have s1:=(t (fun q => ((x◇y)◇((((z◇((y◇y)◇y))◇((y◇y)◇z))◇x)◇(y◇y))) = q) s0 (h25 y))
  exact s1
 have h105 (x y : G):(x◇((((y◇x)◇(x◇y))◇((x◇x)◇x))◇x)) = (x◇x):=by
  have s0:=(t (fun q => (q◇((((y◇x)◇(x◇y))◇((x◇x)◇x))◇x)) = (x◇x)) (h7 ((x◇x)◇x) x x y) (h25 x))
  exact s0
 have h134 (x y : G):((((((x◇(y◇y))◇(y◇x))◇y)◇y)◇y)◇y) = y:=by
  have s0:=(t (fun q => ((((((x◇(y◇y))◇(y◇x))◇y)◇q)◇y)◇y) = y) (h81 ((x◇(y◇y))◇(y◇x)) y) (h3 (y◇y) y x))
  exact s0
 have h143 (x : G):(((((x◇x)◇x)◇x)◇x)◇x) = x:=by
  have s0:=(t (fun q => (((((x◇x)◇x)◇q)◇x)◇x) = x) (h81 (x◇x) x) (h25 x))
  exact s0
 have h160 (x y : G):(x◇((y◇((((x◇x)◇x)◇x)◇x))◇(x◇y))) = x:=by
  have s0:=(t (fun q => (q◇((y◇((((x◇x)◇x)◇x)◇x))◇(x◇y))) = x) (h3 ((((x◇x)◇x)◇x)◇x) x y) (h143 x))
  exact s0
 have h161 (x y : G):((x◇y)◇(x◇(y◇((((x◇x)◇x)◇x)◇x)))) = y:=by
  have s0:=(t (fun q => ((x◇y)◇(q◇(y◇((((x◇x)◇x)◇x)◇x)))) = y) (h3 x y ((((x◇x)◇x)◇x)◇x)) (h143 x))
  exact s0
 have h168 (x : G):(((x◇x)◇((x◇x)◇x))◇(x◇((x◇x)◇x))) = ((x◇x)◇x):=by
  have s0:=(t (fun q => (((x◇x)◇((((((x◇x)◇x)◇((x◇x)◇x))◇((x◇x)◇x))◇((x◇x)◇x))◇((x◇x)◇x)))◇(x◇q)) = ((((((x◇x)◇x)◇((x◇x)◇x))◇((x◇x)◇x))◇((x◇x)◇x))◇((x◇x)◇x))) (h33 x ((((((x◇x)◇x)◇((x◇x)◇x))◇((x◇x)◇x))◇((x◇x)◇x))◇((x◇x)◇x))) (h143 ((x◇x)◇x)))
  have s1:=(t (fun q => (((x◇x)◇((((((x◇x)◇x)◇((x◇x)◇x))◇((x◇x)◇x))◇((x◇x)◇x))◇((x◇x)◇x)))◇(x◇((x◇x)◇x))) = ((q◇((x◇x)◇x))◇((x◇x)◇x))) s0 (h39 x))
  have s2:=(t (fun q => (((x◇x)◇((((((x◇x)◇x)◇((x◇x)◇x))◇((x◇x)◇x))◇((x◇x)◇x))◇((x◇x)◇x)))◇(x◇((x◇x)◇x))) = q) s1 (h39 x))
  have s3:=(t (fun q => (((x◇x)◇((q◇((x◇x)◇x))◇((x◇x)◇x)))◇(x◇((x◇x)◇x))) = ((x◇x)◇x)) s2 (h39 x))
  have s4:=(t (fun q => (((x◇x)◇q)◇(x◇((x◇x)◇x))) = ((x◇x)◇x)) s3 (h39 x))
  exact s4
 have h203 (x : G):(x◇(((x◇x)◇x)◇((x◇x)◇((x◇x)◇x)))) = (x◇x):=by
  have s0:=(t (fun q => (x◇(q◇((x◇x)◇((((((x◇x)◇x)◇((x◇x)◇x))◇((x◇x)◇x))◇((x◇x)◇x))◇((x◇x)◇x))))) = (x◇x)) (h32 x ((((((x◇x)◇x)◇((x◇x)◇x))◇((x◇x)◇x))◇((x◇x)◇x))◇((x◇x)◇x))) (h143 ((x◇x)◇x)))
  have s1:=(t (fun q => (x◇(((x◇x)◇x)◇((x◇x)◇((q◇((x◇x)◇x))◇((x◇x)◇x))))) = (x◇x)) s0 (h39 x))
  have s2:=(t (fun q => (x◇(((x◇x)◇x)◇((x◇x)◇q))) = (x◇x)) s1 (h39 x))
  exact s2
 have h342 (x : G):(((x◇x)◇x)◇(((x◇x)◇((x◇x)◇x))◇x)) = ((x◇x)◇x):=by
  have s0:=(t (fun q => (((x◇x)◇x)◇(((x◇x)◇((((((x◇x)◇x)◇((x◇x)◇x))◇((x◇x)◇x))◇((x◇x)◇x))◇((x◇x)◇x)))◇q)) = ((x◇x)◇x)) (h160 ((x◇x)◇x) (x◇x)) (h25 x))
  have s1:=(t (fun q => (((x◇x)◇x)◇(((x◇x)◇((q◇((x◇x)◇x))◇((x◇x)◇x)))◇x)) = ((x◇x)◇x)) s0 (h39 x))
  have s2:=(t (fun q => (((x◇x)◇x)◇(((x◇x)◇q)◇x)) = ((x◇x)◇x)) s1 (h39 x))
  exact s2
 have h362 (x y : G):(x◇((((y◇(((((x◇x)◇(x◇x))◇(x◇x))◇(x◇x))◇(x◇x)))◇((x◇x)◇y))◇((x◇x)◇x))◇(x◇x))) = (x◇x):=by
  have s0:=(t (fun q => (x◇((((y◇(((((x◇x)◇(x◇x))◇(x◇x))◇(x◇x))◇(x◇x)))◇((x◇x)◇y))◇((x◇x)◇x))◇q)) = (x◇x)) (h32 x ((y◇(((((x◇x)◇(x◇x))◇(x◇x))◇(x◇x))◇(x◇x)))◇((x◇x)◇y))) (h160 (x◇x) y))
  exact s0
 have h378 (x y : G):((x◇(y◇x))◇((y◇(x◇(y◇x)))◇(y◇(y◇(x◇(y◇x)))))) = y:=by
  have s0:=(t (fun q => (q◇((y◇(x◇(y◇x)))◇(y◇(((((y◇(x◇(y◇x)))◇(y◇(x◇(y◇x))))◇(y◇(x◇(y◇x))))◇(y◇(x◇(y◇x))))◇(y◇(x◇(y◇x))))))) = y) (h161 (y◇(x◇(y◇x))) y) (h8 y x))
  have s1:=(t (fun q => ((x◇(y◇x))◇((y◇(x◇(y◇x)))◇(y◇((q◇(y◇(x◇(y◇x))))◇(y◇(x◇(y◇x))))))) = y) s0 (h31 y x))
  have s2:=(t (fun q => ((x◇(y◇x))◇((y◇(x◇(y◇x)))◇(y◇q))) = y) s1 (h31 y x))
  exact s2
 have h431 (x y : G):((x◇(x◇x))◇(x◇(x◇(((y◇x)◇(x◇y))◇x)))) = x:=by
  have s0:=(t (fun q => ((x◇(x◇x))◇(q◇(x◇(((y◇x)◇(x◇y))◇x)))) = x) (h15 x x (((y◇x)◇(x◇y))◇x)) (h6 y x x x))
  exact s0
 have h653 (x : G):(((x◇x)◇x)◇(((x◇x)◇x)◇((((x◇x)◇((x◇x)◇x))◇x)◇((x◇x)◇x)))) = (((x◇x)◇((x◇x)◇x))◇x):=by
  have s0:=(t (fun q => (q◇(((x◇x)◇x)◇((((x◇x)◇((x◇x)◇x))◇x)◇((((x◇x)◇x)◇((x◇x)◇x))◇((x◇x)◇x))))) = (((x◇x)◇((x◇x)◇x))◇x)) (h33 ((x◇x)◇x) (((x◇x)◇((x◇x)◇x))◇x)) (h34 ((x◇x)◇x) x))
  have s1:=(t (fun q => (((x◇x)◇x)◇(((x◇x)◇x)◇((((x◇x)◇((x◇x)◇x))◇x)◇q))) = (((x◇x)◇((x◇x)◇x))◇x)) s0 (h39 x))
  exact s1
 have h658 (x y z : G):((((x◇((y◇y)◇z))◇(y◇x))◇(z◇((y◇y)◇y)))◇(y◇((y◇y)◇y))) = (z◇((y◇y)◇y)):=by
  have s0:=(t (fun q => ((((x◇((y◇y)◇z))◇(y◇x))◇(z◇((y◇y)◇y)))◇(y◇q)) = (z◇((y◇y)◇y))) (h6 x ((y◇y)◇z) y (z◇((y◇y)◇y))) (h34 z y))
  exact s0
 have h661 (x y z : G):(((x◇x)◇x)◇((((y◇((x◇x)◇z))◇(x◇y))◇(z◇((x◇x)◇x)))◇x)) = (((x◇x)◇z)◇x):=by
  have s0:=(t (fun q => (q◇((((y◇((x◇x)◇z))◇(x◇y))◇(z◇((x◇x)◇x)))◇x)) = (((x◇x)◇z)◇x)) (h7 (z◇((x◇x)◇x)) ((x◇x)◇z) x y) (h34 z x))
  exact s0
 have h665 (x y : G):(((((x◇x)◇(x◇y))◇x)◇(y◇(x◇x)))◇x) = (y◇(x◇x)):=by
  have s0:=(t (fun q => (((((x◇x)◇(x◇y))◇x)◇(y◇(x◇x)))◇(q◇(x◇x))) = (y◇(x◇x))) (h7 (((x◇x)◇(x◇y))◇x) y (x◇x) x) (h34 (x◇y) x))
  have s1:=(t (fun q => (((((x◇x)◇(x◇y))◇x)◇(y◇(x◇x)))◇q) = (y◇(x◇x))) s0 (h25 x))
  exact s1
 have h712 (x y : G):(((x◇x)◇x)◇(((y◇x)◇(x◇y))◇((x◇x)◇x))) = (x◇x):=by
  have s0:=(t (fun q => (((((y◇x)◇(x◇y))◇((x◇x)◇x))◇q)◇(((y◇x)◇(x◇y))◇((x◇x)◇x))) = (x◇((((y◇x)◇(x◇y))◇((x◇x)◇x))◇x))) (h8 (((y◇x)◇(x◇y))◇((x◇x)◇x)) x) (h105 x y))
  have s1:=(t (fun q => (q◇(((y◇x)◇(x◇y))◇((x◇x)◇x))) = (x◇((((y◇x)◇(x◇y))◇((x◇x)◇x))◇x))) s0 (h74 y x))
  have s2:=(t (fun q => (((x◇x)◇x)◇(((y◇x)◇(x◇y))◇((x◇x)◇x))) = q) s1 (h105 x y))
  exact s2
 have h740 (x y : G):(x◇((((((y◇x)◇(x◇y))◇((x◇x)◇x))◇x)◇((((x◇x)◇x)◇x)◇x))◇(x◇x))) = x:=by
  have s0:=(t (fun q => (x◇((((((y◇x)◇(x◇y))◇((x◇x)◇x))◇x)◇((((x◇x)◇x)◇x)◇x))◇q)) = x) (h160 x ((((y◇x)◇(x◇y))◇((x◇x)◇x))◇x)) (h105 x y))
  exact s0
 have h777 (x y : G):((x◇x)◇((((y◇((x◇x)◇x))◇(((x◇x)◇((x◇x)◇x))◇y))◇x)◇((x◇x)◇((x◇x)◇x)))) = (((x◇x)◇x)◇((x◇x)◇((x◇x)◇x))):=by
  have s0:=(t (fun q => (q◇((((y◇((x◇x)◇x))◇(((x◇x)◇((x◇x)◇x))◇y))◇x)◇((x◇x)◇((x◇x)◇x)))) = (((x◇x)◇x)◇((x◇x)◇((x◇x)◇x)))) (h7 x ((x◇x)◇x) ((x◇x)◇((x◇x)◇x)) y) (h203 x))
  exact s0
 have h1009 (x : G):((x◇(x◇x))◇(x◇(x◇((((((x◇x)◇x)◇((x◇x)◇((x◇x)◇x)))◇x)◇(x◇x))◇x)))) = x:=by
  have s0:=(t (fun q => ((x◇(x◇x))◇(x◇(x◇((((((x◇x)◇x)◇((x◇x)◇((x◇x)◇x)))◇x)◇q)◇x)))) = x) (h431 x (((x◇x)◇x)◇((x◇x)◇((x◇x)◇x)))) (h203 x))
  exact s0
 have h1021 (x : G):(((x◇x)◇x)◇(((x◇x)◇x)◇((x◇x)◇x))) = ((x◇x)◇x):=by
  have s0:=(t (fun q => (q◇(((x◇x)◇x)◇((x◇x)◇x))) = ((x◇x)◇x)) (h25 ((x◇x)◇x)) (h39 x))
  exact s0
 have h1022 (x : G):(((x◇x)◇x)◇((x◇x)◇x)) = ((x◇x)◇x):=by
  have s0:=(t (fun q => (q◇(((x◇x)◇x)◇(((x◇x)◇x)◇((((x◇x)◇x)◇((x◇x)◇x))◇((x◇x)◇x))))) = ((x◇x)◇x)) (h33 ((x◇x)◇x) ((x◇x)◇x)) (h39 x))
  have s1:=(t (fun q => (((x◇x)◇x)◇(((x◇x)◇x)◇(((x◇x)◇x)◇q))) = ((x◇x)◇x)) s0 (h39 x))
  have s2:=(t (fun q => (((x◇x)◇x)◇q) = ((x◇x)◇x)) s1 (h1021 x))
  exact s2
 have h1256 (x y : G):((((x◇x)◇((x◇((x◇x)◇((x◇x)◇x)))◇(((x◇x)◇(x◇x))◇(x◇x))))◇y)◇((x◇((x◇x)◇((x◇x)◇x)))◇(y◇(x◇x)))) = y:=by
  have s0:=(t (fun q => ((((x◇x)◇((x◇((x◇x)◇((x◇x)◇x)))◇(((x◇x)◇(x◇x))◇(x◇x))))◇y)◇((x◇((x◇x)◇((x◇x)◇x)))◇(y◇q))) = y) (h40 (x◇x) (x◇((x◇x)◇((x◇x)◇x))) y) (h33 x (x◇x)))
  exact s0
 have h1311 (x : G):(((x◇x)◇((x◇((x◇x)◇((x◇x)◇x)))◇(x◇x)))◇(x◇(x◇x))) = ((x◇((x◇x)◇((x◇x)◇x)))◇(x◇x)):=by
  have s0:=(t (fun q => (((x◇x)◇((x◇((x◇x)◇((x◇x)◇x)))◇(x◇x)))◇(((x◇x)◇((x◇x)◇(x◇x)))◇q)) = ((x◇((x◇x)◇((x◇x)◇x)))◇(x◇x))) (h22 (x◇x) ((x◇((x◇x)◇((x◇x)◇x)))◇(x◇x)) (x◇x)) (h40 x (x◇x) (x◇x)))
  have s1:=(t (fun q => (((x◇x)◇((x◇((x◇x)◇((x◇x)◇x)))◇(x◇x)))◇(q◇(x◇x))) = ((x◇((x◇x)◇((x◇x)◇x)))◇(x◇x))) s0 (h3 x x x))
  exact s1
 have h1387 (x y z : G):((((x◇((y◇((z◇z)◇z))◇((z◇z)◇y)))◇((z◇z)◇x))◇((z◇z)◇z))◇((y◇((z◇z)◇z))◇((z◇z)◇y))) = ((z◇z)◇z):=by
  have s0:=(t (fun q => ((((x◇((y◇((z◇z)◇z))◇((z◇z)◇y)))◇(q◇x))◇((z◇((y◇((z◇z)◇z))◇((z◇z)◇y)))◇z))◇((y◇((z◇z)◇z))◇((z◇z)◇y))) = ((z◇((y◇((z◇z)◇z))◇((z◇z)◇y)))◇z)) (h55 x ((y◇((z◇z)◇z))◇((z◇z)◇y)) z) (h32 z y))
  have s1:=(t (fun q => ((((x◇((y◇((z◇z)◇z))◇((z◇z)◇y)))◇((z◇z)◇x))◇((z◇((y◇((z◇z)◇z))◇((z◇z)◇y)))◇z))◇((y◇((z◇z)◇z))◇((z◇z)◇y))) = (q◇z)) s0 (h32 z y))
  have s2:=(t (fun q => ((((x◇((y◇((z◇z)◇z))◇((z◇z)◇y)))◇((z◇z)◇x))◇(q◇z))◇((y◇((z◇z)◇z))◇((z◇z)◇y))) = ((z◇z)◇z)) s1 (h32 z y))
  exact s2
 have h1971 (x y : G):((((x◇y)◇(((y◇y)◇y)◇x))◇((y◇y)◇((y◇y)◇y)))◇((y◇y)◇y)) = ((y◇y)◇((y◇y)◇y)):=by
  have s0:=(t (fun q => ((((x◇y)◇(((y◇y)◇y)◇x))◇((y◇y)◇((y◇y)◇y)))◇(((y◇y)◇y)◇q)) = ((y◇y)◇((y◇y)◇y))) (h6 x y ((y◇y)◇y) ((y◇y)◇((y◇y)◇y))) (h168 y))
  have s1:=(t (fun q => ((((x◇y)◇(((y◇y)◇y)◇x))◇((y◇y)◇((y◇y)◇y)))◇q) = ((y◇y)◇((y◇y)◇y))) s0 (h1022 y))
  exact s1
 have h1973 (x : G):(((x◇x)◇x)◇((x◇x)◇((x◇x)◇x))) = (x◇((x◇x)◇x)):=by
  have s0:=(t (fun q => (q◇((((x◇x)◇(((x◇x)◇x)◇x))◇((x◇x)◇((x◇x)◇x)))◇((x◇x)◇x))) = (x◇((x◇x)◇x))) (h7 ((x◇x)◇((x◇x)◇x)) x ((x◇x)◇x) x) (h168 x))
  have s1:=(t (fun q => (((x◇x)◇x)◇q) = (x◇((x◇x)◇x))) s0 (h1971 x x))
  exact s1
 have h2007 (x : G):((((x◇x)◇(((x◇x)◇(x◇x))◇(x◇x)))◇x)◇(x◇x)) = x:=by
  have s0:=(t (fun q => ((((x◇x)◇(((x◇x)◇(x◇x))◇(x◇x)))◇x)◇(q◇((x◇x)◇(x◇x)))) = x) (h11 ((x◇x)◇(((x◇x)◇(x◇x))◇(x◇x))) x (x◇x) x x) (h168 (x◇x)))
  have s1:=(t (fun q => ((((x◇x)◇(((x◇x)◇(x◇x))◇(x◇x)))◇x)◇q) = x) s0 (h25 (x◇x)))
  exact s1
 have h2018 (x : G):(((((x◇((x◇x)◇x))◇((x◇x)◇x))◇((x◇x)◇x))◇(((x◇x)◇((x◇x)◇x))◇(x◇x)))◇((x◇x)◇x)) = (((x◇x)◇((x◇x)◇x))◇(x◇x)):=by
  have s0:=(t (fun q => (((((x◇((x◇x)◇x))◇((x◇x)◇x))◇q)◇(((x◇x)◇((x◇x)◇x))◇(x◇x)))◇((x◇x)◇x)) = (((x◇x)◇((x◇x)◇x))◇(x◇x))) (h55 (x◇((x◇x)◇x)) ((x◇x)◇x) (x◇x)) (h168 x))
  exact s0
 have h2044 (x : G):((x◇(x◇x))◇(x◇(x◇((((x◇((x◇x)◇x))◇x)◇(x◇x))◇x)))) = x:=by
  have s0:=h1009 x
  have s1:=(t (fun q => ((x◇(x◇x))◇(x◇(x◇(((q◇x)◇(x◇x))◇x)))) = x) s0 (h1973 x))
  exact s1
 have h2070 (x y : G):((x◇x)◇((((y◇((x◇x)◇x))◇(((x◇x)◇((x◇x)◇x))◇y))◇x)◇((x◇x)◇((x◇x)◇x)))) = (x◇((x◇x)◇x)):=by
  have s0:=h777 x y
  have s1:=(t (fun q => ((x◇x)◇((((y◇((x◇x)◇x))◇(((x◇x)◇((x◇x)◇x))◇y))◇x)◇((x◇x)◇((x◇x)◇x)))) = q) s0 (h1973 x))
  exact s1
 have h2084 (x : G):(x◇(x◇((x◇x)◇x))) = (x◇x):=by
  have s0:=h203 x
  have s1:=(t (fun q => (x◇q) = (x◇x)) s0 (h1973 x))
  exact s1
 have h2094 (x : G):((x◇((x◇x)◇x))◇((((x◇x)◇((x◇((x◇x)◇x))◇x))◇(((x◇((x◇x)◇x))◇(x◇((x◇x)◇x)))◇(x◇((x◇x)◇x))))◇(x◇((x◇x)◇x)))) = ((x◇((x◇x)◇x))◇(x◇((x◇x)◇x))):=by
  have s0:=(t (fun q => ((x◇((x◇x)◇x))◇(((q◇((x◇((x◇x)◇x))◇x))◇(((x◇((x◇x)◇x))◇(x◇((x◇x)◇x)))◇(x◇((x◇x)◇x))))◇(x◇((x◇x)◇x)))) = ((x◇((x◇x)◇x))◇(x◇((x◇x)◇x)))) (h105 (x◇((x◇x)◇x)) x) (h2084 x))
  exact s0
 have h2977 (x : G):((((x◇x)◇x)◇((((x◇x)◇((x◇x)◇x))◇x)◇((x◇x)◇x)))◇((x◇x)◇x)) = ((((x◇x)◇((x◇x)◇x))◇x)◇((x◇x)◇x)):=by
  have s0:=(t (fun q => ((((x◇x)◇x)◇((((x◇x)◇((x◇x)◇x))◇x)◇q))◇((x◇x)◇x)) = ((((x◇x)◇((x◇x)◇x))◇x)◇(((x◇x)◇x)◇(((x◇x)◇((x◇x)◇x))◇x)))) (h8 ((x◇x)◇x) (((x◇x)◇((x◇x)◇x))◇x)) (h342 x))
  have s1:=(t (fun q => ((((x◇x)◇x)◇((((x◇x)◇((x◇x)◇x))◇x)◇((x◇x)◇x)))◇((x◇x)◇x)) = ((((x◇x)◇((x◇x)◇x))◇x)◇q)) s0 (h342 x))
  exact s1
 have h3044 (x y : G):((((((x◇(y◇(x◇y)))◇(x◇(y◇(x◇y))))◇(y◇(x◇y)))◇(x◇(y◇(x◇y))))◇(x◇((x◇(y◇(x◇y)))◇(x◇(y◇(x◇y))))))◇(x◇(y◇(x◇y)))) = (x◇((x◇(y◇(x◇y)))◇(x◇(y◇(x◇y))))):=by
  have s0:=(t (fun q => ((((((x◇(y◇(x◇y)))◇(x◇(y◇(x◇y))))◇q)◇(x◇(y◇(x◇y))))◇(x◇((x◇(y◇(x◇y)))◇(x◇(y◇(x◇y))))))◇(x◇(y◇(x◇y)))) = (x◇((x◇(y◇(x◇y)))◇(x◇(y◇(x◇y)))))) (h665 (x◇(y◇(x◇y))) x) (h8 x y))
  exact s0
 have h3225 (x y : G):((x◇(y◇(x◇y)))◇(((x◇(x◇(y◇(x◇y))))◇(y◇(x◇y)))◇(x◇(y◇(x◇y))))) = ((x◇(y◇(x◇y)))◇(x◇(y◇(x◇y)))):=by
  have s0:=(t (fun q => ((((x◇(y◇(x◇y)))◇(x◇(y◇(x◇y))))◇(x◇(y◇(x◇y))))◇(((x◇(x◇(y◇(x◇y))))◇q)◇(((x◇(y◇(x◇y)))◇(x◇(y◇(x◇y))))◇(x◇(y◇(x◇y)))))) = ((x◇(y◇(x◇y)))◇(x◇(y◇(x◇y))))) (h712 (x◇(y◇(x◇y))) x) (h8 x y))
  have s1:=(t (fun q => ((((x◇(y◇(x◇y)))◇(x◇(y◇(x◇y))))◇(x◇(y◇(x◇y))))◇(((x◇(x◇(y◇(x◇y))))◇(y◇(x◇y)))◇q)) = ((x◇(y◇(x◇y)))◇(x◇(y◇(x◇y))))) s0 (h31 x y))
  have s2:=(t (fun q => (q◇(((x◇(x◇(y◇(x◇y))))◇(y◇(x◇y)))◇(x◇(y◇(x◇y))))) = ((x◇(y◇(x◇y)))◇(x◇(y◇(x◇y))))) s1 (h31 x y))
  exact s2
 have h3226 (x : G):((((x◇x)◇(x◇x))◇(x◇x))◇((x◇((x◇x)◇((x◇x)◇x)))◇(((x◇x)◇(x◇x))◇(x◇x)))) = ((x◇x)◇(x◇x)):=by
  have s0:=(t (fun q => ((((x◇x)◇(x◇x))◇(x◇x))◇((q◇((x◇x)◇((x◇x)◇x)))◇(((x◇x)◇(x◇x))◇(x◇x)))) = ((x◇x)◇(x◇x))) (h712 (x◇x) ((x◇x)◇x)) (h25 x))
  exact s0
 have h3227 (x : G):(((x◇x)◇x)◇((((x◇x)◇((x◇x)◇x))◇x)◇((x◇x)◇x))) = ((x◇x)◇x):=by
  have s0:=(t (fun q => (((((x◇x)◇x)◇((x◇x)◇x))◇((x◇x)◇x))◇((((x◇x)◇((x◇x)◇x))◇q)◇((((x◇x)◇x)◇((x◇x)◇x))◇((x◇x)◇x)))) = (((x◇x)◇x)◇((x◇x)◇x))) (h712 ((x◇x)◇x) (x◇x)) (h25 x))
  have s1:=(t (fun q => (((((x◇x)◇x)◇((x◇x)◇x))◇((x◇x)◇x))◇((((x◇x)◇((x◇x)◇x))◇x)◇((((x◇x)◇x)◇((x◇x)◇x))◇((x◇x)◇x)))) = q) s0 (h1022 x))
  have s2:=(t (fun q => (((((x◇x)◇x)◇((x◇x)◇x))◇((x◇x)◇x))◇((((x◇x)◇((x◇x)◇x))◇x)◇(q◇((x◇x)◇x)))) = ((x◇x)◇x)) s1 (h1022 x))
  have s3:=(t (fun q => (((((x◇x)◇x)◇((x◇x)◇x))◇((x◇x)◇x))◇((((x◇x)◇((x◇x)◇x))◇x)◇q)) = ((x◇x)◇x)) s2 (h1022 x))
  have s4:=(t (fun q => ((q◇((x◇x)◇x))◇((((x◇x)◇((x◇x)◇x))◇x)◇((x◇x)◇x))) = ((x◇x)◇x)) s3 (h1022 x))
  have s5:=(t (fun q => (q◇((((x◇x)◇((x◇x)◇x))◇x)◇((x◇x)◇x))) = ((x◇x)◇x)) s4 (h1022 x))
  exact s5
 have h3335 (x : G):((((x◇x)◇((x◇x)◇x))◇x)◇((x◇x)◇x)) = ((x◇x)◇x):=by
  have s0:=(h2977 x).symm
  have s1:=(t (fun q => ((((x◇x)◇((x◇x)◇x))◇x)◇((x◇x)◇x)) = (q◇((x◇x)◇x))) s0 (h3227 x))
  have s2:=(t (fun q => ((((x◇x)◇((x◇x)◇x))◇x)◇((x◇x)◇x)) = q) s1 (h1022 x))
  exact s2
 have h3337 (x : G):(((x◇x)◇((x◇x)◇x))◇x) = ((x◇x)◇x):=by
  have s0:=(h653 x).symm
  have s1:=(t (fun q => (((x◇x)◇((x◇x)◇x))◇x) = (((x◇x)◇x)◇(((x◇x)◇x)◇q))) s0 (h3335 x))
  have s2:=(t (fun q => (((x◇x)◇((x◇x)◇x))◇x) = (((x◇x)◇x)◇q)) s1 (h1022 x))
  have s3:=(t (fun q => (((x◇x)◇((x◇x)◇x))◇x) = q) s2 (h1022 x))
  exact s3
 have h3384 (x : G):((x◇x)◇((x◇(x◇(x◇x)))◇((x◇x)◇x))) = ((x◇x)◇((x◇x)◇x)):=by
  have s0:=(t (fun q => ((x◇x)◇((x◇(x◇(x◇x)))◇q)) = ((x◇x)◇((x◇x)◇x))) (h5 (x◇x) x x x) (h3337 x))
  exact s0
 have h3461 (x : G):(((x◇x)◇(((x◇x)◇(x◇x))◇(x◇x)))◇x) = (((x◇x)◇(x◇x))◇(x◇x)):=by
  have s0:=(t (fun q => (((((x◇x)◇(x◇(((x◇x)◇(x◇x))◇(((x◇x)◇(x◇x))◇(x◇x)))))◇x)◇q)◇x) = ((((x◇x)◇(x◇x))◇(((x◇x)◇(x◇x))◇(x◇x)))◇(x◇x))) (h665 x (((x◇x)◇(x◇x))◇(((x◇x)◇(x◇x))◇(x◇x)))) (h3337 (x◇x)))
  have s1:=(t (fun q => (((((x◇x)◇q)◇x)◇(((x◇x)◇(x◇x))◇(x◇x)))◇x) = ((((x◇x)◇(x◇x))◇(((x◇x)◇(x◇x))◇(x◇x)))◇(x◇x))) s0 (h5 x (x◇x) x x))
  have s2:=(t (fun q => (((q◇x)◇(((x◇x)◇(x◇x))◇(x◇x)))◇x) = ((((x◇x)◇(x◇x))◇(((x◇x)◇(x◇x))◇(x◇x)))◇(x◇x))) s1 (h3 x x x))
  have s3:=(t (fun q => (((x◇x)◇(((x◇x)◇(x◇x))◇(x◇x)))◇x) = q) s2 (h3337 (x◇x)))
  exact s3
 have h3470 (x : G):((((x◇x)◇(x◇x))◇(x◇x))◇(x◇x)) = x:=by
  have s0:=h2007 x
  have s1:=(t (fun q => (q◇(x◇x)) = x) s0 (h3461 x))
  exact s1
 have h3479 (x : G):((x◇(x◇x))◇(x◇x)) = (x◇x):=by
  have s0:=h362 x x
  have s1:=(t (fun q => (x◇((((x◇(q◇(x◇x)))◇((x◇x)◇x))◇((x◇x)◇x))◇(x◇x))) = (x◇x)) s0 (h3470 x))
  have s2:=(t (fun q => q = (x◇x)) s1 (h16 x x x (x◇x)))
  exact s2
 have h3481 (x y : G):((x◇x)◇((y◇(x◇(x◇x)))◇((x◇x)◇y))) = (x◇x):=by
  have s0:=(t (fun q => (q◇((y◇(x◇(x◇x)))◇((x◇x)◇y))) = (x◇x)) (h3 (x◇(x◇x)) (x◇x) y) (h3479 x))
  exact s0
 have h3482 (x y : G):(((x◇x)◇y)◇((x◇x)◇(y◇(x◇(x◇x))))) = y:=by
  have s0:=(t (fun q => (((x◇x)◇y)◇(q◇(y◇(x◇(x◇x))))) = y) (h3 (x◇x) y (x◇(x◇x))) (h3479 x))
  exact s0
 have h3484 (x : G):(x◇((x◇x)◇(x◇x))) = ((x◇x)◇(x◇x)):=by
  have s0:=(t (fun q => (q◇((x◇x)◇(x◇x))) = ((x◇x)◇(x◇x))) (h3479 (x◇x)) (h3 x x x))
  exact s0
 have h3530 (x : G):(((x◇((x◇x)◇((x◇x)◇x)))◇x)◇x) = x:=by
  have s0:=(t (fun q => (((x◇((x◇x)◇((x◇x)◇x)))◇((x◇x)◇((x◇x)◇(x◇x))))◇((x◇x)◇q)) = ((x◇x)◇((x◇x)◇(x◇x)))) (h40 x (x◇x) ((x◇x)◇((x◇x)◇(x◇x)))) (h3479 (x◇x)))
  have s1:=(t (fun q => (((x◇((x◇x)◇((x◇x)◇x)))◇q)◇((x◇x)◇((x◇x)◇(x◇x)))) = ((x◇x)◇((x◇x)◇(x◇x)))) s0 (h3 x x x))
  have s2:=(t (fun q => (((x◇((x◇x)◇((x◇x)◇x)))◇x)◇q) = ((x◇x)◇((x◇x)◇(x◇x)))) s1 (h3 x x x))
  have s3:=(t (fun q => (((x◇((x◇x)◇((x◇x)◇x)))◇x)◇x) = q) s2 (h3 x x x))
  exact s3
 have h3558 (x : G):((((((x◇(x◇x))◇(x◇(x◇x)))◇(x◇x))◇(x◇(x◇x)))◇((x◇x)◇((x◇(x◇x))◇(x◇(x◇x)))))◇(x◇(x◇x))) = ((x◇x)◇((x◇(x◇x))◇(x◇(x◇x)))):=by
  have s0:=(t (fun q => ((((((x◇(x◇x))◇(x◇(x◇x)))◇q)◇(x◇(x◇x)))◇((x◇x)◇((x◇(x◇x))◇(x◇(x◇x)))))◇(x◇(x◇x))) = ((x◇x)◇((x◇(x◇x))◇(x◇(x◇x))))) (h665 (x◇(x◇x)) (x◇x)) (h3479 x))
  exact s0
 have h3567 (x : G):((x◇x)◇((x◇x)◇x)) = (x◇x):=by
  have s0:=(h3384 x).symm
  have s1:=(t (fun q => ((x◇x)◇((x◇x)◇x)) = q) s0 (h3481 x x))
  exact s1
 have h3569 (x : G):(((x◇(x◇x))◇x)◇x) = x:=by
  have s0:=h3530 x
  have s1:=(t (fun q => (((x◇q)◇x)◇x) = x) s0 (h3567 x))
  exact s1
 have h3583 (x : G):((((x◇x)◇(x◇x))◇(x◇x))◇((x◇(x◇x))◇(((x◇x)◇(x◇x))◇(x◇x)))) = ((x◇x)◇(x◇x)):=by
  have s0:=h3226 x
  have s1:=(t (fun q => ((((x◇x)◇(x◇x))◇(x◇x))◇((x◇q)◇(((x◇x)◇(x◇x))◇(x◇x)))) = ((x◇x)◇(x◇x))) s0 (h3567 x))
  exact s1
 have h3600 (x : G):(x◇((x◇x)◇x)) = x:=by
  have s0:=h2070 x x
  have s1:=(t (fun q => ((x◇x)◇((((x◇((x◇x)◇x))◇(q◇x))◇x)◇((x◇x)◇((x◇x)◇x)))) = (x◇((x◇x)◇x))) s0 (h3567 x))
  have s2:=(t (fun q => ((x◇x)◇((((x◇((x◇x)◇x))◇((x◇x)◇x))◇x)◇q)) = (x◇((x◇x)◇x))) s1 (h3567 x))
  have s3:=(t (fun q => q = (x◇((x◇x)◇x))) s2 (h104 x x x)).symm
  exact s3
 have h3602 (x : G):(((x◇x)◇(x◇x))◇((x◇x)◇x)) = ((x◇x)◇(x◇x)):=by
  have s0:=h2018 x
  have s1:=(t (fun q => ((((q◇((x◇x)◇x))◇((x◇x)◇x))◇(((x◇x)◇((x◇x)◇x))◇(x◇x)))◇((x◇x)◇x)) = (((x◇x)◇((x◇x)◇x))◇(x◇x))) s0 (h3600 x))
  have s2:=(t (fun q => (((q◇((x◇x)◇x))◇(((x◇x)◇((x◇x)◇x))◇(x◇x)))◇((x◇x)◇x)) = (((x◇x)◇((x◇x)◇x))◇(x◇x))) s1 (h3600 x))
  have s3:=(t (fun q => ((q◇(((x◇x)◇((x◇x)◇x))◇(x◇x)))◇((x◇x)◇x)) = (((x◇x)◇((x◇x)◇x))◇(x◇x))) s2 (h3600 x))
  have s4:=(t (fun q => ((x◇(q◇(x◇x)))◇((x◇x)◇x)) = (((x◇x)◇((x◇x)◇x))◇(x◇x))) s3 (h3567 x))
  have s5:=(t (fun q => (q◇((x◇x)◇x)) = (((x◇x)◇((x◇x)◇x))◇(x◇x))) s4 (h3484 x))
  have s6:=(t (fun q => (((x◇x)◇(x◇x))◇((x◇x)◇x)) = (q◇(x◇x))) s5 (h3567 x))
  exact s6
 have h3616 (x : G):(((x◇x)◇(x◇x))◇(x◇(x◇x))) = (x◇x):=by
  have s0:=h1311 x
  have s1:=(t (fun q => (((x◇x)◇((x◇((x◇x)◇((x◇x)◇x)))◇(x◇x)))◇(x◇(x◇x))) = ((x◇q)◇(x◇x))) s0 (h3567 x))
  have s2:=(t (fun q => (((x◇x)◇((x◇((x◇x)◇((x◇x)◇x)))◇(x◇x)))◇(x◇(x◇x))) = q) s1 (h3479 x))
  have s3:=(t (fun q => (((x◇x)◇((x◇q)◇(x◇x)))◇(x◇(x◇x))) = (x◇x)) s2 (h3567 x))
  have s4:=(t (fun q => (((x◇x)◇q)◇(x◇(x◇x))) = (x◇x)) s3 (h3479 x))
  exact s4
 have h3617 (x y : G):((((x◇x)◇((x◇(x◇x))◇(((x◇x)◇(x◇x))◇(x◇x))))◇y)◇((x◇(x◇x))◇(y◇(x◇x)))) = y:=by
  have s0:=h1256 x y
  have s1:=(t (fun q => ((((x◇x)◇((x◇((x◇x)◇((x◇x)◇x)))◇(((x◇x)◇(x◇x))◇(x◇x))))◇y)◇((x◇q)◇(y◇(x◇x)))) = y) s0 (h3567 x))
  have s2:=(t (fun q => ((((x◇x)◇((x◇q)◇(((x◇x)◇(x◇x))◇(x◇x))))◇y)◇((x◇(x◇x))◇(y◇(x◇x)))) = y) s1 (h3567 x))
  exact s2
 have h3623 (x : G):(((x◇x)◇(x◇x))◇(x◇x)) = ((x◇x)◇x):=by
  have s0:=(h3461 x).symm
  have s1:=(t (fun q => (((x◇x)◇(x◇x))◇(x◇x)) = (q◇x)) s0 (h3600 (x◇x)))
  exact s1
 have h3640 (x : G):(x◇(((x◇x)◇(x◇x))◇x)) = (x◇x):=by
  have s0:=h2094 x
  have s1:=(t (fun q => (q◇((((x◇x)◇((x◇((x◇x)◇x))◇x))◇(((x◇((x◇x)◇x))◇(x◇((x◇x)◇x)))◇(x◇((x◇x)◇x))))◇(x◇((x◇x)◇x)))) = ((x◇((x◇x)◇x))◇(x◇((x◇x)◇x)))) s0 (h3600 x))
  have s2:=(t (fun q => (x◇((((x◇x)◇(q◇x))◇(((x◇((x◇x)◇x))◇(x◇((x◇x)◇x)))◇(x◇((x◇x)◇x))))◇(x◇((x◇x)◇x)))) = ((x◇((x◇x)◇x))◇(x◇((x◇x)◇x)))) s1 (h3600 x))
  have s3:=(t (fun q => (x◇((((x◇x)◇(x◇x))◇((q◇(x◇((x◇x)◇x)))◇(x◇((x◇x)◇x))))◇(x◇((x◇x)◇x)))) = ((x◇((x◇x)◇x))◇(x◇((x◇x)◇x)))) s2 (h3600 x))
  have s4:=(t (fun q => (x◇((((x◇x)◇(x◇x))◇((x◇q)◇(x◇((x◇x)◇x))))◇(x◇((x◇x)◇x)))) = ((x◇((x◇x)◇x))◇(x◇((x◇x)◇x)))) s3 (h3600 x))
  have s5:=(t (fun q => (x◇((((x◇x)◇(x◇x))◇((x◇x)◇q))◇(x◇((x◇x)◇x)))) = ((x◇((x◇x)◇x))◇(x◇((x◇x)◇x)))) s4 (h3600 x))
  have s6:=(t (fun q => (x◇(q◇(x◇((x◇x)◇x)))) = ((x◇((x◇x)◇x))◇(x◇((x◇x)◇x)))) s5 (h3602 x))
  have s7:=(t (fun q => (x◇(((x◇x)◇(x◇x))◇q)) = ((x◇((x◇x)◇x))◇(x◇((x◇x)◇x)))) s6 (h3600 x))
  have s8:=(t (fun q => (x◇(((x◇x)◇(x◇x))◇x)) = (q◇(x◇((x◇x)◇x)))) s7 (h3600 x))
  have s9:=(t (fun q => (x◇(((x◇x)◇(x◇x))◇x)) = (x◇q)) s8 (h3600 x))
  exact s9
 have h3643 (x : G):((x◇(x◇x))◇(x◇(x◇x))) = x:=by
  have s0:=h2044 x
  have s1:=(t (fun q => ((x◇(x◇x))◇(x◇(x◇(((q◇x)◇(x◇x))◇x)))) = x) s0 (h3600 x))
  have s2:=(t (fun q => ((x◇(x◇x))◇(x◇q)) = x) s1 (h3640 x))
  exact s2
 have h3652 (x y z : G):((((x◇((y◇y)◇z))◇(y◇x))◇(z◇((y◇y)◇y)))◇y) = (z◇((y◇y)◇y)):=by
  have s0:=h658 x y z
  have s1:=(t (fun q => ((((x◇((y◇y)◇z))◇(y◇x))◇(z◇((y◇y)◇y)))◇q) = (z◇((y◇y)◇y))) s0 (h3600 y))
  exact s1
 have h3658 (x y : G):((((x◇x)◇((x◇(x◇x))◇((x◇x)◇x)))◇y)◇((x◇(x◇x))◇(y◇(x◇x)))) = y:=by
  have s0:=h3617 x y
  have s1:=(t (fun q => ((((x◇x)◇((x◇(x◇x))◇q))◇y)◇((x◇(x◇x))◇(y◇(x◇x)))) = y) s0 (h3623 x))
  exact s1
 have h3661 (x : G):(((x◇x)◇x)◇((x◇(x◇x))◇((x◇x)◇x))) = ((x◇x)◇(x◇x)):=by
  have s0:=h3583 x
  have s1:=(t (fun q => ((((x◇x)◇(x◇x))◇(x◇x))◇((x◇(x◇x))◇q)) = ((x◇x)◇(x◇x))) s0 (h3623 x))
  have s2:=(t (fun q => (q◇((x◇(x◇x))◇((x◇x)◇x))) = ((x◇x)◇(x◇x))) s1 (h3623 x))
  exact s2
 have h3707 (x : G):((x◇x)◇x) = (x◇(x◇(x◇x))):=by
  have s0:=h3558 x
  have s1:=(t (fun q => ((((q◇(x◇x))◇(x◇(x◇x)))◇((x◇x)◇((x◇(x◇x))◇(x◇(x◇x)))))◇(x◇(x◇x))) = ((x◇x)◇((x◇(x◇x))◇(x◇(x◇x))))) s0 (h3643 x))
  have s2:=(t (fun q => ((q◇((x◇x)◇((x◇(x◇x))◇(x◇(x◇x)))))◇(x◇(x◇x))) = ((x◇x)◇((x◇(x◇x))◇(x◇(x◇x))))) s1 (h3643 x))
  have s3:=(t (fun q => ((x◇((x◇x)◇q))◇(x◇(x◇x))) = ((x◇x)◇((x◇(x◇x))◇(x◇(x◇x))))) s2 (h3643 x))
  have s4:=(t (fun q => (q◇(x◇(x◇x))) = ((x◇x)◇((x◇(x◇x))◇(x◇(x◇x))))) s3 (h3600 x))
  have s5:=(t (fun q => (x◇(x◇(x◇x))) = ((x◇x)◇q)) s4 (h3643 x)).symm
  exact s5
 have h3733 (x y z : G):((x◇(x◇(x◇x)))◇((((y◇((x◇x)◇z))◇(x◇y))◇(z◇(x◇(x◇(x◇x)))))◇x)) = (((x◇x)◇z)◇x):=by
  have s0:=h661 x y z
  have s1:=(t (fun q => (((x◇x)◇x)◇((((y◇((x◇x)◇z))◇(x◇y))◇(z◇q))◇x)) = (((x◇x)◇z)◇x)) s0 (h3707 x))
  have s2:=(t (fun q => (q◇((((y◇((x◇x)◇z))◇(x◇y))◇(z◇(x◇(x◇(x◇x)))))◇x)) = (((x◇x)◇z)◇x)) s1 (h3707 x))
  exact s2
 have h3779 (x : G):((x◇(x◇(x◇x)))◇((x◇(x◇x))◇(x◇(x◇(x◇x))))) = ((x◇x)◇(x◇x)):=by
  have s0:=h3661 x
  have s1:=(t (fun q => (((x◇x)◇x)◇((x◇(x◇x))◇q)) = ((x◇x)◇(x◇x))) s0 (h3707 x))
  have s2:=(t (fun q => (q◇((x◇(x◇x))◇(x◇(x◇(x◇x))))) = ((x◇x)◇(x◇x))) s1 (h3707 x))
  exact s2
 have h3782 (x y : G):((((x◇x)◇((x◇(x◇x))◇(x◇(x◇(x◇x)))))◇y)◇((x◇(x◇x))◇(y◇(x◇x)))) = y:=by
  have s0:=h3658 x y
  have s1:=(t (fun q => ((((x◇x)◇((x◇(x◇x))◇q))◇y)◇((x◇(x◇x))◇(y◇(x◇x)))) = y) s0 (h3707 x))
  exact s1
 have h3788 (x y z : G):((((x◇((y◇y)◇z))◇(y◇x))◇(z◇(y◇(y◇(y◇y)))))◇y) = (z◇(y◇(y◇(y◇y)))):=by
  have s0:=h3652 x y z
  have s1:=(t (fun q => ((((x◇((y◇y)◇z))◇(y◇x))◇(z◇((y◇y)◇y)))◇y) = (z◇q)) s0 (h3707 y))
  have s2:=(t (fun q => ((((x◇((y◇y)◇z))◇(y◇x))◇(z◇q))◇y) = (z◇(y◇(y◇(y◇y))))) s1 (h3707 y))
  exact s2
 have h3821 (x : G):(x◇(x◇(x◇(x◇x)))) = x:=by
  have s0:=h3600 x
  have s1:=(t (fun q => (x◇q) = x) s0 (h3707 x))
  exact s1
 have h3828 (x : G):((x◇x)◇(x◇(x◇(x◇x)))) = (x◇x):=by
  have s0:=h3567 x
  have s1:=(t (fun q => ((x◇x)◇q) = (x◇x)) s0 (h3707 x))
  exact s1
 have h4496 (x y z : G):((((x◇((y◇(z◇(z◇(z◇z))))◇((z◇z)◇y)))◇((z◇z)◇x))◇(z◇(z◇(z◇z))))◇((y◇(z◇(z◇(z◇z))))◇((z◇z)◇y))) = (z◇(z◇(z◇z))):=by
  have s0:=h1387 x y z
  have s1:=(t (fun q => ((((x◇((y◇((z◇z)◇z))◇((z◇z)◇y)))◇((z◇z)◇x))◇((z◇z)◇z))◇((y◇((z◇z)◇z))◇((z◇z)◇y))) = q) s0 (h3707 z))
  have s2:=(t (fun q => ((((x◇((y◇((z◇z)◇z))◇((z◇z)◇y)))◇((z◇z)◇x))◇((z◇z)◇z))◇((y◇q)◇((z◇z)◇y))) = (z◇(z◇(z◇z)))) s1 (h3707 z))
  have s3:=(t (fun q => ((((x◇((y◇((z◇z)◇z))◇((z◇z)◇y)))◇((z◇z)◇x))◇q)◇((y◇(z◇(z◇(z◇z))))◇((z◇z)◇y))) = (z◇(z◇(z◇z)))) s2 (h3707 z))
  have s4:=(t (fun q => ((((x◇((y◇q)◇((z◇z)◇y)))◇((z◇z)◇x))◇(z◇(z◇(z◇z))))◇((y◇(z◇(z◇(z◇z))))◇((z◇z)◇y))) = (z◇(z◇(z◇z)))) s3 (h3707 z))
  exact s4
 have h4781 (x : G):((x◇(x◇(x◇x)))◇(x◇x)) = x:=by
  have s0:=h740 x x
  have s1:=(t (fun q => (x◇((((((x◇x)◇(x◇x))◇q)◇x)◇((((x◇x)◇x)◇x)◇x))◇(x◇x))) = x) s0 (h3707 x))
  have s2:=(t (fun q => (x◇((((((x◇x)◇(x◇x))◇(x◇(x◇(x◇x))))◇x)◇((q◇x)◇x))◇(x◇x))) = x) s1 (h3707 x))
  have s3:=(t (fun q => (x◇((((((x◇x)◇(x◇x))◇(x◇(x◇(x◇x))))◇x)◇(q◇x))◇(x◇x))) = x) s2 (h8 x x))
  have s4:=(t (fun q => q = x) s3 (h93 x x x (x◇(x◇x))))
  exact s4
 have h5100 (x y : G):(((x◇x)◇y)◇(x◇(y◇(x◇(x◇(x◇x)))))) = y:=by
  have s0:=h33 x y
  have s1:=(t (fun q => (((x◇x)◇y)◇(x◇(y◇q))) = y) s0 (h3707 x))
  exact s1
 have h5102 (x y : G):((x◇(y◇(x◇y)))◇((x◇(y◇(x◇y)))◇((x◇(y◇(x◇y)))◇(x◇(y◇(x◇y)))))) = (x◇(y◇(x◇y))):=by
  have s0:=h31 x y
  have s1:=(t (fun q => q = (x◇(y◇(x◇y)))) s0 (h3707 (x◇(y◇(x◇y)))))
  exact s1
 have h5103 (x y : G):(((x◇x)◇y)◇x) = ((x◇(x◇(x◇x)))◇(y◇(x◇(x◇(x◇x))))):=by
  have s0:=(h3733 x x y).symm
  have s1:=(t (fun q => (((x◇x)◇y)◇x) = ((x◇(x◇(x◇x)))◇q)) s0 (h3788 x x y))
  exact s1
 have h5224 (x y : G):((((x◇(y◇(x◇y)))◇((y◇(x◇y))◇(x◇(y◇(x◇y)))))◇(x◇((x◇(y◇(x◇y)))◇(x◇(y◇(x◇y))))))◇(x◇(y◇(x◇y)))) = (x◇((x◇(y◇(x◇y)))◇(x◇(y◇(x◇y))))):=by
  have s0:=h3044 x y
  have s1:=(t (fun q => ((q◇(x◇((x◇(y◇(x◇y)))◇(x◇(y◇(x◇y))))))◇(x◇(y◇(x◇y)))) = (x◇((x◇(y◇(x◇y)))◇(x◇(y◇(x◇y)))))) s0 (h5103 (x◇(y◇(x◇y))) (y◇(x◇y))))
  have s2:=(t (fun q => (((((x◇(y◇(x◇y)))◇((x◇(y◇(x◇y)))◇((x◇(y◇(x◇y)))◇(x◇(y◇(x◇y))))))◇((y◇(x◇y))◇q))◇(x◇((x◇(y◇(x◇y)))◇(x◇(y◇(x◇y))))))◇(x◇(y◇(x◇y)))) = (x◇((x◇(y◇(x◇y)))◇(x◇(y◇(x◇y)))))) s1 (h5102 x y))
  have s3:=(t (fun q => (((q◇((y◇(x◇y))◇(x◇(y◇(x◇y)))))◇(x◇((x◇(y◇(x◇y)))◇(x◇(y◇(x◇y))))))◇(x◇(y◇(x◇y)))) = (x◇((x◇(y◇(x◇y)))◇(x◇(y◇(x◇y)))))) s2 (h5102 x y))
  exact s3
 have h5260 (x y : G):(x◇((y◇x)◇((x◇(x◇(x◇x)))◇y))) = (x◇(x◇(x◇x))):=by
  have s0:=(t (fun q => (q◇((y◇x)◇((x◇(x◇(x◇x)))◇y))) = (x◇(x◇(x◇x)))) (h3 x (x◇(x◇(x◇x))) y) (h3821 x))
  exact s0
 have h5261 (x y : G):(((x◇(x◇(x◇x)))◇y)◇(x◇(y◇x))) = y:=by
  have s0:=(t (fun q => (((x◇(x◇(x◇x)))◇y)◇(q◇(y◇x))) = y) (h3 (x◇(x◇(x◇x))) y x) (h3821 x))
  exact s0
 have h5305 (x y : G):((((x◇(y◇(y◇(y◇y))))◇(y◇x))◇(y◇y))◇(y◇(y◇(y◇y)))) = (y◇y):=by
  have s0:=(t (fun q => ((((x◇(y◇(y◇(y◇y))))◇(q◇x))◇((y◇(y◇(y◇(y◇y))))◇y))◇(y◇(y◇(y◇y)))) = ((y◇(y◇(y◇(y◇y))))◇y)) (h55 x (y◇(y◇(y◇y))) y) (h3821 y))
  have s1:=(t (fun q => ((((x◇(y◇(y◇(y◇y))))◇(y◇x))◇((y◇(y◇(y◇(y◇y))))◇y))◇(y◇(y◇(y◇y)))) = (q◇y)) s0 (h3821 y))
  have s2:=(t (fun q => ((((x◇(y◇(y◇(y◇y))))◇(y◇x))◇(q◇y))◇(y◇(y◇(y◇y)))) = (y◇y)) s1 (h3821 y))
  exact s2
 have h5392 (x : G):(((x◇(x◇x))◇((x◇(x◇x))◇x))◇(x◇(x◇x))) = ((x◇(x◇x))◇x):=by
  have s0:=(t (fun q => (((x◇(x◇x))◇((x◇(x◇x))◇q))◇(x◇(x◇x))) = ((x◇(x◇x))◇((x◇(x◇x))◇(x◇(x◇x))))) (h8 (x◇(x◇x)) (x◇(x◇x))) (h3643 x))
  have s1:=(t (fun q => (((x◇(x◇x))◇((x◇(x◇x))◇x))◇(x◇(x◇x))) = ((x◇(x◇x))◇q)) s0 (h3643 x))
  exact s1
 have h5449 (x : G):((((x◇(x◇x))◇x)◇(x◇(x◇x)))◇(x◇(x◇x))) = (x◇(x◇x)):=by
  have s0:=(t (fun q => ((((x◇(x◇x))◇q)◇(x◇(x◇x)))◇(x◇(x◇x))) = (x◇(x◇x))) (h3569 (x◇(x◇x))) (h3643 x))
  exact s0
 have h5450 (x : G):((x◇(x◇x))◇((x◇(x◇x))◇((x◇(x◇x))◇x))) = (x◇(x◇x)):=by
  have s0:=(t (fun q => ((x◇(x◇x))◇((x◇(x◇x))◇((x◇(x◇x))◇q))) = (x◇(x◇x))) (h3821 (x◇(x◇x))) (h3643 x))
  exact s0
 have h5469 (x y : G):((x◇(x◇(x◇x)))◇((y◇(x◇x))◇(x◇y))) = x:=by
  have s0:=(t (fun q => (q◇((y◇(x◇x))◇(x◇y))) = x) (h3 (x◇x) x y) (h3707 x))
  exact s0
 have h5470 (x y : G):((x◇(y◇y))◇((y◇x)◇(y◇(y◇(y◇y))))) = (y◇y):=by
  have s0:=(t (fun q => ((x◇(y◇y))◇((y◇x)◇q)) = (y◇y)) (h3 x (y◇y) y) (h3707 y))
  exact s0
 have h5538 (x : G):((x◇(x◇x))◇((x◇(x◇x))◇x)) = (x◇(x◇(x◇x))):=by
  have s0:=(t (fun q => (q◇(x◇(x◇x))) = ((x◇(x◇x))◇((x◇(x◇x))◇((x◇(x◇x))◇(x◇(x◇x)))))) (h3707 (x◇(x◇x))) (h3643 x)).symm
  have s1:=(t (fun q => ((x◇(x◇x))◇((x◇(x◇x))◇q)) = (x◇(x◇(x◇x)))) s0 (h3643 x))
  exact s1
 have h5540 (x : G):((x◇(x◇x))◇(x◇(x◇(x◇x)))) = (x◇(x◇x)):=by
  have s0:=h5450 x
  have s1:=(t (fun q => ((x◇(x◇x))◇q) = (x◇(x◇x))) s0 (h5538 x))
  exact s1
 have h5543 (x : G):((x◇(x◇(x◇x)))◇(x◇(x◇x))) = ((x◇(x◇x))◇x):=by
  have s0:=h5392 x
  have s1:=(t (fun q => (q◇(x◇(x◇x))) = ((x◇(x◇x))◇x)) s0 (h5538 x))
  exact s1
 have h5546 (x y : G):((((x◇x)◇(x◇(x◇x)))◇y)◇((x◇(x◇x))◇(y◇(x◇x)))) = y:=by
  have s0:=h3782 x y
  have s1:=(t (fun q => ((((x◇x)◇q)◇y)◇((x◇(x◇x))◇(y◇(x◇x)))) = y) s0 (h5540 x))
  exact s1
 have h5547 (x : G):((x◇(x◇x))◇x) = ((x◇x)◇(x◇x)):=by
  have s0:=h3779 x
  have s1:=(t (fun q => ((x◇(x◇(x◇x)))◇q) = ((x◇x)◇(x◇x))) s0 (h5540 x))
  have s2:=(t (fun q => q = ((x◇x)◇(x◇x))) s1 (h5543 x))
  exact s2
 have h5557 (x : G):((x◇x)◇(x◇(x◇x))) = (x◇(x◇x)):=by
  have s0:=h5449 x
  have s1:=(t (fun q => ((q◇(x◇(x◇x)))◇(x◇(x◇x))) = (x◇(x◇x))) s0 (h5547 x))
  have s2:=(t (fun q => (q◇(x◇(x◇x))) = (x◇(x◇x))) s1 (h3616 x))
  exact s2
 have h5796 (x y : G):(((x◇(x◇x))◇y)◇((x◇(x◇x))◇(y◇(x◇x)))) = y:=by
  have s0:=h5546 x y
  have s1:=(t (fun q => ((q◇y)◇((x◇(x◇x))◇(y◇(x◇x)))) = y) s0 (h5557 x))
  exact s1
 have h5804 (x y : G):(((x◇(x◇(x◇x)))◇y)◇((x◇x)◇(y◇(x◇x)))) = y:=by
  have s0:=(t (fun q => (((x◇(x◇(x◇x)))◇y)◇(q◇(y◇(x◇x)))) = y) (h3 (x◇(x◇(x◇x))) y (x◇x)) (h3828 x))
  exact s0
 have h5814 (x y : G):((((x◇y)◇((y◇y)◇x))◇y)◇(y◇y)) = y:=by
  have s0:=(t (fun q => ((((x◇y)◇((y◇y)◇x))◇y)◇q) = y) (h6 x y (y◇y) y) (h3828 y))
  exact s0
 have h5865 (x y : G):((((x◇y)◇((y◇y)◇x))◇y)◇(((x◇y)◇((y◇y)◇x))◇y)) = (y◇(y◇(y◇y))):=by
  have s0:=(t (fun q => ((((x◇y)◇((y◇y)◇x))◇y)◇(((x◇y)◇((y◇y)◇x))◇((q◇((((x◇y)◇((y◇y)◇x))◇y)◇(y◇y)))◇(y◇y)))) = (((y◇y)◇(y◇(y◇(y◇y))))◇((((x◇y)◇((y◇y)◇x))◇y)◇(y◇y)))) (h18 x y (y◇y) y (y◇y)) (h3828 y))
  have s1:=(t (fun q => ((((x◇y)◇((y◇y)◇x))◇y)◇(((x◇y)◇((y◇y)◇x))◇(((y◇y)◇q)◇(y◇y)))) = (((y◇y)◇(y◇(y◇(y◇y))))◇((((x◇y)◇((y◇y)◇x))◇y)◇(y◇y)))) s0 (h5814 x y))
  have s2:=(t (fun q => ((((x◇y)◇((y◇y)◇x))◇y)◇(((x◇y)◇((y◇y)◇x))◇(q◇(y◇y)))) = (((y◇y)◇(y◇(y◇(y◇y))))◇((((x◇y)◇((y◇y)◇x))◇y)◇(y◇y)))) s1 (h3707 y))
  have s3:=(t (fun q => ((((x◇y)◇((y◇y)◇x))◇y)◇(((x◇y)◇((y◇y)◇x))◇q)) = (((y◇y)◇(y◇(y◇(y◇y))))◇((((x◇y)◇((y◇y)◇x))◇y)◇(y◇y)))) s2 (h4781 y))
  have s4:=(t (fun q => ((((x◇y)◇((y◇y)◇x))◇y)◇(((x◇y)◇((y◇y)◇x))◇y)) = (q◇((((x◇y)◇((y◇y)◇x))◇y)◇(y◇y)))) s3 (h3828 y))
  have s5:=(t (fun q => ((((x◇y)◇((y◇y)◇x))◇y)◇(((x◇y)◇((y◇y)◇x))◇y)) = ((y◇y)◇q)) s4 (h5814 x y))
  have s6:=(t (fun q => ((((x◇y)◇((y◇y)◇x))◇y)◇(((x◇y)◇((y◇y)◇x))◇y)) = q) s5 (h3707 y))
  exact s6
 have h6139 (x y : G):((((x◇(y◇y))◇((y◇y)◇x))◇y)◇y) = y:=by
  have s0:=(t (fun q => ((((x◇(y◇y))◇((y◇y)◇x))◇y)◇((y◇y)◇q)) = y) (h6 x (y◇y) (y◇y) y) (h3484 y))
  have s1:=(t (fun q => ((((x◇(y◇y))◇((y◇y)◇x))◇y)◇q) = y) s0 (h3 y y y))
  exact s1
 have h6403 (x y z : G):((((x◇(y◇(z◇y)))◇(z◇x))◇(z◇((y◇(y◇(y◇y)))◇z)))◇(y◇(z◇y))) = (z◇((y◇(y◇(y◇y)))◇z)):=by
  have s0:=(t (fun q => ((((x◇(y◇(z◇y)))◇(q◇x))◇((((y◇(y◇(y◇y)))◇z)◇(y◇(z◇y)))◇((y◇(y◇(y◇y)))◇z)))◇(y◇(z◇y))) = ((((y◇(y◇(y◇y)))◇z)◇(y◇(z◇y)))◇((y◇(y◇(y◇y)))◇z))) (h55 x (y◇(z◇y)) ((y◇(y◇(y◇y)))◇z)) (h5261 y z))
  have s1:=(t (fun q => ((((x◇(y◇(z◇y)))◇(z◇x))◇((((y◇(y◇(y◇y)))◇z)◇(y◇(z◇y)))◇((y◇(y◇(y◇y)))◇z)))◇(y◇(z◇y))) = (q◇((y◇(y◇(y◇y)))◇z))) s0 (h5261 y z))
  have s2:=(t (fun q => ((((x◇(y◇(z◇y)))◇(z◇x))◇(q◇((y◇(y◇(y◇y)))◇z)))◇(y◇(z◇y))) = (z◇((y◇(y◇(y◇y)))◇z))) s1 (h5261 y z))
  exact s2
 have h6762 (x y : G):(((((x◇(x◇(x◇x)))◇(((y◇x)◇((x◇x)◇y))◇x))◇(((y◇x)◇((x◇x)◇y))◇x))◇(((y◇x)◇((x◇x)◇y))◇x))◇(((y◇x)◇((x◇x)◇y))◇x)) = (((y◇x)◇((x◇x)◇y))◇x):=by
  have s0:=(t (fun q => (((((((x◇x)◇((((y◇x)◇((x◇x)◇y))◇x)◇(((y◇x)◇((x◇x)◇y))◇x)))◇q)◇(((y◇x)◇((x◇x)◇y))◇x))◇(((y◇x)◇((x◇x)◇y))◇x))◇(((y◇x)◇((x◇x)◇y))◇x))◇(((y◇x)◇((x◇x)◇y))◇x)) = (((y◇x)◇((x◇x)◇y))◇x)) (h134 (x◇x) (((y◇x)◇((x◇x)◇y))◇x)) (h5814 y x))
  have s1:=(t (fun q => (((((((x◇x)◇q)◇x)◇(((y◇x)◇((x◇x)◇y))◇x))◇(((y◇x)◇((x◇x)◇y))◇x))◇(((y◇x)◇((x◇x)◇y))◇x))◇(((y◇x)◇((x◇x)◇y))◇x)) = (((y◇x)◇((x◇x)◇y))◇x)) s0 (h5865 y x))
  have s2:=(t (fun q => (((((q◇x)◇(((y◇x)◇((x◇x)◇y))◇x))◇(((y◇x)◇((x◇x)◇y))◇x))◇(((y◇x)◇((x◇x)◇y))◇x))◇(((y◇x)◇((x◇x)◇y))◇x)) = (((y◇x)◇((x◇x)◇y))◇x)) s1 (h3828 x))
  have s3:=(t (fun q => ((((q◇(((y◇x)◇((x◇x)◇y))◇x))◇(((y◇x)◇((x◇x)◇y))◇x))◇(((y◇x)◇((x◇x)◇y))◇x))◇(((y◇x)◇((x◇x)◇y))◇x)) = (((y◇x)◇((x◇x)◇y))◇x)) s2 (h3707 x))
  exact s3
 have h6776 (x y z u w : G):((((x◇(y◇(z◇z)))◇(((u◇y)◇((z◇z)◇u))◇x))◇(((w◇z)◇((z◇z)◇w))◇z))◇(((u◇y)◇((z◇z)◇u))◇z)) = (((w◇z)◇((z◇z)◇w))◇z):=by
  have s0:=(t (fun q => ((((x◇(y◇(z◇z)))◇(((u◇y)◇((z◇z)◇u))◇x))◇(((w◇z)◇((z◇z)◇w))◇z))◇(((u◇y)◇((z◇z)◇u))◇q)) = (((w◇z)◇((z◇z)◇w))◇z)) (h10 x y (z◇z) u (((w◇z)◇((z◇z)◇w))◇z)) (h5814 w z))
  exact s0
 have h6852 (x y : G):(((x◇y)◇((y◇y)◇x))◇y) = (y◇(y◇(y◇y))):=by
  have s0:=(h6762 y x).symm
  have s1:=(t (fun q => (((x◇y)◇((y◇y)◇x))◇y) = (q◇(((x◇y)◇((y◇y)◇x))◇y))) s0 (h6776 y y y x x))
  have s2:=(t (fun q => (((x◇y)◇((y◇y)◇x))◇y) = q) s1 (h5865 x y))
  exact s2
 have h7157 (x y : G):(((x◇(y◇(x◇y)))◇(x◇(y◇(x◇y))))◇((x◇(y◇(x◇y)))◇(x◇(y◇(x◇y))))) = (x◇(y◇(x◇y))):=by
  have s0:=(t (fun q => (((x◇(y◇(x◇y)))◇((x◇(y◇(x◇y)))◇(x◇(y◇(x◇y)))))◇((x◇(y◇(x◇y)))◇((x◇(y◇(x◇y)))◇(q◇(x◇(y◇(x◇y))))))) = (x◇(y◇(x◇y)))) (h431 (x◇(y◇(x◇y))) (y◇(x◇y))) (h23 (y◇(x◇y)) x y))
  have s1:=(t (fun q => (((x◇(y◇(x◇y)))◇((x◇(y◇(x◇y)))◇(x◇(y◇(x◇y)))))◇q) = (x◇(y◇(x◇y)))) s0 (h5102 x y))
  have s2:=(t (fun q => q = (x◇(y◇(x◇y)))) s1 (h5547 (x◇(y◇(x◇y)))))
  exact s2
 have h7238 (x y : G):((((((x◇(x◇(y◇(x◇y))))◇(y◇(x◇y)))◇((x◇(y◇(x◇y)))◇(x◇(y◇(x◇y)))))◇(x◇(y◇(x◇y))))◇(x◇(y◇(x◇y))))◇(x◇(y◇(x◇y)))) = (x◇(y◇(x◇y))):=by
  have s0:=(t (fun q => ((((((x◇(x◇(y◇(x◇y))))◇(y◇(x◇y)))◇((x◇(y◇(x◇y)))◇(x◇(y◇(x◇y)))))◇q)◇(x◇(y◇(x◇y))))◇(x◇(y◇(x◇y)))) = (x◇(y◇(x◇y)))) (h6139 ((x◇(x◇(y◇(x◇y))))◇(y◇(x◇y))) (x◇(y◇(x◇y)))) (h23 (x◇(y◇(x◇y))) x y))
  exact s0
 have h7242 (x y : G):((x◇(y◇(x◇y)))◇(((x◇(y◇(x◇y)))◇(x◇(y◇(x◇y))))◇(((x◇(x◇(y◇(x◇y))))◇(y◇(x◇y)))◇((x◇(y◇(x◇y)))◇((x◇(y◇(x◇y)))◇(x◇(y◇(x◇y)))))))) = ((x◇(x◇(y◇(x◇y))))◇(y◇(x◇y))):=by
  have s0:=(t (fun q => (q◇(((x◇(y◇(x◇y)))◇(x◇(y◇(x◇y))))◇(((x◇(x◇(y◇(x◇y))))◇(y◇(x◇y)))◇((x◇(y◇(x◇y)))◇((x◇(y◇(x◇y)))◇(x◇(y◇(x◇y)))))))) = ((x◇(x◇(y◇(x◇y))))◇(y◇(x◇y)))) (h3482 (x◇(y◇(x◇y))) ((x◇(x◇(y◇(x◇y))))◇(y◇(x◇y)))) (h23 (x◇(y◇(x◇y))) x y))
  exact s0
 have h7298 (x y : G):((x◇(x◇(y◇(x◇y))))◇(y◇(x◇y))) = ((x◇(y◇(x◇y)))◇((x◇(y◇(x◇y)))◇(x◇(y◇(x◇y))))):=by
  have s0:=(t (fun q => (q◇((x◇(y◇(x◇y)))◇(((x◇(x◇(y◇(x◇y))))◇(y◇(x◇y)))◇((x◇(y◇(x◇y)))◇((x◇(y◇(x◇y)))◇((x◇(y◇(x◇y)))◇(x◇(y◇(x◇y))))))))) = ((x◇(x◇(y◇(x◇y))))◇(y◇(x◇y)))) (h5100 (x◇(y◇(x◇y))) ((x◇(x◇(y◇(x◇y))))◇(y◇(x◇y)))) (h23 (x◇(y◇(x◇y))) x y)).symm
  have s1:=(t (fun q => ((x◇(x◇(y◇(x◇y))))◇(y◇(x◇y))) = ((x◇(y◇(x◇y)))◇((x◇(y◇(x◇y)))◇(((x◇(x◇(y◇(x◇y))))◇(y◇(x◇y)))◇q)))) s0 (h5102 x y))
  have s2:=(t (fun q => ((x◇(x◇(y◇(x◇y))))◇(y◇(x◇y))) = ((x◇(y◇(x◇y)))◇q)) s1 (h3225 x y))
  exact s2
 have h7299 (x y : G):((x◇(y◇(x◇y)))◇((x◇(y◇(x◇y)))◇(x◇(y◇(x◇y))))) = ((x◇(y◇(x◇y)))◇(x◇(y◇(x◇y)))):=by
  have s0:=(h7242 x y).symm
  have s1:=(t (fun q => ((x◇(x◇(y◇(x◇y))))◇(y◇(x◇y))) = ((x◇(y◇(x◇y)))◇(((x◇(y◇(x◇y)))◇(x◇(y◇(x◇y))))◇(q◇((x◇(y◇(x◇y)))◇((x◇(y◇(x◇y)))◇(x◇(y◇(x◇y))))))))) s0 (h7298 x y))
  have s2:=(t (fun q => ((x◇(x◇(y◇(x◇y))))◇(y◇(x◇y))) = ((x◇(y◇(x◇y)))◇(((x◇(y◇(x◇y)))◇(x◇(y◇(x◇y))))◇q))) s1 (h3643 (x◇(y◇(x◇y)))))
  have s3:=(t (fun q => ((x◇(x◇(y◇(x◇y))))◇(y◇(x◇y))) = ((x◇(y◇(x◇y)))◇q)) s2 (h3707 (x◇(y◇(x◇y)))))
  have s4:=(t (fun q => ((x◇(x◇(y◇(x◇y))))◇(y◇(x◇y))) = ((x◇(y◇(x◇y)))◇q)) s3 (h5102 x y))
  have s5:=(t (fun q => q = ((x◇(y◇(x◇y)))◇(x◇(y◇(x◇y))))) s4 (h7298 x y))
  exact s5
 have h7300 (x y : G):((x◇(y◇(x◇y)))◇(x◇(y◇(x◇y)))) = (x◇(y◇(x◇y))):=by
  have s0:=h7238 x y
  have s1:=(t (fun q => ((((q◇((x◇(y◇(x◇y)))◇(x◇(y◇(x◇y)))))◇(x◇(y◇(x◇y))))◇(x◇(y◇(x◇y))))◇(x◇(y◇(x◇y)))) = (x◇(y◇(x◇y)))) s0 (h7298 x y))
  have s2:=(t (fun q => ((((q◇((x◇(y◇(x◇y)))◇(x◇(y◇(x◇y)))))◇(x◇(y◇(x◇y))))◇(x◇(y◇(x◇y))))◇(x◇(y◇(x◇y)))) = (x◇(y◇(x◇y)))) s1 (h7299 x y))
  have s3:=(t (fun q => (((q◇(x◇(y◇(x◇y))))◇(x◇(y◇(x◇y))))◇(x◇(y◇(x◇y)))) = (x◇(y◇(x◇y)))) s2 (h7157 x y))
  have s4:=(t (fun q => (q◇(x◇(y◇(x◇y)))) = (x◇(y◇(x◇y)))) s3 (h3707 (x◇(y◇(x◇y)))))
  have s5:=(t (fun q => (((x◇(y◇(x◇y)))◇q)◇(x◇(y◇(x◇y)))) = (x◇(y◇(x◇y)))) s4 (h7299 x y))
  have s6:=(t (fun q => (q◇(x◇(y◇(x◇y)))) = (x◇(y◇(x◇y)))) s5 (h7299 x y))
  have s7:=(t (fun q => q = (x◇(y◇(x◇y)))) s6 (h3707 (x◇(y◇(x◇y)))))
  have s8:=(t (fun q => ((x◇(y◇(x◇y)))◇q) = (x◇(y◇(x◇y)))) s7 (h7299 x y))
  have s9:=(t (fun q => q = (x◇(y◇(x◇y)))) s8 (h7299 x y))
  exact s9
 have h7313 (x y : G):((((x◇(y◇(x◇y)))◇((y◇(x◇y))◇(x◇(y◇(x◇y)))))◇(x◇(x◇(y◇(x◇y)))))◇(x◇(y◇(x◇y)))) = (x◇(x◇(y◇(x◇y)))):=by
  have s0:=h5224 x y
  have s1:=(t (fun q => ((((x◇(y◇(x◇y)))◇((y◇(x◇y))◇(x◇(y◇(x◇y)))))◇(x◇((x◇(y◇(x◇y)))◇(x◇(y◇(x◇y))))))◇(x◇(y◇(x◇y)))) = (x◇q)) s0 (h7300 x y))
  have s2:=(t (fun q => ((((x◇(y◇(x◇y)))◇((y◇(x◇y))◇(x◇(y◇(x◇y)))))◇(x◇q))◇(x◇(y◇(x◇y)))) = (x◇(x◇(y◇(x◇y))))) s1 (h7300 x y))
  exact s2
 have h7996 (x y : G):((x◇y)◇((y◇y)◇x)) = (y◇y):=by
  have s0:=(t (fun q => ((y◇y)◇((y◇(y◇(y◇y)))◇q)) = ((x◇y)◇((y◇y)◇x))) (h5 (y◇y) y y x) (h6852 x y)).symm
  have s1:=(t (fun q => ((x◇y)◇((y◇y)◇x)) = ((y◇y)◇q)) s0 (h7300 y y))
  have s2:=(t (fun q => ((x◇y)◇((y◇y)◇x)) = q) s1 (h3828 y))
  exact s2
 have h8181 (x y z : G):((((x◇x)◇y)◇z)◇((x◇x)◇(z◇(y◇x)))) = z:=by
  have s0:=(t (fun q => ((((x◇x)◇y)◇z)◇(q◇(z◇(y◇x)))) = z) (h3 ((x◇x)◇y) z (y◇x)) (h7996 y x))
  exact s0
 have h8184 (x y : G):((((x◇y)◇(y◇x))◇y)◇y) = (y◇y):=by
  have s0:=(t (fun q => ((((x◇y)◇(y◇x))◇y)◇q) = (y◇y)) (h7996 ((x◇y)◇(y◇x)) y) (h3 y y x))
  exact s0
 have h8193 (x y : G):((x◇(y◇x))◇((y◇y)◇(y◇(x◇(y◇x))))) = (y◇y):=by
  have s0:=(t (fun q => (q◇((y◇y)◇(y◇(x◇(y◇x))))) = (y◇y)) (h7996 (y◇(x◇(y◇x))) y) (h8 y x))
  exact s0
 have h8298 (x y : G):((x◇(y◇(y◇y)))◇(y◇x)) = y:=by
  have s0:=(t (fun q => ((x◇(y◇(y◇y)))◇(q◇x)) = ((y◇(y◇y))◇(y◇(y◇y)))) (h7996 x (y◇(y◇y))) (h3643 y))
  have s1:=(t (fun q => ((x◇(y◇(y◇y)))◇(y◇x)) = q) s0 (h3643 y))
  exact s1
 have h8363 (x y z : G):(((x◇y)◇z)◇(x◇(z◇(y◇(x◇(x◇x)))))) = z:=by
  have s0:=(t (fun q => (((x◇y)◇z)◇(q◇(z◇(y◇(x◇(x◇x)))))) = z) (h3 (x◇y) z (y◇(x◇(x◇x)))) (h8298 y x))
  exact s0
 have h8536 (x y z : G):((x◇x)◇((y◇(((z◇x)◇(x◇z))◇x))◇(x◇y))) = x:=by
  have s0:=(t (fun q => (q◇((y◇(((z◇x)◇(x◇z))◇x))◇(x◇y))) = x) (h3 (((z◇x)◇(x◇z))◇x) x y) (h8184 z x))
  exact s0
 have h8695 (x y : G):((x◇x)◇((x◇x)◇(((y◇x)◇(x◇y))◇x))) = (x◇x):=by
  have s0:=(t (fun q => (q◇((x◇x)◇(((y◇x)◇(x◇y))◇x))) = (x◇x)) (h7996 (((y◇x)◇(x◇y))◇x) x) (h8184 y x))
  exact s0
 have h10219 (x y : G):((x◇(y◇(x◇y)))◇(((((x◇(y◇(x◇y)))◇(y◇(x◇y)))◇(x◇(y◇(x◇y))))◇(x◇(x◇(y◇(x◇y)))))◇(x◇(y◇(x◇y))))) = ((y◇(x◇y))◇(x◇(y◇(x◇y)))):=by
  have s0:=(t (fun q => ((x◇(y◇(x◇y)))◇(((((x◇(y◇(x◇y)))◇(y◇(x◇y)))◇((x◇(y◇(x◇y)))◇((x◇(y◇(x◇y)))◇((x◇(y◇(x◇y)))◇(x◇(y◇(x◇y)))))))◇(x◇(x◇(y◇(x◇y)))))◇q)) = ((y◇(x◇y))◇((x◇(y◇(x◇y)))◇(x◇(y◇(x◇y)))))) (h28 (x◇(y◇(x◇y))) (((x◇(y◇(x◇y)))◇(y◇(x◇y)))◇((x◇(y◇(x◇y)))◇((x◇(y◇(x◇y)))◇((x◇(y◇(x◇y)))◇(x◇(y◇(x◇y))))))) x y) (h5470 (y◇(x◇y)) (x◇(y◇(x◇y)))))
  have s1:=(t (fun q => ((x◇(y◇(x◇y)))◇(((((x◇(y◇(x◇y)))◇(y◇(x◇y)))◇((x◇(y◇(x◇y)))◇((x◇(y◇(x◇y)))◇q)))◇(x◇(x◇(y◇(x◇y)))))◇((x◇(y◇(x◇y)))◇(x◇(y◇(x◇y)))))) = ((y◇(x◇y))◇((x◇(y◇(x◇y)))◇(x◇(y◇(x◇y)))))) s0 (h7300 x y))
  have s2:=(t (fun q => ((x◇(y◇(x◇y)))◇(((((x◇(y◇(x◇y)))◇(y◇(x◇y)))◇((x◇(y◇(x◇y)))◇q))◇(x◇(x◇(y◇(x◇y)))))◇((x◇(y◇(x◇y)))◇(x◇(y◇(x◇y)))))) = ((y◇(x◇y))◇((x◇(y◇(x◇y)))◇(x◇(y◇(x◇y)))))) s1 (h7300 x y))
  have s3:=(t (fun q => ((x◇(y◇(x◇y)))◇(((((x◇(y◇(x◇y)))◇(y◇(x◇y)))◇q)◇(x◇(x◇(y◇(x◇y)))))◇((x◇(y◇(x◇y)))◇(x◇(y◇(x◇y)))))) = ((y◇(x◇y))◇((x◇(y◇(x◇y)))◇(x◇(y◇(x◇y)))))) s2 (h7300 x y))
  have s4:=(t (fun q => ((x◇(y◇(x◇y)))◇(((((x◇(y◇(x◇y)))◇(y◇(x◇y)))◇(x◇(y◇(x◇y))))◇(x◇(x◇(y◇(x◇y)))))◇q)) = ((y◇(x◇y))◇((x◇(y◇(x◇y)))◇(x◇(y◇(x◇y)))))) s3 (h7300 x y))
  have s5:=(t (fun q => ((x◇(y◇(x◇y)))◇(((((x◇(y◇(x◇y)))◇(y◇(x◇y)))◇(x◇(y◇(x◇y))))◇(x◇(x◇(y◇(x◇y)))))◇(x◇(y◇(x◇y))))) = ((y◇(x◇y))◇q)) s4 (h7300 x y))
  exact s5
 have h10589 (x y : G):((x◇(y◇(x◇y)))◇(x◇(((x◇((y◇(x◇y))◇(x◇x)))◇(y◇(x◇y)))◇(x◇(x◇(x◇x)))))) = ((x◇((y◇(x◇y))◇(x◇x)))◇(y◇(x◇y))):=by
  have s0:=(t (fun q => ((x◇(y◇(x◇y)))◇(q◇(((x◇((y◇(x◇y))◇(x◇x)))◇(y◇(x◇y)))◇(x◇(x◇(x◇x)))))) = ((x◇((y◇(x◇y))◇(x◇x)))◇(y◇(x◇y)))) (h29 x y (x◇(x◇(x◇x))) ((y◇(x◇y))◇(x◇x))) (h5469 x (y◇(x◇y))))
  exact s0
 have h10788 (x y : G):(((x◇y)◇(y◇x))◇((((y◇(y◇y))◇((((x◇y)◇(y◇x))◇y)◇(y◇y)))◇y)◇(((x◇y)◇(y◇x))◇y))) = ((y◇(y◇y))◇(((x◇y)◇(y◇x))◇y)):=by
  have s0:=(t (fun q => (((x◇y)◇(y◇x))◇((((y◇(y◇y))◇((((x◇y)◇(y◇x))◇y)◇(y◇y)))◇y)◇q)) = ((y◇(y◇y))◇(((x◇y)◇(y◇x))◇y))) (h9 x y y ((y◇(y◇y))◇((((x◇y)◇(y◇x))◇y)◇(y◇y))) y) (h5796 y (((x◇y)◇(y◇x))◇y)))
  exact s0
 have h10999 (x y : G):(x◇((((y◇y)◇(x◇(y◇y)))◇((y◇y)◇(x◇(y◇y))))◇((y◇(y◇(y◇y)))◇x))) = (((y◇y)◇(x◇(y◇y)))◇((y◇y)◇(x◇(y◇y)))):=by
  have s0:=(t (fun q => (q◇((((y◇y)◇(x◇(y◇y)))◇((y◇y)◇(x◇(y◇y))))◇((y◇(y◇(y◇y)))◇x))) = (((y◇y)◇(x◇(y◇y)))◇((y◇y)◇(x◇(y◇y))))) (h7996 ((y◇(y◇(y◇y)))◇x) ((y◇y)◇(x◇(y◇y)))) (h5804 y x))
  exact s0
 have h11730 (x y : G):((((x◇(y◇(x◇y)))◇(x◇x))◇(y◇(x◇y)))◇((x◇(y◇(x◇y)))◇(x◇x))) = (y◇(x◇y)):=by
  have s0:=(t (fun q => (((((x◇(y◇(x◇y)))◇(x◇(y◇(x◇y))))◇(x◇x))◇(y◇(x◇y)))◇(((x◇(y◇(x◇y)))◇(x◇(y◇(x◇y))))◇q)) = (y◇(x◇y))) (h8181 (x◇(y◇(x◇y))) (x◇x) (y◇(x◇y))) (h8193 y x))
  have s1:=(t (fun q => (((((x◇(y◇(x◇y)))◇(x◇(y◇(x◇y))))◇(x◇x))◇(y◇(x◇y)))◇(q◇(x◇x))) = (y◇(x◇y))) s0 (h7300 x y))
  have s2:=(t (fun q => (((q◇(x◇x))◇(y◇(x◇y)))◇((x◇(y◇(x◇y)))◇(x◇x))) = (y◇(x◇y))) s1 (h7300 x y))
  exact s2
 have h12125 (x y : G):((x◇(x◇x))◇((y◇(x◇x))◇((x◇x)◇y))) = x:=by
  have s0:=(t (fun q => ((((x◇x)◇((x◇x)◇((x◇x)◇(x◇x))))◇x)◇q) = x) (h51 (x◇x) (x◇x) (x◇x) x y) (h12 x x y x))
  have s1:=(t (fun q => ((((x◇x)◇q)◇x)◇((y◇(x◇x))◇((x◇x)◇y))) = x) s0 (h3 x x x))
  have s2:=(t (fun q => ((q◇x)◇((y◇(x◇x))◇((x◇x)◇y))) = x) s1 (h3707 x))
  have s3:=(t (fun q => (q◇((y◇(x◇x))◇((x◇x)◇y))) = x) s2 (h8 x x))
  exact s3
 have h12614 (x y : G):((x◇(x◇x))◇((((y◇x)◇(x◇y))◇x)◇(x◇x))) = x:=by
  have s0:=(t (fun q => ((x◇(x◇x))◇(q◇((x◇x)◇((x◇x)◇(((y◇x)◇(x◇y))◇x))))) = x) (h12125 x ((x◇x)◇(((y◇x)◇(x◇y))◇x))) (h24 x x y))
  have s1:=(t (fun q => ((x◇(x◇x))◇((((y◇x)◇(x◇y))◇x)◇q)) = x) s0 (h8695 x y))
  exact s1
 have h12675 (x y : G):(((x◇y)◇(y◇x))◇((y◇y)◇(((x◇y)◇(y◇x))◇y))) = ((y◇(y◇y))◇(((x◇y)◇(y◇x))◇y)):=by
  have s0:=h10788 x y
  have s1:=(t (fun q => (((x◇y)◇(y◇x))◇((q◇y)◇(((x◇y)◇(y◇x))◇y))) = ((y◇(y◇y))◇(((x◇y)◇(y◇x))◇y))) s0 (h12614 y x))
  exact s1
 have h12685 (x y : G):((x◇x)◇(((y◇x)◇(x◇y))◇x)) = (x◇(x◇(x◇x))):=by
  have s0:=(t (fun q => ((((x◇x)◇((x◇x)◇x))◇((x◇x)◇(((y◇x)◇(x◇y))◇x)))◇q) = ((x◇x)◇(((y◇x)◇(x◇y))◇x))) (h6 x x (x◇x) ((x◇x)◇(((y◇x)◇(x◇y))◇x))) (h8536 x (x◇x) y)).symm
  have s1:=(t (fun q => ((x◇x)◇(((y◇x)◇(x◇y))◇x)) = ((q◇((x◇x)◇(((y◇x)◇(x◇y))◇x)))◇x)) s0 (h7996 x x))
  have s2:=(t (fun q => ((x◇x)◇(((y◇x)◇(x◇y))◇x)) = (q◇x)) s1 (h8695 x y))
  have s3:=(t (fun q => ((x◇x)◇(((y◇x)◇(x◇y))◇x)) = q) s2 (h3707 x))
  exact s3
 have h12879 (x y z : G):(x◇(x◇(((y◇(((z◇x)◇(x◇z))◇x))◇(x◇y))◇(x◇(x◇(x◇x)))))) = ((y◇(((z◇x)◇(x◇z))◇x))◇(x◇y)):=by
  have s0:=(t (fun q => (q◇(x◇(((y◇(((z◇x)◇(x◇z))◇x))◇(x◇y))◇(x◇(x◇(x◇x)))))) = ((y◇(((z◇x)◇(x◇z))◇x))◇(x◇y))) (h8363 x x ((y◇(((z◇x)◇(x◇z))◇x))◇(x◇y))) (h8536 x y z))
  exact s0
 have h12954 (x y : G):(((x◇y)◇(y◇x))◇(y◇(y◇(y◇y)))) = ((y◇(y◇y))◇(((x◇y)◇(y◇x))◇y)):=by
  have s0:=h12675 x y
  have s1:=(t (fun q => (((x◇y)◇(y◇x))◇q) = ((y◇(y◇y))◇(((x◇y)◇(y◇x))◇y))) s0 (h12685 y x))
  exact s1
 have h13876 (x y : G):(((x◇y)◇(y◇x))◇y) = y:=by
  have s0:=(t (fun q => (((y◇y)◇(((x◇y)◇(y◇x))◇y))◇(q◇y)) = (((x◇y)◇(y◇x))◇y)) (h52 (y◇y) x y y y) (h8298 y y)).symm
  have s1:=(t (fun q => (((x◇y)◇(y◇x))◇y) = (q◇(y◇y))) s0 (h12685 y x))
  have s2:=(t (fun q => (((x◇y)◇(y◇x))◇y) = q) s1 (h8298 y y))
  exact s2
 have h14096 (x y : G):(((x◇y)◇(y◇x))◇(y◇(y◇(y◇y)))) = ((y◇y)◇(y◇y)):=by
  have s0:=h12954 x y
  have s1:=(t (fun q => (((x◇y)◇(y◇x))◇(y◇(y◇(y◇y)))) = ((y◇(y◇y))◇q)) s0 (h13876 x y))
  have s2:=(t (fun q => (((x◇y)◇(y◇x))◇(y◇(y◇(y◇y)))) = q) s1 (h5547 y))
  exact s2
 have h14098 (x y : G):((x◇y)◇(y◇x)) = ((y◇y)◇(y◇y)):=by
  have s0:=h12879 y x x
  have s1:=(t (fun q => (y◇(y◇(((x◇q)◇(y◇x))◇(y◇(y◇(y◇y)))))) = ((x◇(((x◇y)◇(y◇x))◇y))◇(y◇x))) s0 (h13876 x y))
  have s2:=(t (fun q => (y◇(y◇q)) = ((x◇(((x◇y)◇(y◇x))◇y))◇(y◇x))) s1 (h14096 x y))
  have s3:=(t (fun q => (y◇q) = ((x◇(((x◇y)◇(y◇x))◇y))◇(y◇x))) s2 (h3484 y))
  have s4:=(t (fun q => q = ((x◇(((x◇y)◇(y◇x))◇y))◇(y◇x))) s3 (h3484 y))
  have s5:=(t (fun q => ((y◇y)◇(y◇y)) = ((x◇q)◇(y◇x))) s4 (h13876 x y)).symm
  exact s5
 have h14319 (x y : G):((x◇((x◇y)◇(y◇(x◇(x◇x)))))◇(x◇y)) = (x◇y):=by
  have s0:=(t (fun q => ((q◇((x◇y)◇(y◇(x◇(x◇x)))))◇(x◇y)) = (x◇y)) (h13876 (y◇(x◇(x◇x))) (x◇y)) (h8298 y x))
  exact s0
 have h14435 (x y z : G):((((x◇y)◇(z◇x))◇(y◇z))◇z) = (((y◇z)◇(y◇z))◇((y◇z)◇(y◇z))):=by
  have s0:=(t (fun q => ((((x◇y)◇(z◇x))◇(y◇z))◇q) = (((y◇z)◇(y◇z))◇((y◇z)◇(y◇z)))) (h14098 ((x◇y)◇(z◇x)) (y◇z)) (h3 y z x))
  exact s0
 have h14806 (x y : G):(((x◇y)◇(x◇y))◇((x◇y)◇(x◇y))) = (x◇((x◇y)◇(y◇(x◇(x◇x))))):=by
  have s0:=(t (fun q => (q◇((x◇y)◇(y◇(x◇(x◇x))))) = (((x◇y)◇(x◇y))◇((x◇y)◇(x◇y)))) (h14098 (y◇(x◇(x◇x))) (x◇y)) (h8298 y x)).symm
  exact s0
 have h14959 (x y z : G):((x◇y)◇(y◇x)) = ((z◇y)◇(y◇z)):=by
  have s0:=(t (fun q => ((x◇y)◇(y◇x)) = q) (h14098 x y) ((h14098 z y).symm))
  exact s0
 have h15065 (x y z : G):((((x◇y)◇(z◇x))◇(y◇z))◇z) = (y◇((y◇z)◇(z◇(y◇(y◇y))))):=by
  have s0:=h14435 x y z
  have s1:=(t (fun q => ((((x◇y)◇(z◇x))◇(y◇z))◇z) = q) s0 (h14806 y z))
  exact s1
 have h15217 (x y z u : G):(((x◇y)◇z)◇(((u◇x)◇(x◇u))◇(z◇(y◇x)))) = z:=by
  have s0:=(t (fun q => (((x◇y)◇z)◇(q◇(z◇(y◇x)))) = z) (h3 (x◇y) z (y◇x)) (h14959 y x u))
  exact s0
 have h15220 (x y z : G):((x◇(y◇z))◇((y◇z)◇x)) = (y◇((y◇z)◇(z◇(y◇(y◇y))))):=by
  have s0:=(t (fun q => ((((x◇y)◇(z◇x))◇(y◇z))◇q) = ((x◇(y◇z))◇((y◇z)◇x))) (h14959 ((x◇y)◇(z◇x)) (y◇z) x) (h3 y z x)).symm
  have s1:=(t (fun q => ((x◇(y◇z))◇((y◇z)◇x)) = q) s0 (h15065 x y z))
  exact s1
 have h19830 (x y : G):(((x◇(x◇y))◇(x◇(y◇x)))◇(x◇y)) = (x◇(y◇x)):=by
  have s0:=(t (fun q => (((x◇(x◇y))◇(x◇(y◇x)))◇q) = (x◇(y◇x))) (h15217 x (x◇y) (x◇(y◇x)) y) (h3 (y◇x) (x◇y) x))
  exact s0
 have h21871 (x y : G):((((x◇(y◇(x◇y)))◇(y◇(x◇y)))◇((x◇(y◇(x◇y)))◇(x◇(x◇(y◇(x◇y))))))◇(y◇(x◇y))) = ((x◇(y◇(x◇y)))◇(x◇(x◇(y◇(x◇y))))):=by
  have s0:=(t (fun q => ((((x◇(y◇(x◇y)))◇q)◇((x◇(y◇(x◇y)))◇(x◇(x◇(y◇(x◇y))))))◇((x◇(y◇(x◇y)))◇x)) = ((x◇(y◇(x◇y)))◇(x◇(x◇(y◇(x◇y)))))) (h19830 (x◇(y◇(x◇y))) x) (h8 x y))
  have s1:=(t (fun q => ((((x◇(y◇(x◇y)))◇(y◇(x◇y)))◇((x◇(y◇(x◇y)))◇(x◇(x◇(y◇(x◇y))))))◇q) = ((x◇(y◇(x◇y)))◇(x◇(x◇(y◇(x◇y)))))) s0 (h8 x y))
  exact s1
 have h23311 (x y z : G):((((x◇y)◇((y◇(y◇(y◇y)))◇x))◇(y◇(y◇(y◇y))))◇((z◇(y◇(((x◇y)◇((y◇(y◇(y◇y)))◇x))◇(y◇(y◇(y◇y))))))◇(y◇z))) = y:=by
  have s0:=(t (fun q => ((((x◇y)◇((y◇(y◇(y◇y)))◇x))◇q)◇((z◇(y◇(((x◇y)◇((y◇(y◇(y◇y)))◇x))◇(y◇((x◇y)◇((y◇(y◇(y◇y)))◇x))))))◇(y◇z))) = y) (h15 ((x◇y)◇((y◇(y◇(y◇y)))◇x)) y z) (h5260 y x))
  have s1:=(t (fun q => ((((x◇y)◇((y◇(y◇(y◇y)))◇x))◇(y◇(y◇(y◇y))))◇((z◇(y◇(((x◇y)◇((y◇(y◇(y◇y)))◇x))◇q)))◇(y◇z))) = y) s0 (h5260 y x))
  exact s1
 have h23345 (x y z u : G):((x◇(x◇(x◇x)))◇((((y◇(x◇(x◇(x◇x))))◇(((z◇x)◇(((u◇x)◇((x◇(x◇(x◇x)))◇u))◇z))◇y))◇x)◇((z◇x)◇(((u◇x)◇((x◇(x◇(x◇x)))◇u))◇z)))) = ((u◇x)◇((x◇(x◇(x◇x)))◇u)):=by
  have s0:=(t (fun q => ((x◇(x◇(x◇x)))◇((((y◇q)◇(((z◇x)◇(((u◇x)◇((x◇(x◇(x◇x)))◇u))◇z))◇y))◇(x◇(x◇(x◇(x◇x)))))◇((z◇x)◇(((u◇x)◇((x◇(x◇(x◇x)))◇u))◇z)))) = ((u◇x)◇((x◇(x◇(x◇x)))◇u))) (h21 (x◇(x◇(x◇x))) y x u x z) (h5260 x u))
  have s1:=(t (fun q => ((x◇(x◇(x◇x)))◇((((y◇(x◇(x◇(x◇x))))◇(((z◇x)◇(((u◇x)◇((x◇(x◇(x◇x)))◇u))◇z))◇y))◇q)◇((z◇x)◇(((u◇x)◇((x◇(x◇(x◇x)))◇u))◇z)))) = ((u◇x)◇((x◇(x◇(x◇x)))◇u))) s0 (h3821 x))
  exact s1
 have h26745 (x y z u : G):((((x◇(y◇(y◇(y◇y))))◇(((z◇y)◇(((u◇y)◇((y◇(y◇(y◇y)))◇u))◇z))◇x))◇y)◇(((z◇y)◇(((u◇y)◇((y◇(y◇(y◇y)))◇u))◇z))◇(y◇(y◇(y◇y))))) = y:=by
  have s0:=(t (fun q => ((((x◇(y◇(y◇(y◇y))))◇(((z◇(y◇(y◇(y◇(y◇y)))))◇(((u◇y)◇((y◇(y◇(y◇y)))◇u))◇z))◇x))◇y)◇(((z◇(y◇(y◇(y◇(y◇y)))))◇(((u◇y)◇((y◇(y◇(y◇y)))◇u))◇z))◇q)) = y) (h64 x (y◇(y◇(y◇y))) z y u y) (h5260 y u))
  have s1:=(t (fun q => ((((x◇(y◇(y◇(y◇y))))◇(((z◇(y◇(y◇(y◇(y◇y)))))◇(((u◇y)◇((y◇(y◇(y◇y)))◇u))◇z))◇x))◇y)◇(((z◇q)◇(((u◇y)◇((y◇(y◇(y◇y)))◇u))◇z))◇(y◇(y◇(y◇y))))) = y) s0 (h3821 y))
  have s2:=(t (fun q => ((((x◇(y◇(y◇(y◇y))))◇(((z◇q)◇(((u◇y)◇((y◇(y◇(y◇y)))◇u))◇z))◇x))◇y)◇(((z◇y)◇(((u◇y)◇((y◇(y◇(y◇y)))◇u))◇z))◇(y◇(y◇(y◇y))))) = y) s1 (h3821 y))
  exact s2
 have h26754 (x y z : G):((x◇((y◇(z◇(y◇z)))◇x))◇(((y◇(z◇(y◇z)))◇((y◇(z◇(y◇z)))◇(x◇((y◇(z◇(y◇z)))◇x))))◇(y◇(z◇(y◇z))))) = (y◇(z◇(y◇z))):=by
  have s0:=(t (fun q => ((x◇((y◇(z◇(y◇z)))◇x))◇(((y◇(z◇(y◇z)))◇((y◇(z◇(y◇z)))◇(x◇((y◇(z◇(y◇z)))◇x))))◇q)) = (y◇(z◇(y◇z)))) (h15 x (y◇(z◇(y◇z))) (y◇(z◇(y◇z)))) (h7300 y z))
  exact s0
 have h26772 (x y z u : G):((x◇(y◇(x◇y)))◇((((z◇((x◇(y◇(x◇y)))◇u))◇((x◇(y◇(x◇y)))◇z))◇(u◇(x◇(y◇(x◇y)))))◇(x◇(y◇(x◇y))))) = (((x◇(y◇(x◇y)))◇u)◇(x◇(y◇(x◇y)))):=by
  have s0:=(t (fun q => ((x◇(y◇(x◇y)))◇((((z◇((x◇(y◇(x◇y)))◇u))◇(q◇z))◇(u◇(x◇(y◇(x◇y)))))◇((x◇(y◇(x◇y)))◇(x◇(y◇(x◇y)))))) = (((x◇(y◇(x◇y)))◇u)◇((x◇(y◇(x◇y)))◇(x◇(y◇(x◇y)))))) (h16 (x◇(y◇(x◇y))) z (x◇(y◇(x◇y))) u) (h7300 x y))
  have s1:=(t (fun q => ((x◇(y◇(x◇y)))◇((((z◇((x◇(y◇(x◇y)))◇u))◇((x◇(y◇(x◇y)))◇z))◇(u◇(x◇(y◇(x◇y)))))◇((x◇(y◇(x◇y)))◇(x◇(y◇(x◇y)))))) = (((x◇(y◇(x◇y)))◇u)◇q)) s0 (h7300 x y))
  have s2:=(t (fun q => ((x◇(y◇(x◇y)))◇((((z◇((x◇(y◇(x◇y)))◇u))◇((x◇(y◇(x◇y)))◇z))◇(u◇(x◇(y◇(x◇y)))))◇q)) = (((x◇(y◇(x◇y)))◇u)◇(x◇(y◇(x◇y))))) s1 (h7300 x y))
  exact s2
 have h26818 (x y z u : G):((((x◇((y◇(z◇(y◇z)))◇u))◇((y◇(z◇(y◇z)))◇x))◇(u◇(y◇(z◇(y◇z)))))◇(y◇(z◇(y◇z)))) = (u◇(y◇(z◇(y◇z)))):=by
  have s0:=(t (fun q => ((((x◇((y◇(z◇(y◇z)))◇u))◇(q◇x))◇(u◇(y◇(z◇(y◇z)))))◇(((y◇(z◇(y◇z)))◇(y◇(z◇(y◇z))))◇(y◇(z◇(y◇z))))) = (u◇(y◇(z◇(y◇z))))) (h54 x (y◇(z◇(y◇z))) u (y◇(z◇(y◇z)))) (h7300 y z))
  have s1:=(t (fun q => ((((x◇((y◇(z◇(y◇z)))◇u))◇((y◇(z◇(y◇z)))◇x))◇(u◇(y◇(z◇(y◇z)))))◇(q◇(y◇(z◇(y◇z))))) = (u◇(y◇(z◇(y◇z))))) s0 (h7300 y z))
  have s2:=(t (fun q => ((((x◇((y◇(z◇(y◇z)))◇u))◇((y◇(z◇(y◇z)))◇x))◇(u◇(y◇(z◇(y◇z)))))◇q) = (u◇(y◇(z◇(y◇z))))) s1 (h7300 y z))
  exact s2
 have h26851 (x y z : G):(((x◇(y◇(x◇y)))◇z)◇(x◇(y◇(x◇y)))) = ((x◇(y◇(x◇y)))◇(z◇(x◇(y◇(x◇y))))):=by
  have s0:=(h26772 x y x z).symm
  have s1:=(t (fun q => (((x◇(y◇(x◇y)))◇z)◇(x◇(y◇(x◇y)))) = ((x◇(y◇(x◇y)))◇q)) s0 (h26818 x x y z))
  exact s1
 have h26863 (x y z : G):((x◇((y◇(z◇(y◇z)))◇x))◇((y◇(z◇(y◇z)))◇(x◇((y◇(z◇(y◇z)))◇x)))) = (y◇(z◇(y◇z))):=by
  have s0:=h26754 x y z
  have s1:=(t (fun q => ((x◇((y◇(z◇(y◇z)))◇x))◇q) = (y◇(z◇(y◇z)))) s0 (h26851 y z ((y◇(z◇(y◇z)))◇(x◇((y◇(z◇(y◇z)))◇x)))))
  have s2:=(t (fun q => ((x◇((y◇(z◇(y◇z)))◇x))◇((y◇(z◇(y◇z)))◇q)) = (y◇(z◇(y◇z)))) s1 (h8 (y◇(z◇(y◇z))) x))
  exact s2
 have h26882 (x y : G):((x◇(y◇(x◇y)))◇(x◇(x◇(y◇(x◇y))))) = ((y◇(x◇y))◇(x◇(y◇(x◇y)))):=by
  have s0:=h10219 x y
  have s1:=(t (fun q => ((x◇(y◇(x◇y)))◇((q◇(x◇(x◇(y◇(x◇y)))))◇(x◇(y◇(x◇y))))) = ((y◇(x◇y))◇(x◇(y◇(x◇y))))) s0 (h26851 x y (y◇(x◇y))))
  have s2:=(t (fun q => ((x◇(y◇(x◇y)))◇q) = ((y◇(x◇y))◇(x◇(y◇(x◇y))))) s1 (h7313 x y))
  exact s2
 have h26891 (x y : G):((x◇(y◇x))◇(y◇(x◇(y◇x)))) = (x◇(y◇x)):=by
  have s0:=(h21871 y x).symm
  have s1:=(t (fun q => ((y◇(x◇(y◇x)))◇(y◇(y◇(x◇(y◇x))))) = ((((y◇(x◇(y◇x)))◇(x◇(y◇x)))◇q)◇(x◇(y◇x)))) s0 (h26882 y x))
  have s2:=(t (fun q => ((y◇(x◇(y◇x)))◇(y◇(y◇(x◇(y◇x))))) = (q◇(x◇(y◇x)))) s1 (h15220 (y◇(x◇(y◇x))) x (y◇x)))
  have s3:=(t (fun q => ((y◇(x◇(y◇x)))◇(y◇(y◇(x◇(y◇x))))) = q) s2 (h14319 x (y◇x)))
  have s4:=(t (fun q => q = (x◇(y◇x))) s3 (h26882 y x))
  exact s4
 have h26894 (x y : G):((x◇(y◇x))◇(x◇(y◇x))) = y:=by
  have s0:=h378 x y
  have s1:=(t (fun q => ((x◇(y◇x))◇q) = y) s0 (h26882 y x))
  have s2:=(t (fun q => ((x◇(y◇x))◇q) = y) s1 (h26891 x y))
  exact s2
 have h26896 (x y z : G):(x◇((y◇(z◇(y◇z)))◇x)) = (y◇(z◇(y◇z))):=by
  have s0:=h26863 x y z
  have s1:=(t (fun q => q = (y◇(z◇(y◇z)))) s0 (h26891 x (y◇(z◇(y◇z)))))
  exact s1
 have h26999 (x y : G):(x◇(y◇(y◇(y◇y)))) = x:=by
  have s0:=h10999 x y
  have s1:=(t (fun q => (x◇(q◇((y◇(y◇(y◇y)))◇x))) = (((y◇y)◇(x◇(y◇y)))◇((y◇y)◇(x◇(y◇y))))) s0 (h26894 (y◇y) x))
  have s2:=(t (fun q => (x◇q) = (((y◇y)◇(x◇(y◇y)))◇((y◇y)◇(x◇(y◇y))))) s1 (h26896 x y y))
  have s3:=(t (fun q => (x◇(y◇(y◇(y◇y)))) = q) s2 (h26894 (y◇y) x))
  exact s3
 have h27036 (x y z : G):(((x◇(y◇(z◇y)))◇(z◇x))◇(y◇(z◇y))) = (y◇(y◇(y◇y))):=by
  have s0:=h6403 x y z
  have s1:=(t (fun q => ((((x◇(y◇(z◇y)))◇(z◇x))◇q)◇(y◇(z◇y))) = (z◇((y◇(y◇(y◇y)))◇z))) s0 (h26896 z y y))
  have s2:=(t (fun q => (q◇(y◇(z◇y))) = (z◇((y◇(y◇(y◇y)))◇z))) s1 (h26999 ((x◇(y◇(z◇y)))◇(z◇x)) y))
  have s3:=(t (fun q => (((x◇(y◇(z◇y)))◇(z◇x))◇(y◇(z◇y))) = q) s2 (h26896 z y y))
  exact s3
 have h27060 (x y z u : G):(((x◇(((y◇z)◇(((u◇z)◇((z◇(z◇(z◇z)))◇u))◇y))◇x))◇z)◇((y◇z)◇(((u◇z)◇((z◇(z◇(z◇z)))◇u))◇y))) = z:=by
  have s0:=h26745 x z y u
  have s1:=(t (fun q => ((((x◇(z◇(z◇(z◇z))))◇(((y◇z)◇(((u◇z)◇((z◇(z◇(z◇z)))◇u))◇y))◇x))◇z)◇q) = z) s0 (h26999 ((y◇z)◇(((u◇z)◇((z◇(z◇(z◇z)))◇u))◇y)) z))
  have s2:=(t (fun q => (((q◇(((y◇z)◇(((u◇z)◇((z◇(z◇(z◇z)))◇u))◇y))◇x))◇z)◇((y◇z)◇(((u◇z)◇((z◇(z◇(z◇z)))◇u))◇y))) = z) s1 (h26999 x z))
  exact s2
 have h27808 (x y : G):((x◇y)◇((y◇(y◇(y◇y)))◇x)) = (y◇(y◇y)):=by
  have s0:=h23345 y x x x
  have s1:=(t (fun q => ((y◇(y◇(y◇y)))◇(((q◇(((x◇y)◇(((x◇y)◇((y◇(y◇(y◇y)))◇x))◇x))◇x))◇y)◇((x◇y)◇(((x◇y)◇((y◇(y◇(y◇y)))◇x))◇x)))) = ((x◇y)◇((y◇(y◇(y◇y)))◇x))) s0 (h26999 x y))
  have s2:=(t (fun q => ((y◇(y◇(y◇y)))◇q) = ((x◇y)◇((y◇(y◇(y◇y)))◇x))) s1 (h27060 x x y x))
  have s3:=(t (fun q => q = ((x◇y)◇((y◇(y◇(y◇y)))◇x))) s2 (h8 y y)).symm
  exact s3
 have h27827 (x y : G):((x◇(x◇x))◇(y◇(x◇y))) = x:=by
  have s0:=h23311 x x y
  have s1:=(t (fun q => ((q◇(x◇(x◇(x◇x))))◇((y◇(x◇(((x◇x)◇((x◇(x◇(x◇x)))◇x))◇(x◇(x◇(x◇x))))))◇(x◇y))) = x) s0 (h27808 x x))
  have s2:=(t (fun q => (q◇((y◇(x◇(((x◇x)◇((x◇(x◇(x◇x)))◇x))◇(x◇(x◇(x◇x))))))◇(x◇y))) = x) s1 (h26999 (x◇(x◇x)) x))
  have s3:=(t (fun q => ((x◇(x◇x))◇((y◇(x◇(q◇(x◇(x◇(x◇x))))))◇(x◇y))) = x) s2 (h27808 x x))
  have s4:=(t (fun q => ((x◇(x◇x))◇((y◇(x◇q))◇(x◇y))) = x) s3 (h26999 (x◇(x◇x)) x))
  have s5:=(t (fun q => ((x◇(x◇x))◇(q◇(x◇y))) = x) s4 (h26999 y x))
  exact s5
 have h28365 (x y : G):((x◇(y◇(x◇y)))◇(x◇((x◇((y◇(x◇y))◇(x◇x)))◇(y◇(x◇y))))) = ((x◇((y◇(x◇y))◇(x◇x)))◇(y◇(x◇y))):=by
  have s0:=h10589 x y
  have s1:=(t (fun q => ((x◇(y◇(x◇y)))◇(x◇q)) = ((x◇((y◇(x◇y))◇(x◇x)))◇(y◇(x◇y)))) s0 (h26999 ((x◇((y◇(x◇y))◇(x◇x)))◇(y◇(x◇y))) x))
  exact s1
 have h28633 (x y : G):((x◇(y◇x))◇(y◇y)) = (y◇y):=by
  have s0:=h5305 x y
  have s1:=(t (fun q => (((q◇(y◇x))◇(y◇y))◇(y◇(y◇(y◇y)))) = (y◇y)) s0 (h26999 x y))
  have s2:=(t (fun q => q = (y◇y)) s1 (h26999 ((x◇(y◇x))◇(y◇y)) y))
  exact s2
 have h28764 (x y : G):(x◇(x◇(x◇x))) = (y◇(y◇(y◇y))):=by
  have s0:=h4496 x x y
  have s1:=(t (fun q => (q◇((x◇(y◇(y◇(y◇y))))◇((y◇y)◇x))) = (y◇(y◇(y◇y)))) s0 (h26999 ((x◇((x◇(y◇(y◇(y◇y))))◇((y◇y)◇x)))◇((y◇y)◇x)) y))
  have s2:=(t (fun q => (((x◇(q◇((y◇y)◇x)))◇((y◇y)◇x))◇((x◇(y◇(y◇(y◇y))))◇((y◇y)◇x))) = (y◇(y◇(y◇y)))) s1 (h26999 x y))
  have s3:=(t (fun q => (((x◇(x◇((y◇y)◇x)))◇((y◇y)◇x))◇(q◇((y◇y)◇x))) = (y◇(y◇(y◇y)))) s2 (h26999 x y))
  have s4:=(t (fun q => q = (y◇(y◇(y◇y)))) s3 (h27036 x x (y◇y)))
  exact s4
 have h28981 (x y : G):((x◇(x◇(x◇x)))◇((y◇(x◇(y◇x)))◇(y◇y))) = (x◇(y◇x)):=by
  have s0:=h11730 y x
  have s1:=(t (fun q => (q◇((y◇(x◇(y◇x)))◇(y◇y))) = (x◇(y◇x))) s0 (h27036 y x y))
  exact s1
 have h29988 (x y : G):((x◇(y◇(x◇y)))◇(x◇x)) = x:=by
  have s0:=h28365 x y
  have s1:=(t (fun q => ((x◇(y◇(x◇y)))◇(x◇((x◇q)◇(y◇(x◇y))))) = ((x◇((y◇(x◇y))◇(x◇x)))◇(y◇(x◇y)))) s0 (h28633 y x))
  have s2:=(t (fun q => ((x◇(y◇(x◇y)))◇(x◇q)) = ((x◇((y◇(x◇y))◇(x◇x)))◇(y◇(x◇y)))) s1 (h27827 x y))
  have s3:=(t (fun q => ((x◇(y◇(x◇y)))◇(x◇x)) = ((x◇q)◇(y◇(x◇y)))) s2 (h28633 y x))
  have s4:=(t (fun q => ((x◇(y◇(x◇y)))◇(x◇x)) = q) s3 (h27827 x y))
  exact s4
 have bridge (a b : G) :
   ((a◇(a◇(a◇a)))◇b) = a◇(b◇a) := by
  have hb : (b◇(a◇(b◇a)))◇(b◇b) = b :=
   h29988 b a
  have eb := congrArg
   (fun q : G => (a◇(a◇(a◇a)))◇q) hb.symm
  exact Eq.trans eb (h28981 a b)
 intro x y z
 have e1 := (bridge x y).symm
 have e2 := congrArg (fun q : G => q◇y) (h28764 x z)
 have e3 := congrArg
  (fun q : G => (z◇(z◇(z◇z)))◇q)
  (h26999 y z).symm
 exact Eq.trans e1 (Eq.trans e2 (Eq.trans e3 (h5103 z y).symm))

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_19023_to_57632 : ∀ (G : Type) [Magma G], EquationLHS G → EquationRHS G := submission
#print axioms certificate_19023_to_57632
