-- Equation707 → Equation1316
-- Recorded verdict: false
-- Premise: x = y ◇ (y ◇ ((x ◇ y) ◇ y))
-- Conclusion: x = y ◇ (((y ◇ x) ◇ y) ◇ y)
-- Original submission SHA-256: 344ed5af88bd5d940f5e4dd262c4e62f4b223b37234d4454fa6cabb6379c97f6
-- Aurora-accepted correction SHA-256: 33da8c811c6f343bfa2dea04b6a9971d9273509ac8faf1be16e76875e54215de
-- Generator: equational-challenges standalone v2
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x = y ◇ (y ◇ ((x ◇ y) ◇ y))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x = y ◇ (((y ◇ x) ◇ y) ◇ y)
abbrev Goal : Prop := ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G
end

-- Aurora-accepted corrected submission body
                   
                     
set_option maxHeartbeats 0
namespace submission
open Finset
structure P where
 R:Nat→Nat→Nat→Prop
 f:∀{x y z w},R x y z→R x y w→z=w
 q:∀{x y z u v},R x y z→R y u v→R z y u→R y v x
 l:∀{x x' y z},R x y z→R x' y z→x=x'
 r:∀{x y:Nat},R x y y→∀u,R u y x→R y u x
 s:Finset Nat
 m1:∀{x y z},R x y z→x∈s
 m2:∀{x y z},R x y z→y∈s
 m3:∀{x y z},R x y z→z∈s
namespace P
variable(p:P)(a b c:Nat)
inductive N:Nat→Nat→Nat→Prop
| i{ x y z}:p.R x y z→N x y z
| n:N a b c
| d{z u}:p.R z a u→p.R u a b→N a c z
theorem nf(hc:c∉p.s){x y}(h:p.R x y c):False:=hc (p.m3 h)
theorem cf(hc:c∉p.s){x z}(h:p.R x c z):False:=hc (p.m2 h)
theorem xf(hc:c∉p.s){y z}(h:p.R c y z):False:=hc (p.m1 h)
theorem chain{z w u v}(h1:p.R z a u)(h2:p.R u a b)(h3:p.R w a v)(h4:p.R v a b):z=w:=by
 have e:u=v:=p.l h2 h4
 subst v;exact p.l h1 h3
theorem qr{x v u}(hx:p.R x a a)(hv:p.R v a u)(hu:p.R u a a):p.R a v x:=by
 have e:x=u:=p.l hx hu
 subst u;exact p.r hx v hv
theorem funN(h:∀z,¬p.R a b z)(hc:c∉p.s)(ca:c≠a)(cb:c≠b):
 ∀{x y z w},N p a b c x y z→N p a b c x y w→z=w:=by
 intro x y z w h1 h2
 cases h1 <;> cases h2
 all_goals try exact p.f (by assumption) (by assumption)
 all_goals try {exfalso;exact h _ (by assumption)}
 all_goals try {exfalso;exact hc (p.m2 (by assumption))}
 all_goals try contradiction
 all_goals try rfl
 case d.d=>exact chain p a b (by assumption) (by assumption) (by assumption) (by assumption)
theorem leftN(h:∀z,¬p.R a b z)(hc:c∉p.s)(ca:c≠a)(cb:c≠b):
 ∀{x x' y z},N p a b c x y z→N p a b c x' y z→x=x':=by
 intro x x' y z h1 h2
 cases h1 <;> cases h2
 all_goals try exact p.l (by assumption) (by assumption)
 all_goals try {exfalso;exact hc (p.m3 (by assumption))}
 all_goals try {exfalso;exact hc (p.m2 (by assumption))}
 all_goals try contradiction
 all_goals rfl
theorem relN(h:∀z,¬p.R a b z)(hc:c∉p.s)(ca:c≠a)(cb:c≠b):
 ∀{x y},N p a b c x y y→∀u,N p a b c u y x→N p a b c y u x:=by
 intro x y e u k
 cases e <;> cases k
 all_goals try exact .i (p.r (by assumption) _ (by assumption))
 all_goals try {exfalso;exact hc (p.m3 (by assumption))}
 all_goals try {exfalso;exact hc (p.m2 (by assumption))}
 all_goals try {exfalso;exact hc (p.m1 (by assumption))}
 all_goals try {exfalso;exact h _ (by assumption)}
 all_goals try contradiction
 all_goals try exact .n
 all_goals try {exfalso;exact ca (chain p a b (by assumption) (by assumption) (by assumption) (by assumption))}
theorem qN(h:∀z,¬p.R a b z)(hc:c∉p.s)(ca:c≠a)(cb:c≠b):
 ∀{x y z u v},N p a b c x y z→N p a b c y u v→N p a b c z y u→N p a b c y v x:=by
 intro x y z u v e1 e2 e3
 cases e1 <;> cases e2 <;> cases e3
 case i.i.i h1 h2 h3=>exact .i (p.q h1 h2 h3)
 all_goals try {exfalso;exact nf p c hc (by assumption)}
 all_goals try {exfalso;exact cf p c hc (by assumption)}
 all_goals try {exfalso;exact xf p c hc (by assumption)}
 all_goals try contradiction
 all_goals try exact .n
 all_goals try exact N.d (by assumption) (by assumption)
 all_goals try exact N.i (qr p a (by assumption) (by assumption) (by assumption))
 all_goals simp_all
def next(h:∀z,¬p.R a b z)(hc:c∉p.s)(ca:c≠a)(cb:c≠b):P where
 R:=N p a b c
 f:=funN p a b c h hc ca cb
 q:=qN p a b c h hc ca cb
 l:=leftN p a b c h hc ca cb
 r:=relN p a b c h hc ca cb
 s:=p.s∪{a,b,c}
 m1:=by intro x y z e;cases e with|i h=>simp[p.m1 h]|n=>simp|d h _=>simp
 m2:=by intro x y z e;cases e with|i h=>simp[p.m2 h]|n=>simp|d h _=>simp
 m3:=by intro x y z e;cases e with|i h=>simp[p.m3 h]|n=>simp|d h _=>simp[p.m1 h]
theorem next_has(h:∀z,¬p.R a b z)(hc:c∉p.s)(ca:c≠a)(cb:c≠b):
 (next p a b c h hc ca cb).R a b c:=.n
theorem next_old(h:∀z,¬p.R a b z)(hc:c∉p.s)(ca:c≠a)(cb:c≠b){x y z}:
 p.R x y z→(next p a b c h hc ca cb).R x y z:=.i
def fresh:Nat:=max (p.s.sup id) (max a b)+1
theorem fresh_s:fresh p a b∉p.s:=by
 intro h
 have e:=p.s.le_sup (f:=id) h
 dsimp [fresh] at e;omega
theorem fresh_a:fresh p a b≠a:=by unfold fresh;omega
theorem fresh_b:fresh p a b≠b:=by unfold fresh;omega
open scoped Classical
noncomputable def add:P:=if h:∃z,p.R a b z then p else next p a b (fresh p a b)
 (by simpa using h) (fresh_s p a b) (fresh_a p a b) (fresh_b p a b)
theorem add_has:∃z,(add p a b).R a b z:=by
 unfold add;split
 case isTrue h=>exact h
 case isFalse h=>exact ⟨fresh p a b,next_has p a b _ (by simpa using h) (fresh_s p a b) (fresh_a p a b) (fresh_b p a b)⟩
theorem add_old{ x y z}:p.R x y z→(add p a b).R x y z:=by
 intro e;unfold add;split
 case isTrue=>exact e
 case isFalse h=>exact next_old p a b _ (by simpa using h) (fresh_s p a b) (fresh_a p a b) (fresh_b p a b) e
noncomputable def seq:P→Nat→P
| p,0=>p
| p,n+1=>add (seq p n) n.unpair.1 n.unpair.2
theorem mono1(p:P){i x y z}:(seq p i).R x y z→(seq p (i+1)).R x y z:=by
 change (seq p i).R x y z→(add (seq p i) i.unpair.1 i.unpair.2).R x y z
 intro h;exact add_old (seq p i) i.unpair.1 i.unpair.2 h
theorem mono(p:P){i j x y z}(ij:i≤j):(seq p i).R x y z→(seq p j).R x y z:=by
 intro h;induction ij with
 | refl=>exact h
 | @step j _ ih=>exact mono1 p ih
theorem step(p:P)(i:Nat):∃z:Nat,(seq p (i+1)).R i.unpair.1 i.unpair.2 z:=add_has ..
def comp(p:P)(x y z:Nat):Prop:=∃i,(seq p i).R x y z
theorem Cfun{ x y z w}:comp p x y z→comp p x y w→z=w:=by
 rintro⟨i,h⟩⟨j,k⟩
 let n:=max i j
 exact (seq p n).f (mono p (Nat.le_max_left _ _) h) (mono p (Nat.le_max_right _ _) k)
theorem Ctotal(x y):∃z,comp p x y z:=by
 obtain⟨z,h⟩:=step p (Nat.pair x y)
 exact⟨z,_,by simpa using h⟩
theorem Cbase{x y z}:p.R x y z→comp p x y z:=fun h=>⟨0,h⟩
theorem Cq{x y z u v}:comp p x y z→comp p y u v→comp p z y u→comp p y v x:=by
 rintro⟨i,h⟩⟨j,k⟩⟨l,m⟩
 let n:=max i (max j l)
 exact⟨n,(seq p n).q (mono p (Nat.le_max_left _ _) h)
  (mono p (le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)) k)
  (mono p (le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) m)⟩
noncomputable def op(x y:Nat):Nat:=(Ctotal p x y).choose
theorem op_mem(x y):comp p x y (op p x y):=(Ctotal p x y).choose_spec
@[implicit_reducible]noncomputable def mag:Magma Nat:=⟨op p⟩
theorem law:letI:=mag p;EquationLHS Nat:=by
 intro x y
 exact Cfun p (Cq p (op_mem p x y) (op_mem p y (op p (op p x y) y))
  (op_mem p (op p x y) y)) (op_mem p y (op p y (op p (op p x y) y)))
end P
def base:P where
 R:=fun x y z=>x=1∧(y=1∨y=2)∧z=1
 f:=by rintro x y z w ⟨_,_,rfl⟩⟨_,_,rfl⟩;rfl
 q:=by
  rintro x y z u v ⟨hx,hy,hz⟩⟨hyy,hu,hv⟩⟨hzz,hy',hu'⟩
  subst x;subst z;subst y;subst u;subst v
  exact⟨rfl,.inl rfl,rfl⟩
 l:=by rintro x x' y z ⟨rfl,_,_⟩⟨rfl,_,_⟩;rfl
 r:=by
  rintro x y ⟨hx,hy,hyy⟩ u ⟨hu,hy',hx'⟩
  subst x;subst y;subst u
  exact⟨rfl,.inl rfl,rfl⟩
 s:={1,2}
 m1:=by rintro x y z ⟨rfl,_,_⟩;simp
 m2:=by rintro x y z ⟨_,h,_⟩;rcases h with rfl|rfl<;>simp
 m3:=by rintro x y z ⟨_,_,rfl⟩;simp
noncomputable instance:Magma Nat:=P.mag base
theorem source:EquationLHS Nat:=P.law base
theorem counter:¬EquationRHS Nat:=by
 have h11:P.op base 1 1=1:=P.Cfun base (P.op_mem base 1 1) (P.Cbase base ⟨rfl,.inl rfl,rfl⟩)
 have h12:P.op base 1 2=1:=P.Cfun base (P.op_mem base 1 2) (P.Cbase base ⟨rfl,.inr rfl,rfl⟩)
 intro h
 have e:=h 2 1
 change 2=P.op base 1 (P.op base (P.op base (P.op base 1 2) 1) 1) at e
 simp only[h12,h11] at e
 omega
def certificate : Goal := ⟨Nat, inferInstance, source, counter⟩
end submission
def submission : Goal := submission.certificate

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_707_to_1316 : ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G := submission
#print axioms certificate_707_to_1316
