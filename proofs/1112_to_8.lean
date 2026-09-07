-- Equation1112 → Equation8
-- Recorded verdict: false
-- Premise: x = y ◇ ((y ◇ (x ◇ y)) ◇ x)
-- Conclusion: x = x ◇ (x ◇ x)
-- Original submission SHA-256: cc2293ce6f373c536478fb6e8b3b7a55ffe20b735277a721b6e9412b009f2dcf
-- Aurora-accepted correction SHA-256: 5abbaa43bdfd71717e8ce6cf773180d095447e038f6631d87e9614bacf042bd1
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x = y ◇ ((y ◇ (x ◇ y)) ◇ x)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G), x = x ◇ (x ◇ x)
abbrev Goal : Prop := ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G
end

-- Aurora-accepted corrected submission body
                   
                     
set_option maxHeartbeats 0
namespace submission
open Finset
structure P where
 R:Nat→Nat→Nat→Prop
 f:∀{x y z w},R x y z→R x y w→z=w
 q:∀{x y z u v},R x y z→R y z u→R u x v→R y v x
 k:∀{x y z},R x x y→R x y z→R x z x→y=z
 r:∀{x y z u},R x x y→R x y z→R x z u→R x u z
 s:Finset Nat
 m1:∀{x y z},R x y z→x∈s
 m2:∀{x y z},R x y z→y∈s
 m3:∀{x y z},R x y z→z∈s
namespace P
variable(p:P)(a b c:Nat)
inductive N:Nat→Nat→Nat→Prop
| i{x y z}:p.R x y z→N x y z
| n:N a b c
| d{x u}:p.R b x u→p.R x u a→N x c b
| e{u}:p.R a a u→p.R a u b→N a c b
theorem funN(h:∀z,¬p.R a b z)(hc:c∉p.s)(ca:c≠a)(cb:c≠b):
 ∀{x y z w},N p a b c x y z→N p a b c x y w→z=w:=by
 intro x y z w e k;cases e<;>cases k
 all_goals try exact p.f (by assumption) (by assumption)
 all_goals try {exfalso;exact h _ (by assumption)}
 all_goals try {exfalso;exact hc (p.m2 (by assumption))}
 all_goals try {exfalso;exact hc (p.m3 (by assumption))}
 all_goals try contradiction
 all_goals rfl
theorem qN(h:∀z,¬p.R a b z)(hc:c∉p.s)(ca:c≠a)(cb:c≠b):
 ∀{x y z u v},N p a b c x y z→N p a b c y z u→N p a b c u x v→N p a b c y v x:=by
 intro x y z u v e1 e2 e3;cases e1<;>cases e2<;>cases e3
 all_goals try exact N.i (p.q (by assumption) (by assumption) (by assumption))
 all_goals try {exfalso;exact h _ (by assumption)}
 all_goals try {exfalso;exact hc (p.m1 (by assumption))}
 all_goals try {exfalso;exact hc (p.m2 (by assumption))}
 all_goals try {exfalso;exact hc (p.m3 (by assumption))}
 all_goals try contradiction
 all_goals try exact N.n
 all_goals try exact N.d (by assumption) (by assumption)
 all_goals try exact N.e (by assumption) (by assumption)
 all_goals try exact N.i (p.r (by assumption) (by assumption) (by assumption))
 all_goals simp_all
theorem kN(h:∀z,¬p.R a b z)(hc:c∉p.s)(ca:c≠a)(cb:c≠b):
 ∀{x y z},N p a b c x x y→N p a b c x y z→N p a b c x z x→y=z:=by
 intro x y z e1 e2 e3;cases e1<;>cases e2<;>cases e3
 all_goals try exact p.k (by assumption) (by assumption) (by assumption)
 all_goals try {exfalso;exact h _ (by assumption)}
 all_goals try {exfalso;exact hc (p.m1 (by assumption))}
 all_goals try {exfalso;exact hc (p.m2 (by assumption))}
 all_goals try {exfalso;exact hc (p.m3 (by assumption))}
 all_goals try contradiction
 all_goals try rfl
 all_goals simp_all
theorem rN(h:∀z,¬p.R a b z)(hc:c∉p.s)(ca:c≠a)(cb:c≠b):
 ∀{x y z u},N p a b c x x y→N p a b c x y z→N p a b c x z u→N p a b c x u z:=by
 intro x y z u e1 e2 e3;cases e1<;>cases e2<;>cases e3
 all_goals try exact N.i (p.r (by assumption) (by assumption) (by assumption))
 all_goals try {exfalso;exact h _ (by assumption)}
 all_goals try {exfalso;exact hc (p.m1 (by assumption))}
 all_goals try {exfalso;exact hc (p.m2 (by assumption))}
 all_goals try {exfalso;exact hc (p.m3 (by assumption))}
 all_goals try contradiction
 all_goals try exact N.n
 all_goals try exact N.d (by assumption) (by assumption)
 all_goals try exact N.e (by assumption) (by assumption)
 all_goals simp_all
def next(h:∀z,¬p.R a b z)(hc:c∉p.s)(ca:c≠a)(cb:c≠b):P where
 R:=N p a b c
 f:=funN p a b c h hc ca cb
 q:=qN p a b c h hc ca cb
 k:=kN p a b c h hc ca cb
 r:=rN p a b c h hc ca cb
 s:=p.s∪{a,b,c}
 m1:=by intro x y z e;cases e with|i h=>simp[p.m1 h]|n=>simp|d h _=>simp[p.m2 h]|e=>simp
 m2:=by intro x y z e;cases e with|i h=>simp[p.m2 h]|n=>simp|d=>simp|e=>simp
 m3:=by intro x y z e;cases e with|i h=>simp[p.m3 h]|n=>simp|d=>simp|e=>simp
def fresh:Nat:=max (p.s.sup id) (max a b)+1
theorem fs:fresh p a b∉p.s:=by intro h;have e:=p.s.le_sup (f:=id) h;dsimp[fresh]at e;omega
theorem fa:fresh p a b≠a:=by unfold fresh;omega
theorem fb:fresh p a b≠b:=by unfold fresh;omega
open scoped Classical
noncomputable def add:P:=if h:∃z,p.R a b z then p else next p a b (fresh p a b)
 (by simpa using h) (fs p a b) (fa p a b) (fb p a b)
theorem ah:∃z,(add p a b).R a b z:=by
 unfold add;split
 case isTrue h=>exact h
 case isFalse h=>exact⟨_,N.n⟩
theorem ao{x y z:Nat}:p.R x y z→(add p a b).R x y z:=by
 intro e;unfold add;split
 case isTrue=>exact e
 case isFalse=>exact N.i e
noncomputable def seq:P→Nat→P
| p,0=>p
| p,n+1=>add (seq p n) n.unpair.1 n.unpair.2
theorem mo1(p:P){i x y z}:(seq p i).R x y z→(seq p (i+1)).R x y z:=by
 change _→(add (seq p i) i.unpair.1 i.unpair.2).R x y z
 intro h;exact ao (seq p i) i.unpair.1 i.unpair.2 h
theorem mo(p:P){i j x y z}(ij:i≤j):(seq p i).R x y z→(seq p j).R x y z:=by
 intro h;induction ij with|refl=>exact h|@step j _ ih=>exact mo1 p ih
theorem st(p:P)(i:Nat):∃z:Nat,(seq p (i+1)).R i.unpair.1 i.unpair.2 z:=ah ..
def comp(p:P)(x y z:Nat):Prop:=∃i,(seq p i).R x y z
theorem ct(x y):∃z,comp p x y z:=by obtain⟨z,h⟩:=st p (Nat.pair x y);exact⟨z,_,by simpa using h⟩
theorem cf{x y z w}:comp p x y z→comp p x y w→z=w:=by
 rintro⟨i,h⟩⟨j,k⟩;let n:=max i j
 exact (seq p n).f (mo p (Nat.le_max_left _ _) h) (mo p (Nat.le_max_right _ _) k)
theorem cb{x y z}:p.R x y z→comp p x y z:=fun h=>⟨0,h⟩
theorem cq{x y z u v}:comp p x y z→comp p y z u→comp p u x v→comp p y v x:=by
 rintro⟨i,h⟩⟨j,k⟩⟨l,m⟩;let n:=max i (max j l)
 exact⟨n,(seq p n).q (mo p (Nat.le_max_left _ _) h)
  (mo p (le_trans (Nat.le_max_left _ _) (Nat.le_max_right _ _)) k)
  (mo p (le_trans (Nat.le_max_right _ _) (Nat.le_max_right _ _)) m)⟩
noncomputable def op(x y:Nat):Nat:=(ct p x y).choose
theorem om(x y):comp p x y (op p x y):=(ct p x y).choose_spec
@[implicit_reducible]noncomputable def mag:Magma Nat:=⟨op p⟩
theorem law:letI:=mag p;EquationLHS Nat:=by
 intro x y
 exact cf p (cq p (om p x y) (om p y (op p x y))
  (om p (op p y (op p x y)) x)) (om p y (op p (op p y (op p x y)) x))
end P
def base:P where
 R:=fun x y z=>x=1∧(y=1∨y=2)∧z=2
 f:=by rintro x y z w ⟨_,_,rfl⟩⟨_,_,rfl⟩;rfl
 q:=by rintro x y z u v ⟨_,_,rfl⟩⟨h,_,_⟩ _;omega
 k:=by rintro x y z ⟨_,_,rfl⟩ _ ⟨_,_,h⟩;omega
 r:=by
  rintro x y z u ⟨hx,hy,hyy⟩⟨hx',hy',hz⟩⟨hx'',hz',hu⟩
  subst x;subst y;subst z;subst u
  exact⟨rfl,.inr rfl,rfl⟩
 s:={1,2}
 m1:=by rintro x y z ⟨rfl,_,_⟩;simp
 m2:=by rintro x y z ⟨_,h,_⟩;rcases h with rfl|rfl<;>simp
 m3:=by rintro x y z ⟨_,_,rfl⟩;simp
noncomputable instance:Magma Nat:=P.mag base
theorem source:EquationLHS Nat:=P.law base
theorem counter:¬EquationRHS Nat:=by
 have h11:P.op base 1 1=2:=P.cf base (P.om base 1 1) (P.cb base ⟨rfl,.inl rfl,rfl⟩)
 have h12:P.op base 1 2=2:=P.cf base (P.om base 1 2) (P.cb base ⟨rfl,.inr rfl,rfl⟩)
 intro h;have e:=h 1
 change 1=P.op base 1 (P.op base 1 1) at e
 simp only[h11,h12]at e
 omega
def certificate : Goal := ⟨Nat, inferInstance, source, counter⟩
end submission
def submission : Goal := submission.certificate

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_1112_to_8 : ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G := submission
#print axioms certificate_1112_to_8
