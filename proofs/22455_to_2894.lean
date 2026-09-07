-- Equation22455 → Equation2894
-- Recorded verdict: false
-- Premise: x = (y ◇ (x ◇ x)) ◇ ((y ◇ z) ◇ y)
-- Conclusion: x = ((x ◇ (y ◇ z)) ◇ w) ◇ x
-- Original submission SHA-256: cf9fe18aacef222271509f9e24273e778bb0cf5a00541bec8e0cabf37cf247dd
-- Generator: equational-challenges standalone v1
-- All project definitions are embedded in this file.
import Mathlib.Tactic.Lemma

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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (y ◇ (x ◇ x)) ◇ ((y ◇ z) ◇ y)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G) (w : G), x = ((x ◇ (y ◇ z)) ◇ w) ◇ x
abbrev Goal : Prop := ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G
end

-- Original submission body
-- stage:stage0_generalized_infinite_source_family
                   
              

set_option maxRecDepth 10000

namespace submission

inductive CM where
  | e : CM
  | k : CM → CM
  | p : CM → CM → CM

namespace CM

def cmDecEq : (a b : CM) → Decidable (a = b)
  | CM.e, CM.e => isTrue rfl
  | CM.e, CM.k _ => isFalse (fun h => CM.noConfusion h)
  | CM.e, CM.p _ _ => isFalse (fun h => CM.noConfusion h)
  | CM.k _, CM.e => isFalse (fun h => CM.noConfusion h)
  | CM.p _ _, CM.e => isFalse (fun h => CM.noConfusion h)
  | CM.k a, CM.k b =>
      match cmDecEq a b with
      | isTrue h => isTrue (congrArg CM.k h)
      | isFalse h => isFalse (fun hab => h (CM.k.inj hab))
  | CM.k _, CM.p _ _ => isFalse (fun h => CM.noConfusion h)
  | CM.p _ _, CM.k _ => isFalse (fun h => CM.noConfusion h)
  | CM.p a b, CM.p c d =>
      match cmDecEq a c with
      | isFalse h => isFalse (fun hab => h (CM.p.inj hab).1)
      | isTrue hac =>
          match cmDecEq b d with
          | isFalse h => isFalse (fun hab => h (CM.p.inj hab).2)
          | isTrue hbd => isTrue (by cases hac; cases hbd; rfl)

instance instDecidableEq : DecidableEq CM := cmDecEq

def sz : CM → Nat
  | CM.e => 0
  | CM.k x => sz x + 1
  | CM.p x y => (sz x + 1) + (sz y + 1)

lemma sz_lt_p_left (a b : CM) : sz a < sz (CM.p a b) := by
  change sz a < (sz a + 1) + (sz b + 1)
  exact Nat.lt_of_lt_of_le (Nat.lt_succ_self (sz a))
    (Nat.le_add_right (sz a + 1) (sz b + 1))

lemma sz_lt_p_right (a b : CM) : sz b < sz (CM.p a b) := by
  change sz b < (sz a + 1) + (sz b + 1)
  exact Nat.lt_of_lt_of_le (Nat.lt_succ_self (sz b))
    (Nat.le_add_left (sz b + 1) (sz a + 1))

structure Pat1 where
  y : CM
  x : CM
  z : CM

structure Pat2 where
  a : CM
  b : CM
  c : CM

def left1 (m : Pat1) : CM := CM.p m.y (CM.p m.x m.x)
def right1 (m : Pat1) : CM := CM.p (CM.p m.y m.z) m.y
def left2 (m : Pat2) : CM := CM.p (CM.p m.a (CM.p m.b m.b)) (CM.p m.c m.c)
def right2 (m : Pat2) : CM := CM.p m.b (CM.p m.a (CM.p m.b m.b))

abbrev No1 (a b : CM) := (m : Pat1) → a = left1 m → b = right1 m → False
abbrev No2 (a b : CM) := (m : Pat2) → a = left2 m → b = right2 m → False

def get1Y : CM → CM
  | CM.p y _ => y
  | _ => CM.e

def get1X : CM → CM
  | CM.p _ (CM.p x _) => x
  | _ => CM.e

def get1Z : CM → CM
  | CM.p (CM.p _ z) _ => z
  | _ => CM.e

def get2A : CM → CM
  | CM.p (CM.p a _) _ => a
  | _ => CM.e

def get2B : CM → CM
  | CM.p (CM.p _ (CM.p b _)) _ => b
  | _ => CM.e

def get2C : CM → CM
  | CM.p _ (CM.p c _) => c
  | _ => CM.e

inductive Detect1 (a b : CM) where
  | yes (m : Pat1) (ha : a = left1 m) (hb : b = right1 m)
  | no (h : No1 a b)

inductive Detect2 (a b : CM) where
  | yes (m : Pat2) (ha : a = left2 m) (hb : b = right2 m)
  | no (h : No2 a b)

def detect1 (a b : CM) : Detect1 a b :=
  let m : Pat1 := ⟨get1Y a, get1X a, get1Z b⟩
  match cmDecEq a (left1 m) with
  | isFalse ha => .no (fun q hqa _ => by cases hqa; exact ha rfl)
  | isTrue ha =>
      match cmDecEq b (right1 m) with
      | isFalse hb => .no (fun q hqa hqb => by
          cases hqa
          cases hqb
          exact hb rfl)
      | isTrue hb => .yes m ha hb

def detect2 (a b : CM) : Detect2 a b :=
  let m : Pat2 := ⟨get2A a, get2B a, get2C a⟩
  match cmDecEq a (left2 m) with
  | isFalse ha => .no (fun q hqa _ => by cases hqa; exact ha rfl)
  | isTrue ha =>
      match cmDecEq b (right2 m) with
      | isFalse hb => .no (fun q hqa hqb => by
          cases hqa
          cases hqb
          exact hb rfl)
      | isTrue hb => .yes m ha hb

inductive View (a b : CM) where
  | r1 (m : Pat1) (ha : a = left1 m) (hb : b = right1 m)
  | r2 (m : Pat2) (ha : a = left2 m) (hb : b = right2 m)
  | raw (h1 : No1 a b) (h2 : No2 a b)

def view (a b : CM) : View a b :=
  match detect1 a b with
  | .yes m ha hb => .r1 m ha hb
  | .no h1 =>
      match detect2 a b with
      | .yes m ha hb => .r2 m ha hb
      | .no h2 => .raw h1 h2

def op (a b : CM) : CM :=
  match view a b with
  | .r1 m _ _ => m.x
  | .r2 m _ _ => m.c
  | .raw _ _ => CM.p a b

instance instMagma : Magma CM where
  op := op

lemma pat_disjoint (m : Pat1) (n : Pat2)
    (hl : left1 m = left2 n) (hr : right1 m = right2 n) : False := by
  have hy : m.y = CM.p n.a (CM.p n.b n.b) := (CM.p.inj hl).1
  have hb : CM.p m.y m.z = n.b := (CM.p.inj hr).1
  have hby : sz n.b < sz m.y := by
    have h1 : sz n.b < sz (CM.p n.b n.b) := sz_lt_p_left n.b n.b
    have h2 : sz (CM.p n.b n.b) < sz (CM.p n.a (CM.p n.b n.b)) :=
      sz_lt_p_right n.a (CM.p n.b n.b)
    exact Nat.lt_of_lt_of_eq (Nat.lt_trans h1 h2) (congrArg sz hy).symm
  have hyb : sz m.y < sz n.b :=
    Nat.lt_of_lt_of_eq (sz_lt_p_left m.y m.z) (congrArg sz hb)
  exact (Nat.lt_irrefl (sz n.b)) (Nat.lt_trans hby hyb)

lemma op_rule1 (m : Pat1) : op (left1 m) (right1 m) = m.x := by
  unfold op view
  cases hd : detect1 (left1 m) (right1 m) with
  | yes q hq _ =>
      change q.x = m.x
      have hp : CM.p m.x m.x = CM.p q.x q.x := (CM.p.inj hq).2
      exact (CM.p.inj hp).1.symm
  | no hn => exact (hn m rfl rfl).elim

lemma op_rule2 (m : Pat2) : op (left2 m) (right2 m) = m.c := by
  unfold op view
  cases hd1 : detect1 (left2 m) (right2 m) with
  | yes q hq1 hq2 => exact (pat_disjoint q m hq1.symm hq2.symm).elim
  | no _ =>
      cases hd2 : detect2 (left2 m) (right2 m) with
      | yes q hq _ =>
          change q.c = m.c
          have hp : CM.p m.c m.c = CM.p q.c q.c := (CM.p.inj hq).2
          exact (CM.p.inj hp).1.symm
      | no hn => exact (hn m rfl rfl).elim

lemma op_raw {a b : CM} (h1 : No1 a b) (h2 : No2 a b) : op a b = CM.p a b := by
  unfold op view
  cases hd1 : detect1 a b with
  | yes m ha hb => exact (h1 m ha hb).elim
  | no _ =>
      cases hd2 : detect2 a b with
      | yes m ha hb => exact (h2 m ha hb).elim
      | no _ => rfl

lemma no1_same (t : CM) : No1 t t := by
  intro m hl hr
  have h : left1 m = right1 m := hl.symm.trans hr
  have hy : m.y = CM.p m.y m.z := (CM.p.inj h).1
  exact (Nat.ne_of_lt (sz_lt_p_left m.y m.z)) (congrArg sz hy)

lemma no2_same (t : CM) : No2 t t := by
  intro m hl hr
  have h : left2 m = right2 m := hl.symm.trans hr
  have hb : CM.p m.a (CM.p m.b m.b) = m.b := (CM.p.inj h).1
  have hlt : sz m.b < sz (CM.p m.a (CM.p m.b m.b)) :=
    Nat.lt_trans (sz_lt_p_left m.b m.b)
      (sz_lt_p_right m.a (CM.p m.b m.b))
  exact (Nat.ne_of_lt hlt) (congrArg sz hb).symm

lemma no1_encode (y x : CM) : No1 y (CM.p x x) := by
  intro m _ hr
  have hx1 : x = CM.p m.y m.z := (CM.p.inj hr).1
  have hx2 : x = m.y := (CM.p.inj hr).2
  have hy : m.y = CM.p m.y m.z := hx2.symm.trans hx1
  exact (Nat.ne_of_lt (sz_lt_p_left m.y m.z)) (congrArg sz hy)

lemma no2_encode (y x : CM) : No2 y (CM.p x x) := by
  intro m _ hr
  have hx1 : x = m.b := (CM.p.inj hr).1
  have hx2 : x = CM.p m.a (CM.p m.b m.b) := (CM.p.inj hr).2
  have hb : m.b = CM.p m.a (CM.p m.b m.b) := hx1.symm.trans hx2
  have hlt : sz m.b < sz (CM.p m.a (CM.p m.b m.b)) :=
    Nat.lt_trans (sz_lt_p_left m.b m.b)
      (sz_lt_p_right m.a (CM.p m.b m.b))
  exact (Nat.ne_of_lt hlt) (congrArg sz hb)

lemma no1_after1 (m : Pat1) : No1 m.x (left1 m) := by
  intro q hl hr
  have hright : CM.p m.x m.x = q.y := (CM.p.inj hr).2
  have hqx : sz q.y < sz m.x :=
    Nat.lt_of_lt_of_eq (sz_lt_p_left q.y (CM.p q.x q.x)) (congrArg sz hl).symm
  have hxq : sz m.x < sz q.y :=
    Nat.lt_of_lt_of_eq (sz_lt_p_left m.x m.x) (congrArg sz hright)
  exact (Nat.lt_irrefl (sz q.y)) (Nat.lt_trans hqx hxq)

lemma no2_after1 (m : Pat1) : No2 m.x (left1 m) := by
  intro q hl hr
  have hxq : m.x = q.a := (CM.p.inj (CM.p.inj hr).2).1
  have hqa : sz q.a < sz m.x :=
    Nat.lt_of_lt_of_eq
      (Nat.lt_trans (sz_lt_p_left q.a (CM.p q.b q.b))
        (sz_lt_p_left (CM.p q.a (CM.p q.b q.b)) (CM.p q.c q.c)))
      (congrArg sz hl).symm
  exact (Nat.ne_of_lt hqa) (congrArg sz hxq).symm

lemma no1_after2 (m : Pat2) : No1 m.c (left2 m) := by
  intro q hl hr
  have hcy : CM.p m.c m.c = q.y := (CM.p.inj hr).2
  have hyc : sz q.y < sz m.c :=
    Nat.lt_of_lt_of_eq (sz_lt_p_left q.y (CM.p q.x q.x)) (congrArg sz hl).symm
  have hcy' : sz m.c < sz q.y :=
    Nat.lt_of_lt_of_eq (sz_lt_p_left m.c m.c) (congrArg sz hcy)
  exact (Nat.lt_irrefl (sz q.y)) (Nat.lt_trans hyc hcy')

lemma no2_after2 (m : Pat2) : No2 m.c (left2 m) := by
  intro q hl hr
  have hcq : m.c = q.a := (CM.p.inj (CM.p.inj hr).2).1
  have hqa : sz q.a < sz m.c :=
    Nat.lt_of_lt_of_eq
      (Nat.lt_trans (sz_lt_p_left q.a (CM.p q.b q.b))
        (sz_lt_p_left (CM.p q.a (CM.p q.b q.b)) (CM.p q.c q.c)))
      (congrArg sz hl).symm
  exact (Nat.ne_of_lt hqa) (congrArg sz hcq).symm

lemma no1_after_raw (y z : CM) : No1 (CM.p y z) y := by
  intro m hl hr
  have hy : y = m.y := (CM.p.inj hl).1
  have hself : m.y = right1 m := hy.symm.trans hr
  have hlt : sz m.y < sz (right1 m) := by
    unfold right1
    exact sz_lt_p_right (CM.p m.y m.z) m.y
  exact (Nat.ne_of_lt hlt) (congrArg sz hself)

lemma no2_after_raw (y z : CM) : No2 (CM.p y z) y := by
  intro m hl hr
  have hy : y = CM.p m.a (CM.p m.b m.b) := (CM.p.inj hl).1
  have hself : CM.p m.a (CM.p m.b m.b) =
      CM.p m.b (CM.p m.a (CM.p m.b m.b)) := hy.symm.trans hr
  have hlt : sz (CM.p m.a (CM.p m.b m.b)) <
      sz (CM.p m.b (CM.p m.a (CM.p m.b m.b))) :=
    sz_lt_p_right m.b (CM.p m.a (CM.p m.b m.b))
  exact (Nat.ne_of_lt hlt) (congrArg sz hself)

lemma square (x : CM) : op x x = CM.p x x := op_raw (no1_same x) (no2_same x)

lemma encode (y x : CM) : op y (CM.p x x) = CM.p y (CM.p x x) :=
  op_raw (no1_encode y x) (no2_encode y x)

lemma return_right (y z : CM) : op (op y z) y = CM.p (op y z) y := by
  cases hv : view y z with
  | r1 m ha hb =>
      have hop : op y z = m.x := by unfold op; rw [hv]
      rw [hop, ha]
      exact op_raw (no1_after1 m) (no2_after1 m)
  | r2 m ha hb =>
      have hop : op y z = m.c := by unfold op; rw [hv]
      rw [hop, ha]
      exact op_raw (no1_after2 m) (no2_after2 m)
  | raw h1 h2 =>
      have hop : op y z = CM.p y z := by unfold op; rw [hv]
      rw [hop]
      exact op_raw (no1_after_raw y z) (no2_after_raw y z)

lemma source_holds (x y z : CM) :
    x = op (op y (op x x)) (op (op y z) y) := by
  rw [square x, encode y x, return_right y z]
  cases hv : view y z with
  | r1 m ha hb =>
      have hop : op y z = m.x := by unfold op; rw [hv]
      rw [hop, ha]
      exact (op_rule2 ⟨m.y, m.x, x⟩).symm
  | r2 m ha hb =>
      have hop : op y z = m.c := by unfold op; rw [hv]
      rw [hop, ha]
      exact (op_rule2 ⟨CM.p m.a (CM.p m.b m.b), m.c, x⟩).symm
  | raw h1 h2 =>
      have hop : op y z = CM.p y z := by unfold op; rw [hv]
      rw [hop]
      exact (op_rule1 ⟨y, x, z⟩).symm
end CM

end submission

open submission

namespace submission.CM

theorem d10TargetRefutation
    (target : @EquationRHS CM CM.instMagma) : False := by
  first
  | have bad := target CM.e CM.e CM.e (CM.k CM.e)
    change (CM.e : CM) = (@Magma.op CM CM.instMagma (@Magma.op CM CM.instMagma (@Magma.op CM CM.instMagma (CM.e : CM) (@Magma.op CM CM.instMagma (CM.e : CM) (CM.e : CM))) ((CM.k CM.e) : CM)) (CM.e : CM)) at bad
    exact nomatch bad
  | have bad := target CM.e CM.e (CM.k CM.e) CM.e
    change (CM.e : CM) = (@Magma.op CM CM.instMagma (@Magma.op CM CM.instMagma (@Magma.op CM CM.instMagma (CM.e : CM) (@Magma.op CM CM.instMagma (CM.e : CM) ((CM.k CM.e) : CM))) (CM.e : CM)) (CM.e : CM)) at bad
    exact nomatch bad
  | have bad := target CM.e CM.e (CM.k CM.e) (CM.k CM.e)
    change (CM.e : CM) = (@Magma.op CM CM.instMagma (@Magma.op CM CM.instMagma (@Magma.op CM CM.instMagma (CM.e : CM) (@Magma.op CM CM.instMagma (CM.e : CM) ((CM.k CM.e) : CM))) ((CM.k CM.e) : CM)) (CM.e : CM)) at bad
    exact nomatch bad
  | have bad := target CM.e (CM.k CM.e) CM.e CM.e
    change (CM.e : CM) = (@Magma.op CM CM.instMagma (@Magma.op CM CM.instMagma (@Magma.op CM CM.instMagma (CM.e : CM) (@Magma.op CM CM.instMagma ((CM.k CM.e) : CM) (CM.e : CM))) (CM.e : CM)) (CM.e : CM)) at bad
    exact nomatch bad
  | have bad := target CM.e (CM.k CM.e) CM.e (CM.k CM.e)
    change (CM.e : CM) = (@Magma.op CM CM.instMagma (@Magma.op CM CM.instMagma (@Magma.op CM CM.instMagma (CM.e : CM) (@Magma.op CM CM.instMagma ((CM.k CM.e) : CM) (CM.e : CM))) ((CM.k CM.e) : CM)) (CM.e : CM)) at bad
    exact nomatch bad
  | have bad := target CM.e (CM.k CM.e) (CM.k CM.e) CM.e
    change (CM.e : CM) = (@Magma.op CM CM.instMagma (@Magma.op CM CM.instMagma (@Magma.op CM CM.instMagma (CM.e : CM) (@Magma.op CM CM.instMagma ((CM.k CM.e) : CM) ((CM.k CM.e) : CM))) (CM.e : CM)) (CM.e : CM)) at bad
    exact nomatch bad
  | have bad := target CM.e (CM.k CM.e) (CM.k CM.e) (CM.k CM.e)
    change (CM.e : CM) = (@Magma.op CM CM.instMagma (@Magma.op CM CM.instMagma (@Magma.op CM CM.instMagma (CM.e : CM) (@Magma.op CM CM.instMagma ((CM.k CM.e) : CM) ((CM.k CM.e) : CM))) ((CM.k CM.e) : CM)) (CM.e : CM)) at bad
    exact nomatch bad
  | have bad := target (CM.k CM.e) CM.e CM.e CM.e
    change ((CM.k CM.e) : CM) = (@Magma.op CM CM.instMagma (@Magma.op CM CM.instMagma (@Magma.op CM CM.instMagma ((CM.k CM.e) : CM) (@Magma.op CM CM.instMagma (CM.e : CM) (CM.e : CM))) (CM.e : CM)) ((CM.k CM.e) : CM)) at bad
    exact nomatch bad

end submission.CM

def submission : Goal := by
  refine ⟨CM, CM.instMagma, ?_, ?_⟩
  · intro x y z
    change x = CM.op (CM.op y (CM.op x x)) (CM.op (CM.op y z) y)
    exact CM.source_holds x y z
  · intro target
    exact CM.d10TargetRefutation target

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_22455_to_2894 : ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G := submission
#print axioms certificate_22455_to_2894
