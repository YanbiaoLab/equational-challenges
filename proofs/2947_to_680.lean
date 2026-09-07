-- Equation2947 → Equation680
-- Recorded verdict: false
-- Premise: x = ((y ◇ (y ◇ y)) ◇ x) ◇ y
-- Conclusion: x = y ◇ (x ◇ ((y ◇ y) ◇ y))
-- Original submission SHA-256: a58b3ba9693daa2800efcc068aab43bc0e3dc9ce5f3344a3c1fcf40748f58a6f
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x = ((y ◇ (y ◇ y)) ◇ x) ◇ y
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x = y ◇ (x ◇ ((y ◇ y) ◇ y))
abbrev Goal : Prop := ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G
end

-- Original submission body
                   

set_option maxRecDepth 10000

namespace submission

inductive CM where
  | e : CM
  | p : CM → CM → CM
deriving DecidableEq

namespace CM

def sz : CM → Nat
  | e => 0
  | p a b => sz a + sz b + 1

def tri (a : CM) : CM := p a (p a a)

def lhs0 (a x : CM) : CM := p (p (tri a) x) a

def lhs1 (a : CM) : CM := p (p (tri a) (tri a)) (tri a)

def get0a : CM → CM
  | p _ a => a
  | _ => e

def get0x : CM → CM
  | p (p _ x) _ => x
  | _ => e

def get1a : CM → CM
  | p _ (p a _) => a
  | _ => e

def root (t : CM) : CM :=
  let a0 := get0a t
  let x0 := get0x t
  if t = lhs0 a0 x0 then
    x0
  else
    let a1 := get1a t
    if t = lhs1 a1 then a1 else t

def op (a b : CM) : CM := root (p a b)

instance instMagma : Magma CM where
  op := op

theorem lhs1_ne_lhs0_tri (a : CM) :
    lhs1 a = lhs0 (tri a) (tri a) → False := by
  intro h
  have hs := congrArg sz h
  simp [lhs0, lhs1, tri, sz] at hs
  omega

theorem root_lhs0 (a x : CM) : root (lhs0 a x) = x := by
  change
    (if lhs0 a x = lhs0 a x then x
      else if lhs0 a x = lhs1 (get1a (lhs0 a x))
        then get1a (lhs0 a x) else lhs0 a x) = x
  rw [if_pos rfl]

theorem root_lhs1 (a : CM) : root (lhs1 a) = a := by
  change
    (if lhs1 a = lhs0 (tri a) (tri a) then tri a
      else if lhs1 a = lhs1 a then a else lhs1 a) = a
  rw [if_neg (lhs1_ne_lhs0_tri a), if_pos rfl]

theorem root_eq_self {t : CM}
    (h0 : t = lhs0 (get0a t) (get0x t) → False)
    (h1 : t = lhs1 (get1a t) → False) :
    root t = t := by
  unfold root
  rw [if_neg h0, if_neg h1]

theorem op_rule0 (a x : CM) : op (p (tri a) x) a = x := by
  exact root_lhs0 a x

theorem op_rule1 (a : CM) :
    op (p (tri a) (tri a)) (tri a) = a := by
  exact root_lhs1 a

theorem no_yy_lhs0 (y a x : CM) :
    p y y = lhs0 a x → False := by
  intro h
  have hleft : y = p (tri a) x := (CM.p.inj h).1
  have hright : y = a := (CM.p.inj h).2
  have hself : a = p (tri a) x := hright.symm.trans hleft
  have hs := congrArg sz hself
  simp [tri, sz] at hs
  omega

theorem no_yy_lhs1 (y a : CM) : p y y = lhs1 a → False := by
  intro h
  have hleft : y = p (tri a) (tri a) := (CM.p.inj h).1
  have hright : y = tri a := (CM.p.inj h).2
  have hself : tri a = p (tri a) (tri a) :=
    hright.symm.trans hleft
  have hs := congrArg sz hself
  simp [sz] at hs
  omega

theorem op_yy_raw (y : CM) : op y y = p y y := by
  unfold op
  apply root_eq_self
  · exact no_yy_lhs0 y _ _
  · exact no_yy_lhs1 y _

theorem no_y_yy_lhs0 (y a x : CM) :
    p y (p y y) = lhs0 a x → False := by
  intro h
  have hleft : y = p (tri a) x := (CM.p.inj h).1
  have hright : p y y = a := (CM.p.inj h).2
  have hlarge : y = p (tri (p y y)) x :=
    hleft.trans (congrArg (fun q => p (tri q) x) hright).symm
  have hs := congrArg sz hlarge
  simp [tri, sz] at hs
  omega

theorem no_y_yy_lhs1 (y a : CM) :
    p y (p y y) = lhs1 a → False := by
  intro h
  have hright : p y y = tri a := (CM.p.inj h).2
  have hy : y = a := (CM.p.inj hright).1
  have hself : y = p y y := by
    calc
      y = p a a := (CM.p.inj hright).2
      _ = p y y := by rw [hy]
  have hs := congrArg sz hself
  simp [sz] at hs
  omega

theorem op_y_yy_raw (y : CM) : op y (p y y) = tri y := by
  change root (p y (p y y)) = p y (p y y)
  apply root_eq_self
  · exact no_y_yy_lhs0 y _ _
  · exact no_y_yy_lhs1 y _

theorem mid_ne_lhs1 (x y a : CM) :
    p (tri y) x = lhs1 a → False := by
  intro h
  have hleft : tri y = p (tri a) (tri a) := (CM.p.inj h).1
  have hy : y = tri a := (CM.p.inj hleft).1
  have htail : p y y = tri a := (CM.p.inj hleft).2
  have hself : p y y = y := htail.trans hy.symm
  have hs := congrArg sz hself
  simp [sz] at hs
  omega

theorem source_holds (x y : CM) :
    x = op (op (op y (op y y)) x) y := by
  rw [op_yy_raw, op_y_yy_raw]
  by_cases h : p (tri y) x = lhs0 x (p y y)
  · have hleft : tri y = p (tri x) (p y y) := (CM.p.inj h).1
    have hy : y = tri x := (CM.p.inj hleft).1
    have hmid : op (tri y) x = p y y := by
      unfold op
      rw [h]
      exact root_lhs0 x (p y y)
    rw [hmid, hy]
    exact (op_rule1 x).symm
  · have hmid : op (tri y) x = p (tri y) x := by
      have hn1 :
          p (tri y) x = lhs1 (get1a (p (tri y) x)) → False :=
        mid_ne_lhs1 x y _
      exact root_eq_self h hn1
    rw [hmid]
    exact (op_rule0 y x).symm

end CM

end submission

open submission

def submission : Goal := by
  refine ⟨CM, CM.instMagma, ?_, ?_⟩
  · intro x y
    exact CM.source_holds x y
  · intro target
    have bad := target CM.e CM.e
    change
      CM.e =
        CM.p CM.e
          (CM.p CM.e (CM.p (CM.p CM.e CM.e) CM.e)) at bad
    exact CM.noConfusion bad

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_2947_to_680 : ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G := submission
#print axioms certificate_2947_to_680
