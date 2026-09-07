-- Equation680 → Equation1832
-- Recorded verdict: false
-- Premise: x = y ◇ (x ◇ ((y ◇ y) ◇ y))
-- Conclusion: x = (x ◇ (x ◇ x)) ◇ (x ◇ x)
-- Original submission SHA-256: 831fc4667733058eeda22eb02b85ad076359960d1941ae8688b36066f7f46bb5
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x = y ◇ (x ◇ ((y ◇ y) ◇ y))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G), x = (x ◇ (x ◇ x)) ◇ (x ◇ x)
abbrev Goal : Prop := ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G
end

-- Original submission body
-- stage:stage0_generalized_infinite_source_family
                   

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

def cub (a : CM) : CM := p (p a a) a

def lhs0 (a x : CM) : CM := p a (p x (cub a))

def lhs1 (a : CM) : CM := p (cub a) (p (cub a) (cub a))

def get0a : CM → CM
  | p a _ => a
  | _ => e

def get0x : CM → CM
  | p _ (p x _) => x
  | _ => e

def get1a : CM → CM
  | p (p (p a _) _) _ => a
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

theorem lhs1_ne_lhs0_cub (a : CM) :
    lhs1 a = lhs0 (cub a) (cub a) → False := by
  intro h
  have hs := congrArg sz h
  simp [lhs0, lhs1, cub, sz] at hs
  omega

theorem root_lhs0 (a x : CM) : root (lhs0 a x) = x := by
  change
    (if lhs0 a x = lhs0 a x then x
      else if lhs0 a x = lhs1 (get1a (lhs0 a x))
        then get1a (lhs0 a x) else lhs0 a x) = x
  rw [if_pos rfl]

theorem root_lhs1 (a : CM) : root (lhs1 a) = a := by
  change
    (if lhs1 a = lhs0 (cub a) (cub a) then cub a
      else if lhs1 a = lhs1 a then a else lhs1 a) = a
  rw [if_neg (lhs1_ne_lhs0_cub a), if_pos rfl]

theorem root_eq_self {t : CM}
    (h0 : t = lhs0 (get0a t) (get0x t) → False)
    (h1 : t = lhs1 (get1a t) → False) :
    root t = t := by
  unfold root
  rw [if_neg h0, if_neg h1]

theorem op_rule0 (a x : CM) : op a (p x (cub a)) = x := by
  exact root_lhs0 a x

theorem op_rule1 (a : CM) :
    op (cub a) (p (cub a) (cub a)) = a := by
  exact root_lhs1 a

theorem no_yy_lhs0 (y a x : CM) :
    p y y = lhs0 a x → False := by
  intro h
  have hleft : y = a := (CM.p.inj h).1
  have hright : y = p x (cub a) := (CM.p.inj h).2
  have hself : a = p x (cub a) := hleft.symm.trans hright
  have hs := congrArg sz hself
  simp [cub, sz] at hs
  omega

theorem no_yy_lhs1 (y a : CM) : p y y = lhs1 a → False := by
  intro h
  have hleft : y = cub a := (CM.p.inj h).1
  have hright : y = p (cub a) (cub a) := (CM.p.inj h).2
  have hself : cub a = p (cub a) (cub a) :=
    hleft.symm.trans hright
  have hs := congrArg sz hself
  simp [sz] at hs
  omega

theorem op_yy_raw (y : CM) : op y y = p y y := by
  unfold op
  apply root_eq_self
  · exact no_yy_lhs0 y _ _
  · exact no_yy_lhs1 y _

theorem no_yy_y_lhs0 (y a x : CM) :
    p (p y y) y = lhs0 a x → False := by
  intro h
  have hleft : p y y = a := (CM.p.inj h).1
  have hright : y = p x (cub a) := (CM.p.inj h).2
  have hlarge : y = p x (cub (p y y)) :=
    hright.trans (congrArg (fun q => p x (cub q)) hleft).symm
  have hs := congrArg sz hlarge
  simp [cub, sz] at hs
  omega

theorem no_yy_y_lhs1 (y a : CM) :
    p (p y y) y = lhs1 a → False := by
  intro h
  have hleft : p y y = cub a := (CM.p.inj h).1
  have hy : y = a := (CM.p.inj hleft).2
  have hself : y = p y y := by
    calc
      y = p a a := (CM.p.inj hleft).1
      _ = p y y := by rw [hy]
  have hs := congrArg sz hself
  simp [sz] at hs
  omega

theorem op_yy_y_raw (y : CM) : op (p y y) y = cub y := by
  change root (p (p y y) y) = p (p y y) y
  apply root_eq_self
  · exact no_yy_y_lhs0 y _ _
  · exact no_yy_y_lhs1 y _

theorem mid_ne_lhs1 (x y a : CM) :
    p x (cub y) = lhs1 a → False := by
  intro h
  have hleft : x = cub a := (CM.p.inj h).1
  have hright : cub y = p (cub a) (cub a) := (CM.p.inj h).2
  have hy : y = cub a := (CM.p.inj hright).2
  have hhead : p y y = cub a := (CM.p.inj hright).1
  have hself : p y y = y := hhead.trans hy.symm
  have hs := congrArg sz hself
  simp [sz] at hs
  omega

theorem source_holds (x y : CM) :
    x = op y (op x (op (op y y) y)) := by
  rw [op_yy_raw, op_yy_y_raw]
  by_cases h : p x (cub y) = lhs0 x (p y y)
  · have hright : cub y = p (p y y) (cub x) := (CM.p.inj h).2
    have hy : y = cub x := (CM.p.inj hright).2
    have hmid : op x (cub y) = p y y := by
      unfold op
      rw [h]
      exact root_lhs0 x (p y y)
    rw [hmid, hy]
    exact (op_rule1 x).symm
  · have hmid : op x (cub y) = p x (cub y) := by
      have hn1 :
          p x (cub y) = lhs1 (get1a (p x (cub y))) → False :=
        mid_ne_lhs1 x y _
      exact root_eq_self h hn1
    rw [hmid]
    exact (op_rule0 y x).symm

end CM

end submission

open submission

namespace submission.CM

theorem d10TargetRefutation
    (target : @EquationRHS CM CM.instMagma) : False := by
  first
  | have bad := target CM.e
    change (CM.e : CM) = (@Magma.op CM CM.instMagma (@Magma.op CM CM.instMagma (CM.e : CM) (@Magma.op CM CM.instMagma (CM.e : CM) (CM.e : CM))) (@Magma.op CM CM.instMagma (CM.e : CM) (CM.e : CM))) at bad
    exact nomatch bad

end submission.CM

def submission : Goal := by
  refine ⟨CM, CM.instMagma, ?_, ?_⟩
  · intro x y
    exact CM.source_holds x y
  · intro target
    exact CM.d10TargetRefutation target

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_680_to_1832 : ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G := submission
#print axioms certificate_680_to_1832
