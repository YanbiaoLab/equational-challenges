-- Equation1279 → Equation39142
-- Recorded verdict: false
-- Premise: x = y ◇ (((x ◇ x) ◇ y) ◇ y)
-- Conclusion: x = (((y ◇ x) ◇ (y ◇ x)) ◇ y) ◇ y
-- Original submission SHA-256: 77b6ee51fc3b14a8f5e3e056b5ef0bfd61544e57d9ea4564936def754a63635f
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x = y ◇ (((x ◇ x) ◇ y) ◇ y)
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G), x = (((y ◇ x) ◇ (y ◇ x)) ◇ y) ◇ y
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

def sq (a : CM) : CM := p a a
def mid (x y : CM) : CM := p (sq x) y
def tail (x y : CM) : CM := p (mid x y) y
def d (a b : CM) : CM := tail a (sq b)

def lhs0 (y x : CM) : CM := p y (tail x y)
def lhs1 (a b : CM) : CM := p (d a b) (p a (d a b))
def lhs2 (b : CM) : CM := p (p (d b b) (sq b)) (sq b)

def get0y : CM → CM
  | p y _ => y
  | _ => e

def get0x : CM → CM
  | p _ (p (p (p x _) _) _) => x
  | _ => e

def get1a : CM → CM
  | p _ (p a _) => a
  | _ => e

def get1b : CM → CM
  | p (p _ (p b _)) _ => b
  | _ => e

def get2b : CM → CM
  | p _ (p b _) => b
  | _ => e

def root (t : CM) : CM :=
  let y0 := get0y t
  let x0 := get0x t
  if t = lhs0 y0 x0 then
    x0
  else
    let a1 := get1a t
    let b1 := get1b t
    if t = lhs1 a1 b1 then
      b1
    else
      let b2 := get2b t
      if t = lhs2 b2 then b2 else t

def op (a b : CM) : CM := root (p a b)

instance instMagma : Magma CM where
  op := op

theorem lhs1_ne_lhs0 (a b y x : CM) :
    lhs1 a b = lhs0 y x → False := by
  intro h
  have hy : d a b = y := (CM.p.inj h).1
  have hright : p a (d a b) = tail x y := (CM.p.inj h).2
  have ha : a = mid x y := (CM.p.inj hright).1
  rw [← hy] at ha
  have hs := congrArg sz ha
  simp [d, tail, mid, sq, sz] at hs
  omega

theorem lhs2_ne_lhs0 (b y x : CM) :
    lhs2 b = lhs0 y x → False := by
  intro h
  have hy : p (d b b) (sq b) = y := (CM.p.inj h).1
  have hright : sq b = tail x y := (CM.p.inj h).2
  have hb : b = mid x y := (CM.p.inj hright).1
  have hby : b = y := (CM.p.inj hright).2
  have hcycle : y = mid x y := hby.symm.trans hb
  have hs := congrArg sz hcycle
  simp [mid, sq, sz] at hs
  omega

theorem lhs2_ne_lhs1 (b a c : CM) :
    lhs2 b = lhs1 a c → False := by
  intro h
  have hleft : p (d b b) (sq b) = d a c := (CM.p.inj h).1
  have hright : sq b = p a (d a c) := (CM.p.inj h).2
  have hba : b = a := (CM.p.inj hright).1
  have hbd : b = d a c := (CM.p.inj hright).2
  have hcycle : b = d b c := by simpa [hba] using hbd
  have hs := congrArg sz hcycle
  simp [d, tail, mid, sq, sz] at hs
  omega

theorem root_lhs0 (y x : CM) : root (lhs0 y x) = x := by
  change
    (if lhs0 y x = lhs0 y x then x
      else
        if lhs0 y x =
            lhs1 (get1a (lhs0 y x)) (get1b (lhs0 y x))
        then get1b (lhs0 y x)
        else
          if lhs0 y x = lhs2 (get2b (lhs0 y x))
          then get2b (lhs0 y x) else lhs0 y x) = x
  rw [if_pos rfl]

theorem root_lhs1 (a b : CM) : root (lhs1 a b) = b := by
  change
    (if lhs1 a b = lhs0 (d a b) (get0x (lhs1 a b))
      then get0x (lhs1 a b)
      else
        if lhs1 a b = lhs1 a b then b
        else if lhs1 a b = lhs2 (get2b (lhs1 a b))
          then get2b (lhs1 a b) else lhs1 a b) = b
  rw [if_neg (lhs1_ne_lhs0 a b _ _), if_pos rfl]

theorem root_lhs2 (b : CM) : root (lhs2 b) = b := by
  change
    (if lhs2 b = lhs0 (p (d b b) (sq b)) (get0x (lhs2 b))
      then get0x (lhs2 b)
      else
        if lhs2 b = lhs1 b b then b
        else if lhs2 b = lhs2 b then b else lhs2 b) = b
  rw [
    if_neg (lhs2_ne_lhs0 b _ _),
    if_neg (lhs2_ne_lhs1 b _ _),
    if_pos rfl,
  ]

theorem root_eq_self {t : CM}
    (h0 : t = lhs0 (get0y t) (get0x t) → False)
    (h1 : t = lhs1 (get1a t) (get1b t) → False)
    (h2 : t = lhs2 (get2b t) → False) :
    root t = t := by
  unfold root
  rw [if_neg h0, if_neg h1, if_neg h2]

theorem op_rule0 (y x : CM) : op y (tail x y) = x := by
  exact root_lhs0 y x

theorem op_rule1 (a b : CM) :
    op (d a b) (p a (d a b)) = b := by
  exact root_lhs1 a b

theorem op_rule2 (b : CM) :
    op (p (d b b) (sq b)) (sq b) = b := by
  exact root_lhs2 b

theorem no_yy_lhs0 (u y x : CM) :
    p u u = lhs0 y x → False := by
  intro h
  have huy : u = y := (CM.p.inj h).1
  have hut : u = tail x y := (CM.p.inj h).2
  have hcycle : y = tail x y := huy.symm.trans hut
  have hs := congrArg sz hcycle
  simp [tail, mid, sq, sz] at hs
  omega

theorem no_yy_lhs1 (u a b : CM) :
    p u u = lhs1 a b → False := by
  intro h
  have hud : u = d a b := (CM.p.inj h).1
  have hur : u = p a (d a b) := (CM.p.inj h).2
  have hcycle : d a b = p a (d a b) := hud.symm.trans hur
  have hs := congrArg sz hcycle
  simp [d, tail, mid, sq, sz] at hs
  omega

theorem no_yy_lhs2 (u b : CM) :
    p u u = lhs2 b → False := by
  intro h
  have hleft : u = p (d b b) (sq b) := (CM.p.inj h).1
  have hright : u = sq b := (CM.p.inj h).2
  have hcycle : sq b = p (d b b) (sq b) :=
    hright.symm.trans hleft
  have hs := congrArg sz hcycle
  simp [d, tail, mid, sq, sz] at hs
  omega

theorem op_yy_raw (u : CM) : op u u = sq u := by
  unfold op
  apply root_eq_self
  · exact no_yy_lhs0 u _ _
  · exact no_yy_lhs1 u _ _
  · exact no_yy_lhs2 u _

theorem mid_ne_lhs1 (x y a b : CM) :
    mid x y = lhs1 a b → False := by
  intro h
  have hleft : sq x = d a b := (CM.p.inj h).1
  have hright : y = p a (d a b) := (CM.p.inj h).2
  have hx : x = mid a (sq b) := (CM.p.inj hleft).1
  have htail : x = sq b := (CM.p.inj hleft).2
  have hcycle : sq b = mid a (sq b) := htail.symm.trans hx
  have hs := congrArg sz hcycle
  simp [mid, sq, sz] at hs
  omega

theorem mid_ne_lhs2 (x y b : CM) :
    mid x y = lhs2 b → False := by
  intro h
  have hleft : sq x = p (d b b) (sq b) := (CM.p.inj h).1
  have hright : y = sq b := (CM.p.inj h).2
  have hx : x = d b b := (CM.p.inj hleft).1
  have hxb : x = sq b := (CM.p.inj hleft).2
  have hcycle : sq b = d b b := hxb.symm.trans hx
  have hs := congrArg sz hcycle
  simp [d, tail, mid, sq, sz] at hs
  omega

theorem tail_ne_lhs0 (x y a b : CM) :
    tail x y = lhs0 a b → False := by
  intro h
  have hleft : mid x y = a := (CM.p.inj h).1
  have hright : y = tail b a := (CM.p.inj h).2
  have hcycle : y = tail b (mid x y) := by simpa [hleft] using hright
  have hs := congrArg sz hcycle
  simp [tail, mid, sq, sz] at hs
  omega

theorem tail_ne_lhs1 (x y a b : CM) :
    tail x y = lhs1 a b → False := by
  intro h
  have hleft : mid x y = d a b := (CM.p.inj h).1
  have hright : y = p a (d a b) := (CM.p.inj h).2
  have hcycle : y = p a (mid x y) := by simpa [hleft] using hright
  have hs := congrArg sz hcycle
  simp [mid, sq, sz] at hs
  omega

theorem tail_ne_lhs2 (x y b : CM) :
    tail x y = lhs2 b → False := by
  intro h
  have hleft : mid x y = p (d b b) (sq b) := (CM.p.inj h).1
  have hright : y = sq b := (CM.p.inj h).2
  have hsquare : sq x = d b b := (CM.p.inj hleft).1
  have hx0 : x = mid b (sq b) := (CM.p.inj hsquare).1
  have hx1 : x = sq b := (CM.p.inj hsquare).2
  have hcycle : sq b = mid b (sq b) := hx1.symm.trans hx0
  have hs := congrArg sz hcycle
  simp [mid, sq, sz] at hs
  omega

theorem op_tail_raw (x y : CM) :
    op (mid x y) y = tail x y := by
  change root (tail x y) = tail x y
  apply root_eq_self
  · exact tail_ne_lhs0 x y _ _
  · exact tail_ne_lhs1 x y _ _
  · exact tail_ne_lhs2 x y _

theorem branch_ne_lhs1 (a x u v : CM) :
    p a (d a x) = lhs1 u v → False := by
  intro h
  have ha : a = d u v := (CM.p.inj h).1
  have hd : d a x = p u (d u v) := (CM.p.inj h).2
  have hu : mid a (sq x) = u := (CM.p.inj hd).1
  have hxa : sq x = d u v := (CM.p.inj hd).2
  have hax : a = sq x := ha.trans hxa.symm
  have hcycle : a = d (mid a (sq x)) v := by
    calc
      a = d u v := ha
      _ = d (mid a (sq x)) v := by rw [hu]
  have hs := congrArg sz hcycle
  simp [d, tail, mid, sq, sz] at hs
  omega

theorem branch_ne_lhs2 (a x b : CM) :
    p a (d a x) = lhs2 b → False := by
  intro h
  have ha : a = p (d b b) (sq b) := (CM.p.inj h).1
  have hd : d a x = sq b := (CM.p.inj h).2
  have hleft : mid a (sq x) = b := (CM.p.inj hd).1
  have hright : sq x = b := (CM.p.inj hd).2
  have hcycle : b = mid a b := by
    calc
      b = mid a (sq x) := hleft.symm
      _ = mid a b := congrArg (mid a) hright
  have hs := congrArg sz hcycle
  simp [mid, sq, sz] at hs
  omega

theorem source_holds (x y : CM) :
    x = op y (op (op (op x x) y) y) := by
  rw [op_yy_raw]
  let t := mid x y
  by_cases h0 : t = lhs0 (get0y t) (get0x t)
  · let a := get0x t
    have hsx : sq x = get0y t := (CM.p.inj h0).1.symm
    have hy : y = d a x := by
      have htail : y = tail a (get0y t) := (CM.p.inj h0).2
      simpa [a, d, hsx] using htail
    have ht : op (sq x) y = a := by
      change root t = a
      unfold root
      rw [if_pos h0]
    rw [ht, hy]
    let r := p a (d a x)
    by_cases k0 : r = lhs0 (get0y r) (get0x r)
    · have hr : op a (d a x) = get0x r := by
        change root r = get0x r
        unfold root
        rw [if_pos k0]
      have hax : a = sq x := by
        have hleft : a = get0y r := (CM.p.inj k0).1
        have hright : d a x = tail (get0x r) (get0y r) :=
          (CM.p.inj k0).2
        have hmid :
            mid a (sq x) = mid (get0x r) (get0y r) :=
          (CM.p.inj hright).1
        have htail : sq x = get0y r := (CM.p.inj hright).2
        exact hleft.trans htail.symm
      have hget : get0x r = a := by
        have hright : d a x = tail (get0x r) (get0y r) :=
          (CM.p.inj k0).2
        have hmid :
            mid a (sq x) = mid (get0x r) (get0y r) :=
          (CM.p.inj hright).1
        exact (CM.p.inj (CM.p.inj hmid).1).1.symm
      rw [hr, hget, hax]
      exact (op_rule2 x).symm
    · have hr : op a (d a x) = r := by
        change root r = r
        apply root_eq_self k0
        · exact branch_ne_lhs1 a x _ _
        · exact branch_ne_lhs2 a x _
      rw [hr]
      exact (op_rule1 a x).symm
  · have ht : op (sq x) y = t := by
      change root t = t
      apply root_eq_self h0
      · exact mid_ne_lhs1 x y _ _
      · exact mid_ne_lhs2 x y _
    rw [ht, op_tail_raw]
    exact (op_rule0 y x).symm

theorem witness_rhs :
    op (op (op (op e e) (op e e)) e) e =
      p (p (p (sq e) (sq e)) e) e := by
  rfl

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
        CM.op
          (CM.op
            (CM.op (CM.op CM.e CM.e) (CM.op CM.e CM.e))
            CM.e)
          CM.e at bad
    rw [CM.witness_rhs] at bad
    exact CM.noConfusion bad

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_1279_to_39142 : ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G := submission
#print axioms certificate_1279_to_39142
