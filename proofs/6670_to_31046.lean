-- Equation6670 → Equation31046
-- Recorded verdict: false
-- Premise: x = y ◇ (x ◇ ((x ◇ y) ◇ (z ◇ z)))
-- Conclusion: x = (x ◇ ((x ◇ y) ◇ (z ◇ y))) ◇ z
-- Original submission SHA-256: 51b604d08a8594183b36a4217a1a1a820a5f503de5d32be15e66958449a2bc61
-- Aurora-accepted correction SHA-256: ebc6beccdba22188f1d245ae90bc92c0de8931baea8bf9c2a76a57d06255ddb9
-- Generator: equational-challenges standalone v2
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
@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = y ◇ (x ◇ ((x ◇ y) ◇ (z ◇ z)))
@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop := ∀ (x : G) (y : G) (z : G), x = (x ◇ ((x ◇ y) ◇ (z ◇ y))) ◇ z
abbrev Goal : Prop := ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G
end

-- Aurora-accepted corrected submission body
                   

namespace submission

set_option maxHeartbeats 0

namespace CM6670_31046

abbrev B := Bool × Bool

structure M where
  b0 : Bool
  b1 : Bool
  u0 : Bool
  u1 : Bool

theorem Mext (x y : M)
    (h0 : x.b0 = y.b0) (h1 : x.b1 = y.b1)
    (h2 : x.u0 = y.u0) (h3 : x.u1 = y.u1) : x = y := by
  cases x
  cases y
  cases h0
  cases h1
  cases h2
  cases h3
  rfl

def sel (p : B) (v0 v1 v2 v3 : Bool) : Bool :=
  if p.1 then (if p.2 then v3 else v2) else (if p.2 then v1 else v0)

def tab (p q : B)
    (v00 v01 v02 v03 v10 v11 v12 v13
     v20 v21 v22 v23 v30 v31 v32 v33 : Bool) : Bool :=
  sel p (sel q v00 v01 v02 v03) (sel q v10 v11 v12 v13)
    (sel q v20 v21 v22 v23) (sel q v30 v31 v32 v33)

def a00 (p q : B) := tab p q true true false true false true true false
  true true true true true false false false
def a01 (p q : B) := tab p q true false true false true false true true
  false true true false true true true true
def a10 (p q : B) := tab p q true false true true true false false true
  true true false true false true true true
def a11 (p q : B) := tab p q false true true true true true true true
  true false true true true true true true
def b00 (p q : B) := tab p q true false true true false true true false
  true true true false false false true false
def b01 (p q : B) := tab p q true true false true true false true true
  true true true true true true false true
def b10 (p q : B) := tab p q true true true false true false true true
  true false false true true true true true
def b11 (p q : B) := tab p q false true true true true true false true
  false true true true false true true true
def t0 (p q : B) := tab p q true false true false false true true false
  false true true true false false true true
def t1 (p q : B) := tab p q true true true true false true true true
  false true true false false true false true

def op (x y : M) : M :=
  let p : B := (x.b0, x.b1)
  let q : B := (y.b0, y.b1)
  {
    b0 := x.b1 ^^ y.b1
    b1 := (x.b0 ^^ y.b0) ^^ (x.b1 ^^ y.b1)
    u0 := (a00 p q && x.u0) ^^ (a01 p q && x.u1) ^^
      (b00 p q && y.u0) ^^ (b01 p q && y.u1) ^^ t0 p q
    u1 := (a10 p q && x.u0) ^^ (a11 p q && x.u1) ^^
      (b10 p q && y.u0) ^^ (b11 p q && y.u1) ^^ t1 p q
  }

theorem source (x y z : M) :
    x = op y (op x (op (op x y) (op z z))) := by
  rcases x with ⟨x0, x1, x2, x3⟩
  rcases y with ⟨y0, y1, y2, y3⟩
  rcases z with ⟨z0, z1, z2, z3⟩
  cases x0 <;> cases x1 <;> cases y0 <;> cases y1 <;> cases z0 <;> cases z1 <;>
    apply Mext <;>
    simp [op, a00, a01, a10, a11, b00, b01, b10, b11, t0, t1, tab, sel,
      Bool.xor_assoc, Bool.xor_comm, Bool.xor_left_comm]

def xw : M := ⟨false, false, false, false⟩
def zw : M := ⟨false, true, false, false⟩

theorem target_not :
    ¬ ∀ x y z : M, x = op (op x (op (op x y) (op z y))) z := by
  intro h
  have bad := congrArg M.u0 (h xw xw zw)
  exact Bool.noConfusion bad

end CM6670_31046

def certificate : Goal := by
  refine ⟨CM6670_31046.M, ⟨CM6670_31046.op⟩, ?_, ?_⟩
  · exact CM6670_31046.source
  · exact CM6670_31046.target_not

end submission

def submission : Goal := submission.certificate

-- Explicit verdict-specific target, independent of the Goal abbreviation.
theorem certificate_6670_to_31046 : ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G := submission
#print axioms certificate_6670_to_31046
