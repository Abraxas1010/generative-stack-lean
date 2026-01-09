/-!
# Minimal surreal core

`SurrealCore` collects the lightweight, list-based `PreGame` structure
that the rest of the surreal pipeline relies on. It offers:

* a smart constructor (`PreGame.build`) that computes a consistent birthday,
* budgeted comparison operators (`leAt`/`le`/`lt`) and a legality predicate,
* small, executable arithmetic on pre-games (`add`/`neg`/`mul`) implemented
  via fuel-based recursion (suitable for demos and smoke tests).

This module is intentionally lightweight and is not presented as a full,
quotiented Conway theory of surreal numbers.
-/

namespace HeytingLean
namespace Numbers
namespace SurrealCore

/-- Minimal pre-game skeleton used by the surreal pipeline. -/
structure PreGame where
  L : List PreGame := []
  R : List PreGame := []
  birth : Nat := 0
deriving Repr

namespace PreGame

def maxBirth (xs : List PreGame) : Nat :=
  xs.foldl (fun acc g => Nat.max acc g.birth) 0

/-- Smart constructor that updates `birth` from child lists. -/
def build (L R : List PreGame) : PreGame :=
  { L := L
    R := R
    birth := Nat.succ (Nat.max (maxBirth L) (maxBirth R)) }

end PreGame

/-! ### Conway null cut and birthdays -/

/-- Conway-style null cut `{∅ ∣ ∅}` with birthday zero. -/
def nullCut : PreGame :=
  { L := [], R := [], birth := 0 }

def birthday (g : PreGame) : Nat := g.birth

def truncate (θ : Nat) (g : PreGame) : Option PreGame :=
  if birthday g ≤ θ then some g else none

/-- Finite-day comparison core (rank-indexed): `leAt k x y` computes `x ≤ y` up to budget `k`. -/
noncomputable def leAt : Nat → PreGame → PreGame → Prop
  | 0, _, _ => True
  | Nat.succ k, x, y =>
      (∀ l ∈ x.L, ¬ leAt k y l) ∧ (∀ r ∈ y.R, ¬ leAt k r x)

/-- Finite-day order: `x ≤ y` at budget `x.birth + y.birth`. -/
noncomputable def le (x y : PreGame) : Prop :=
  leAt (x.birth + y.birth) x y

/-- Strict order derived from `≤` by asymmetry. -/
noncomputable def lt (x y : PreGame) : Prop := ¬ le y x

/-- Legality via the classical cut condition. -/
noncomputable def legal (g : PreGame) : Prop :=
  ∀ l ∈ g.L, ∀ r ∈ g.R, lt l r

/-- Canonicalisation (identity). -/
def canonicalize (g : PreGame) : PreGame := g

/-- Surreal closure hook: canonicalise and assume legality is enforced upstream. -/
def close (g : PreGame) : PreGame := canonicalize g

theorem canonicalize_idem (g : PreGame) :
    canonicalize (canonicalize g) = canonicalize g := rfl

/-! ## Arithmetic skeleton (to be refined) -/

private def addAt : Nat → PreGame → PreGame → PreGame
  | 0, _, _ => nullCut
  | Nat.succ k, x, y =>
      let xL := x.L.map (fun l => addAt k l y)
      let yL := y.L.map (fun l => addAt k x l)
      let xR := x.R.map (fun r => addAt k r y)
      let yR := y.R.map (fun r => addAt k x r)
      PreGame.build (xL ++ yL) (xR ++ yR)

/-- Conway-style addition on pre-games, implemented via a fuel bound derived from birthdays.

This is an executable approximation suitable for demos; it does not claim to be
the fully-quotiented surreal addition. -/
def add (x y : PreGame) : PreGame :=
  addAt (Nat.succ (x.birth + y.birth)) x y

/-- Conway negation on pre-games: swap left/right options recursively. -/
private def negAt : Nat → PreGame → PreGame
  | 0, x => x
  | Nat.succ k, x => PreGame.build (x.R.map (fun r => negAt k r)) (x.L.map (fun l => negAt k l))

def neg (x : PreGame) : PreGame :=
  negAt (Nat.succ x.birth) x

private def sub (x y : PreGame) : PreGame := add x (neg y)

private def listBind {α β : Type} (xs : List α) (f : α → List β) : List β :=
  xs.foldr (fun x acc => f x ++ acc) []

private def mulAt : Nat → PreGame → PreGame → PreGame
  | 0, _, _ => nullCut
  | Nat.succ k, x, y =>
      let mulRec := fun a b => mulAt k a b
      let L₁ :=
        listBind x.L (fun xl =>
          y.L.map (fun yl =>
            sub (add (mulRec xl y) (mulRec x yl)) (mulRec xl yl)))
      let L₂ :=
        listBind x.R (fun xr =>
          y.R.map (fun yr =>
            sub (add (mulRec xr y) (mulRec x yr)) (mulRec xr yr)))
      let R₁ :=
        listBind x.L (fun xl =>
          y.R.map (fun yr =>
            sub (add (mulRec xl y) (mulRec x yr)) (mulRec xl yr)))
      let R₂ :=
        listBind x.R (fun xr =>
          y.L.map (fun yl =>
            sub (add (mulRec xr y) (mulRec x yl)) (mulRec xr yl)))
      PreGame.build (L₁ ++ L₂) (R₁ ++ R₂)

/-- Conway-style multiplication on pre-games, implemented via a fuel bound derived from birthdays.

This is an executable approximation suitable for demos; it does not claim to be
the fully-quotiented surreal multiplication. -/
def mul (x y : PreGame) : PreGame :=
  mulAt (Nat.succ (x.birth + y.birth)) x y

end SurrealCore
end Numbers
end HeytingLean
