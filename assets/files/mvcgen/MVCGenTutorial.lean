import Std.Data.HashMap
import Std.Data.HashSet

import Std.Tactic.Do

set_option mvcgen.warning false

open Std.Do

def mySum (l : Array Nat) : Nat := Id.run do
  let mut out := 0
  for i in l do
    out := out + i
  return out

theorem mySum_correct (l : Array Nat) : mySum l = l.sum := by
  -- Focus on the part of the program with the `do` block (`Id.run ...`)
  generalize h : mySum l = x
  apply Id.of_wp_run_eq h
  -- Break down into verification conditions
  mvcgen
  -- Specify the invariant which should hold throughout the loop
  -- * `out` refers to the current value of the `let mut` variable
  -- * `xs` is a `List.Cursor`, which is a data structure representing
  --   a list that is split into `xs.prefix` and `xs.suffix`.
  --   It tracks how far into the loop we have gotten.
  -- Our invariant is that `out` holds the sum of the prefix.
  -- The notation ⌜p⌝ embeds a `p : Prop` into the assertion language.
  case inv1 => exact ⇓⟨xs, out⟩ => ⌜xs.prefix.sum = out⌝
  -- After specifying the invariant, we can further simplify our goals
  -- by "leaving the proof mode". `mleave` is just
  -- `simp only [...] at *` with a stable simp subset.
  all_goals mleave
  -- Prove that our invariant is preserved at each step of the loop
  case vc1 ih =>
    -- The goal here mentions `pref`, which binds the `prefix` field of
    -- the cursor passed to the invariant. Unpacking the
    -- (dependently-typed) cursor makes it easier for `grind`.
    grind
  -- Prove that the invariant is true at the start
  case vc2 =>
    grind
  -- Prove that the invariant at the end of the loop implies the
  -- property we wanted
  case vc3 h =>
    grind

theorem mySum_correct_short (l : Array Nat) : mySum l = l.sum := by
  generalize h : mySum l = x
  apply Id.of_wp_run_eq h
  mvcgen
  case inv1 => exact ⇓⟨xs, out⟩ => ⌜xs.prefix.sum = out⌝
  all_goals mleave; grind

theorem mySum_correct_shorter (l : Array Nat) : mySum l = l.sum := by
  generalize h : mySum l = x
  apply Id.of_wp_run_eq h
  mvcgen
  invariants
  · ⇓⟨xs, out⟩ => ⌜xs.prefix.sum = out⌝
  with grind

theorem mySum_correct_vanilla (l : Array Nat) : mySum l = l.sum := by
  -- Turn the array into a list
  cases l with | mk l =>
  -- Unfold `mySum` and rewrite `forIn` to `foldl`
  simp [mySum]
  -- Generalize the inductive hypothesis
  suffices h : ∀ out, List.foldl (· + ·) out l = out + l.sum by simp [h]
  -- Grind away
  induction l with grind

def nodup (l : List Int) : Bool := Id.run do
  let mut seen : Std.HashSet Int := ∅
  for x in l do
    if x ∈ seen then
      return false
    seen := seen.insert x
  return true

theorem nodup_correct (l : List Int) : nodup l ↔ l.Nodup := by
  generalize h : nodup l = r
  apply Id.of_wp_run_eq h
  mvcgen
  invariants
  · Invariant.withEarlyReturnNewDo
      (onReturn := fun ret seen => ⌜ret = false ∧ ¬l.Nodup⌝)
      (onContinue := fun xs seen =>
        ⌜(∀ x, x ∈ seen ↔ x ∈ xs.prefix) ∧ xs.prefix.Nodup⌝)
  with grind

example (l : List Int) : nodup l ↔ l.Nodup := by
  generalize h : nodup l = r
  apply Id.of_wp_run_eq h
  mvcgen invariants? <;> sorry

theorem nodup_correct_directly (l : List Int) : nodup l ↔ l.Nodup := by
  rw [nodup]
  generalize hseen : (∅ : Std.HashSet Int) = seen
  change ?lhs ↔ l.Nodup
  suffices h : ?lhs ↔ l.Nodup ∧ ∀ x ∈ l, x ∉ seen by grind
  clear hseen
  induction l generalizing seen with grind [Id.run_pure, Id.run_bind]

structure Supply where
  counter : Nat

def mkFresh : StateM Supply Nat := do
  let n ← (·.counter) <$> get
  modify fun s => { s with counter := s.counter + 1 }
  pure n

def mkFreshN (n : Nat) : StateM Supply (List Nat) := do
  let mut acc := #[]
  for _ in [:n] do
    acc := acc.push (← mkFresh)
  pure acc.toList

theorem mkFreshN_correct (n : Nat) : ((mkFreshN n).run' s).Nodup := by
  -- Focus on `(mkFreshN n).run' s`.
  generalize h : (mkFreshN n).run' s = x
  apply StateM.of_wp_run'_eq h
  -- Show something about monadic program `mkFresh n`.
  -- The `mkFreshN` and `mkFresh` arguments to `mvcgen` add to an
  -- internal `simp` set and makes `mvcgen` unfold these definitions.
  mvcgen [mkFreshN, mkFresh]
  invariants
  -- Invariant: The counter is larger than any accumulated number,
  --            and all accumulated numbers are distinct.
  -- Note that the invariant may refer to the state through function
  -- argument `state : Supply`. Since the next number to accumulate is
  -- the counter, it is distinct to all accumulated numbers.
  · ⇓⟨xs, acc⟩ state =>
      ⌜(∀ x ∈ acc, x < state.counter) ∧ acc.toList.Nodup⌝
  with grind

-- This is the definition of Std.Do.Triple:
def Triple [WP m ps] {α : Type u} (prog : m α)
    (P : Assertion ps) (Q : PostCond α ps) : Prop :=
  P ⊢ₛ wp⟦prog⟧ Q

def StateMTriple {α σ : Type u} (prog : StateM σ α)
    (P : σ → ULift Prop) (Q : (α → σ → ULift Prop) × PUnit) : Prop :=
  ∀ s, (P s).down → let (a, s') := prog.run s; (Q.1 a s').down

@[spec]
theorem mkFresh_spec (c : Nat) :
    ⦃fun state => ⌜state.counter = c⌝⦄
    mkFresh
    ⦃⇓ r state => ⌜r = c ∧ c < state.counter⌝⦄ := by
  -- Unfold `mkFresh` and blast away:
  mvcgen [mkFresh] with grind

@[spec]
theorem mkFreshN_spec (n : Nat) :
    ⦃⌜True⌝⦄ mkFreshN n ⦃⇓ r => ⌜r.Nodup⌝⦄ := by
  -- `mvcgen [mkFreshN, mkFresh_spec]` if `mkFresh_spec` were not
  -- registered with `@[spec]`
  mvcgen [mkFreshN]
  invariants
  -- As before:
  · ⇓⟨xs, acc⟩ state =>
      ⌜(∀ x ∈ acc, x < state.counter) ∧ acc.toList.Nodup⌝
  with grind

theorem mkFreshN_correct_compositional (n : Nat) :
    ((mkFreshN n).run' s).Nodup := by
  generalize h : (mkFreshN n).run' s = x
  apply StateM.of_wp_run'_eq h
  mvcgen

axiom M : Type → Type
variable {x y : UInt8} [Monad M] [WP M .pure]
def addQ (x y : UInt8) : M UInt8 := pure (x + y)
local infix:1023 " +? " => addQ

namespace Transformers

abbrev CounterM := StateT Supply (ReaderM String)

abbrev AppM := StateT Bool CounterM

def mkFresh : CounterM Nat := do
  let n ← (·.counter) <$> get
  modify fun s => { s with counter := s.counter + 1 }
  pure n

def mkFreshN (n : Nat) : AppM (List Nat) := do
  let mut acc := #[]
  for _ in [:n] do
    let n ← mkFresh
    acc := acc.push n
  return acc.toList

@[spec]
theorem mkFresh_spec (c : Nat) :
    ⦃fun state => ⌜state.counter = c⌝⦄
    mkFresh
    ⦃⇓ r state => ⌜r = c ∧ c < state.counter⌝⦄ := by
  mvcgen [mkFresh] with grind

@[spec]
theorem mkFreshN_spec (n : Nat) :
    ⦃⌜True⌝⦄ mkFreshN n ⦃⇓ r => ⌜r.Nodup⌝⦄ := by
  -- `liftCounterM` here ensures unfolding
  mvcgen [mkFreshN]
  invariants
  · ⇓⟨xs, acc⟩ _ state =>
      ⌜(∀ n ∈ acc, n < state.counter) ∧ acc.toList.Nodup⌝
  with grind

end Transformers

namespace Exceptions

structure Supply where
  counter : Nat
  limit : Nat
  property : counter ≤ limit

def mkFresh : EStateM String Supply Nat := do
  let supply ← get
  if h : supply.counter = supply.limit then
    throw s!"Supply exhausted: {supply.counter} = {supply.limit}"
  else
    let n := supply.counter
    have := supply.property
    set { supply with counter := n + 1, property := by grind }
    pure n

@[spec]
theorem mkFresh_spec (c : Nat) :
    ⦃fun state => ⌜state.counter = c⌝⦄
    mkFresh
    ⦃post⟨fun r state => ⌜r = c ∧ c < state.counter⌝,
          fun _ state => ⌜c = state.counter ∧ c = state.limit⌝⟩⦄ := by
  mvcgen [mkFresh] with grind

def mkFreshN (n : Nat) : EStateM String Supply (List Nat) := do
  let mut acc := #[]
  for _ in [:n] do
    acc := acc.push (← mkFresh)
  pure acc.toList

@[spec]
theorem mkFreshN_spec (n : Nat) :
    ⦃⌜True⌝⦄
    mkFreshN n
    ⦃post⟨fun r => ⌜r.Nodup⌝,
          fun _msg state => ⌜state.counter = state.limit⌝⟩⦄ := by
  mvcgen [mkFreshN]
  invariants
  · post⟨fun ⟨xs, acc⟩ state =>
           ⌜(∀ n ∈ acc, n < state.counter) ∧ acc.toList.Nodup⌝,
         fun _msg state => ⌜state.counter = state.limit⌝⟩
  with grind

theorem mkFreshN_correct (n : Nat) :
    match (mkFreshN n).run s with
    | .ok    l _  => l.Nodup
    | .error _ s' => s'.counter = s'.limit := by
  generalize h : (mkFreshN n).run s = x
  apply EStateM.of_wp_run_eq h
  mvcgen

end Exceptions

inductive Error where
  | integerOverflow: Error
  -- ... more error kinds ...

inductive Result (α : Type u) where
  | ok (v: α): Result α
  | fail (e: Error): Result α
  | div

instance Result.instMonad : Monad Result where
  pure x := .ok x
  bind x f := match x with
  | .ok v => f v
  | .fail e => .fail e
  | .div => .div

instance Result.instLawfulMonad : LawfulMonad Result := by
  apply LawfulMonad.mk' _
  all_goals (dsimp [Functor.map, bind, pure]; grind)

instance : WP Result (.except Error .pure) where
  wp
    | .ok v => PredTrans.pure v
    | .fail e => PredTrans.throw e
    | .div => PredTrans.const ⌜False⌝

theorem Result.apply_wp_pure {α} {a : α} {Q} :
  wp⟦pure (f := Result) a⟧ Q = Q.1 a := by rfl

theorem Result.apply_wp_bind {α β} {x} {f : α → Result β} {Q} :
  wp⟦do let a ← x; f a⟧ Q = wp⟦x⟧ (fun a => wp⟦f a⟧ Q, Q.2) := by
  simp only [wp, bind]
  grind

instance Result.instWPMonad : WPMonad Result (.except Error .pure) where
  wp_pure _ := by ext Q : 1; apply Result.apply_wp_pure
  wp_bind x f := by ext Q : 1; apply Result.apply_wp_bind

theorem Result.of_wp_eq {α} {x prog : Result α}
    (h : prog = x) (P : Result α → Prop)
    (hspec : ⊢ₛ wp⟦prog⟧ post⟨fun a => ⌜P (.ok a)⌝,
                              fun e => ⌜P (.fail e)⌝⟩) :
      P x := by
  subst h
  match prog with
  | .ok a   => simpa [wp] using hspec
  | .fail e => simpa [wp] using hspec
  | .div    => simp [wp] at hspec

instance : MonadExcept Error Result where
  throw e := .fail e
  tryCatch x h := match x with
  | .ok v => pure v
  | .fail e => h e
  | .div => .div

def addOp (x y : UInt32) : Result UInt32 :=
  if x.toNat + y.toNat ≥ UInt32.size then
    throw .integerOverflow
  else
    pure (x + y)

@[spec]
theorem Result.throw_spec {α Q} (e : Error) :
    ⦃Q.2.1 e⦄ throw (m := Result) (α := α) e ⦃Q⦄ := id

@[spec]
theorem addOp_ok_spec {x y} (h : x.toNat + y.toNat < UInt32.size) :
    ⦃⌜True⌝⦄
    addOp x y
    ⦃⇓ r => ⌜r = x + y ∧ (x + y).toNat = x.toNat + y.toNat⌝⦄ := by
  mvcgen [addOp] with (simp_all; try grind)

example :
  ⦃⌜True⌝⦄
  do let mut x ← addOp 1 3
     for _ in [:4] do
        x ← addOp x 5
     return x
  ⦃⇓ r => ⌜r.toNat = 24⌝⦄ := by
  mvcgen
  invariants
  · ⇓⟨xs, x⟩ => ⌜x.toNat = 4 + 5 * xs.prefix.length⌝
  with (simp_all [UInt32.size]; try grind)

abbrev PostShape.args : PostShape.{u} → List (Type u)
  | .pure => []
  | .arg σ s => σ :: PostShape.args s
  | .except _ s => PostShape.args s

abbrev Assertion (ps : PostShape.{u}) : Type u :=
  SPred (PostShape.args ps)
