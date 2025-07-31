import Mathlib.Control.Monad.Writer
import Mathlib.Control.Monad.Cont
import Mathlib.Tactic.Cases

/-!
# Free Monad and Common Instances

This file defines a general `FreeM` monad construction.

The `FreeM` monad generates a free monad from any type constructor `f : Type → Type`, without
requiring `f` to be a `Functor`. This implementation uses the "freer monad" approach as the
traditional free monad is not safely definable in Lean due to termination checking.

In this construction, computations are represented as **trees of effects**. Each node (`liftBind`)
represents a request to perform an effect, accompanied by a continuation specifying how the
computation proceeds after the effect. The leaves (`pure`) represent completed computations with
final results.
-/

/-- The Free monad over a type constructor `f`.

A `FreeM f a` is a tree of operations from the type constructor `f`, with leaves of type `a`.
It has two constructors: `pure` for wrapping a value of type `a`, and `liftBind` for
representing an operation from `f` followed by a continuation.

This construction provides a free monad for any type constructor `f`, allowing for composable
effect descriptions that can be interpreted later. Unlike the traditional free monad,
this does not require `f` to be a functor. -/
inductive FreeM.{u, v, w} (f : Type u → Type v) (α : Type w) where
  | protected pure : α → FreeM f α
  | liftBind {ι : Type u} (op : f ι) (cont : ι → FreeM f α) : FreeM f α

-- Disable simpNF lints for auto-generated constructor lemmas, as they don't follow simp normal
-- form patterns.
attribute [nolint simpNF] FreeM.pure.sizeOf_spec FreeM.pure.injEq

universe u v w

namespace FreeM

/-- Map a function over a `FreeM` monad. -/
def map {α β : Type _} {F : Type u → Type v} (f : α → β) : FreeM F α → FreeM F β
  | .pure a => .pure (f a)
  | .liftBind op cont => .liftBind op (fun z => map f (cont z))

instance {F : Type u → Type v} : Functor (FreeM F) where
  map := map

instance {F : Type u → Type v} : LawfulFunctor (FreeM F) where
  map_const := rfl
  id_map x := by
    simp [Functor.map]
    induction x with
    | pure a => rfl
    | liftBind op cont ih =>
      simp [map, ih]
  comp_map g h x := by
    simp [Functor.map]
    induction x with
    | pure a => rfl
    | liftBind op cont ih => simp [FreeM.map, ih]

/-- Bind operation for the `FreeM` monad. -/
protected def bind {a b : Type _} {F : Type u → Type v} (x : FreeM F a) (f : a → FreeM F b) :
FreeM F b :=
  match x with
  | .pure a => f a
  | .liftBind op cont => .liftBind op (fun z => .bind (cont z) f)

/-- Lift an operation from the effect signature `f` into the `FreeM f` monad. -/
@[simp]
def lift {F : Type u → Type v} {ι : Type u} (op : F ι) : FreeM F ι :=
  .liftBind op .pure

instance {F : Type u → Type v} : Monad (FreeM F) where
  pure := .pure
  bind := .bind

@[simp]
lemma pure_eq_pure {F : Type u → Type v} {α : Type w} (a : α) :
    (FreeM.pure a : FreeM F α) = pure a := rfl

/-- The `liftBind` constructor is semantically equivalent to `(lift op) >>= cont`. -/
lemma liftBind_eq_lift_bind {F : Type u → Type v} {ι : Type u} {α : Type u}
    (op : F ι) (cont : ι → FreeM F α) :
    FreeM.liftBind op cont = (lift op) >>= cont := by
    simp [lift, bind, FreeM.bind]

instance {F : Type u → Type v} : LawfulMonad (FreeM F) := LawfulMonad.mk'
  (bind_pure_comp := by {
    intro _ _ f x;
    induction' x with a b op cont ih
    · simp only [bind, FreeM.bind, Functor.map, Pure.pure, map]
    · simp only [Functor.map, bind, FreeM.bind, map, Pure.pure, map] at *; simp only [ih]
  })
  (id_map := by intro x y; induction' y with a b op cont ih'; all_goals {simp})
  (pure_bind := by
    intro α β x f
    simp [bind, FreeM.bind])
  (bind_assoc := by
    intro _ _ _ x f g; induction' x with a b op cont ih;
    · simp only [bind, FreeM.bind]
    · simp only [bind, FreeM.bind] at *; simp [ih])


/--
Interpret a `FreeM f` computation into any monad `m` by providing an interpretation
function for the effect signature `f`.

This function defines the *canonical interpreter* from the free monad `FreeM f` into the target
monad `m`. It is the unique monad morphism that extends the effect handler
`interp : ∀ {β}, F β → M β` via the universal property of `FreeM` -/
protected def mapM {F : Type u → Type v} {M : Type u → Type w} [Monad M] {α : Type u} :
    FreeM F α → ({β : Type u} → F β → M β) → M α
  | .pure a, _ => pure a
  | .liftBind op cont, interp => interp op >>= fun result => (cont result).mapM interp

@[simp]
lemma mapM_pure {F : Type u → Type v} {M : Type u → Type w} [Monad M] {α : Type u}
    (interp : {β : Type u} → F β → M β) (a : α) :
    (pure a : FreeM F α).mapM interp = pure a := by simp [FreeM.mapM]

@[simp]
lemma mapM_liftBind {F : Type u → Type v} {M : Type u → Type w} [Monad M] {α β : Type u}
    (interp : {γ : Type u} → F γ → M γ) (op : F β) (cont : β → FreeM F α) :
    (FreeM.liftBind op cont).mapM interp = interp op >>=
    fun result => (cont result).mapM interp := by simp [FreeM.mapM]

lemma mapM_lift {F : Type u → Type v} {M : Type u → Type w} [Monad M] [LawfulMonad M] {α : Type u}
    (interp : {β : Type u} → F β → M β) (op : F α) :
    (lift op).mapM interp = interp op := by
  simp [FreeM.mapM, lift]

/-- The fold function for a `FreeM` monad. The unique morphism from the initial algebra
to any other algebra.
-/
def foldM {F : Type u → Type v} {α β : Type w}
  (pureCase : α → β)
  (bindCase : {ι : Type u} → F ι → (ι → β) → β)
  : FreeM F α → β
| .pure a => pureCase a
| .liftBind op k => bindCase op (fun x => foldM pureCase bindCase (k x))

/--
A predicate stating that `g : FreeM F α → M α` is an interpreter for the effect
handler `f : ∀ {α}, F α → M α`.

This means that `g` is a monad morphism from the free monad `FreeM F` to the
monad `M`, and that it extends the interpretation of individual operations
given by `f`.

Formally, `g` satisfies the two equations:
- `g (pure a) = pure a`
- `g (liftBind op k) = f op >>= fun x => g (k x)`
-/
def ExtendsHandler
    {F : Type u → Type v} {M : Type u → Type w} [Monad M] {α : Type u}
    (f : {ι : Type u} → F ι → M ι)
    (g : FreeM F α → M α) : Prop :=
  (∀ a, g (pure a) = pure a) ∧
  (∀ {ι} (op : F ι) (k : ι → FreeM F α),
    g (FreeM.liftBind op k) = f op >>= fun x => g (k x))

/--
The universal property of the free monad `FreeM`. That is, `mapM f` is the unique interpreter that
extends the effect handler `f` to interpret `FreeM F` computations in monad `M`.
-/
theorem extendsHandler_iff
{F : Type u → Type v} {m : Type u → Type w} [Monad m] {α : Type u}
    (f : {ι : Type u} → F ι → m ι) (g : FreeM F α → m α) :
    ExtendsHandler @f g ↔ g = (·.mapM @f) := by
  refine ⟨fun h => funext fun x => ?_, fun h => ?_⟩
  · induction x with
    | pure a => exact h.1 a
    | liftBind op cont ih =>
      rw [mapM_liftBind, h.2]
      simp [ih]
  · subst h
    exact ⟨fun _ => rfl, fun _ _ => rfl⟩
end FreeM
