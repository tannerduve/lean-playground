/-
Copyright (c) 2025 Tanner Duve. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tanner Duve
-/
import Mathlib.Control.Monad.Cont
import Mathlib.Control.Monad.Writer
import Mathlib.Tactic.Cases

/-!
# Free Monad and Common Instances

This file defines a general `FreeM` monad construction and several canonical instances:
`State`, `Writer`, and `Continuation` monads implemented via this construction.

The `FreeM` monad generates a free monad from any type constructor `f : Type → Type`, without
requiring `f` to be a `Functor`. This implementation uses the "freer monad" approach as the
traditional free monad is not safely definable in Lean due to termination checking.

In this construction, computations are represented as **trees of effects**. Each node (`liftBind`)
represents a request to perform an effect, accompanied by a continuation specifying how the
computation proceeds after the effect. The leaves (`pure`) represent completed computations with
final results.

A key insight is that `FreeM F` satisfies the **universal property of free monads**: for any monad
`M` and effect handler `f : F → M`, there exists a unique way to interpret `FreeM F` computations
in `M` that respects the effect semantics given by `f`. This unique interpreter is `liftM f`, which
acts as the canonical **fold** for free monads.

## Implementation

To execute or interpret these computations, we provide two approaches:
1. **Hand-written interpreters** (`FreeState.run`, `FreeWriter.run`, `FreeCont.run`) that directly
  pattern-match on the tree structure
2. **Canonical interpreters** (`FreeState.toStateM`, `FreeWriter.toWriterT`, `FreeCont.toContT`)
  derived from the universal property via `liftM`

We prove that these approaches are equivalent, demonstrating that the implementation aligns with
the theory. We also provide uniqueness theorems for the canonical interpreters, which follow from
the universal property.

## Main Definitions

- `FreeM`: The free monad construction
- `liftM`: The canonical fold/interpreter satisfying the universal property
- `FreeState`, `FreeWriter`, `FreeCont`: Specific effect monads with both hand-written and
  canonical interpreters
- `liftM_unique`: Proof of the universal property

See the Haskell [freer-simple](https://hackage.haskell.org/package/freer-simple) library for the
Haskell implementation that inspired this approach.

## Implementation Notes

The `FreeM` monad is defined using an inductive type with constructors `pure` and `liftBind`.
We implement `Functor` and `Monad` instances, and prove the corresponding `LawfulFunctor`
and `LawfulMonad` instances.

The monads `FreeState`, `FreeWriter`, and `FreeCont` are built by supplying appropriate
effect type constructors to the `FreeM` constructor. They are equipped with interpreters
and helper functions.

## References

* [Kiselyov2015] Oleg Kiselyov, Hiromi Ishii. *Freer Monads, More Extensible Effects*.
  Haskell Symposium 2015.
* [MilewskiDao] Bartosz Milewski. *The Dao of Functional Programming*. 2025.

## Tags

Free monad, state monad, writer monad, continuation monad
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

/-
Disable simpNF lints for auto-generated constructor lemmas, as they don't follow simp normal
form patterns. The LHS of these lemmas use `FreeM.pure` which simplifies to `pure` via
`pure_eq_pure`.
-/
attribute [nolint simpNF] FreeM.pure.sizeOf_spec
  FreeM.pure.injEq FreeM.liftBind.sizeOf_spec FreeM.liftBind.injEq

universe u v w w' w''

namespace FreeM

variable {F : Type u → Type v} {ι : Type u} {α : Type w} {β : Type w'} {γ : Type w''}

instance : Pure (FreeM F) where pure := .pure

@[simp]
theorem pure_eq_purePure : (pure : α → FreeM F α) = FreeM.pure := rfl

/-- Bind operation for the `FreeM` monad. -/
protected def bind (x : FreeM F α) (f : α → FreeM F β) : FreeM F β :=
  match x with
  | .pure a => f a
  | .liftBind op cont => .liftBind op (fun z => FreeM.bind (cont z) f)

protected theorem bind_assoc (x : FreeM F α) (f : α → FreeM F β) (g : β → FreeM F γ) :
    (x.bind f).bind g = x.bind (fun x => (f x).bind g) := by
  induction x with
  | pure a => rfl
  | liftBind op cont ih =>
    simp [FreeM.bind,  ← pure_eq_purePure] at *
    simp [ih]

instance : Bind (FreeM F) where bind := .bind

@[simp]
theorem bind_eq_bindBind {α β : Type w} :
    Bind.bind = (FreeM.bind : FreeM F α → _ → FreeM F β) := rfl

/-- Map a function over a `FreeM` monad. -/
def map (f : α → β) : FreeM F α → FreeM F β
  | .pure a => .pure (f a)
  | .liftBind op cont => .liftBind op (fun z => FreeM.map f (cont z))

instance: Functor (FreeM F) where
  map := .map

@[simp]
theorem map_eq_functorMap {α β : Type w} : Functor.map = FreeM.map (F := F) (α := α) (β := β) := rfl

/-- Lift an operation from the effect signature `f` into the `FreeM f` monad. -/
def lift (op : F ι) : FreeM F ι :=
  .liftBind op pure

attribute [-simp] liftBind.injEq liftBind.sizeOf_spec

/-- Rewrite `lift` to the constructor form so that simplification stays in constructor
normal form. -/
@[simp]
lemma lift_def (op : F ι) :
    (lift op : FreeM F ι) = liftBind op pure := rfl

@[simp]
lemma map_lift {ι : Type u} {β : Type u} (f : ι → β) (op : F ι) :
    (f <$> (lift op : FreeM F ι)) =
      liftBind op (fun z : ι => (pure (f z) : FreeM F β)) := rfl

/-- `.pure a` followed by `bind` collapses immediately. -/
@[simp]
lemma bind_pure_left (a : α) (f : α → FreeM F β) :
    (.pure a : FreeM F α).bind f = f a := rfl

@[simp]
lemma bind_pure_right {α : Type u} (x : FreeM F α) :
    x.bind (.pure) = x := by
  induction x with
  | pure a       => rfl
  | liftBind op k ih =>
      simp [FreeM.bind, ih]

/-- Collapse a `.bind` that follows a `liftBind` into a single `liftBind` -/
@[simp]
lemma bind_liftBind_dot {α β γ : Type u} (op : F α) (cont : α → FreeM F β)
    (f : β → FreeM F γ) :
    (liftBind op cont).bind f = liftBind op (fun x => (cont x).bind f) := rfl


instance : LawfulFunctor (FreeM F) where
  map_const := rfl
  id_map x := by
    induction x with
    | pure a => rfl
    | liftBind op cont ih =>
      simp_all [map_eq_functorMap, lift_def, map, ih]
  comp_map g h x := by
    induction x with
    | pure a => rfl
    | liftBind op cont ih =>
      simp_all [map_eq_functorMap, lift_def, map, ih]

instance : Monad (FreeM F) where

instance : LawfulMonad (FreeM F) := LawfulMonad.mk'
  (bind_pure_comp := fun f x => by
    induction x with
    | pure a => rfl
    | liftBind op cont ih =>
      simp only [FreeM.bind, bind_eq_bindBind, map_eq_functorMap, pure_eq_purePure, map] at *
      simp only [ih]
  )
  (id_map := id_map)
  (pure_bind := fun x f => rfl)
  (bind_assoc := FreeM.bind_assoc)

/--
Interpret a `FreeM f` computation into any monad `m` by providing an interpretation
function for the effect signature `f`.

This function defines the *canonical interpreter* from the free monad `FreeM f` into the target
monad `m`. It is the unique monad morphism that extends the effect handler
`interp : ∀ {β}, F β → M β` via the universal property of `FreeM`.
-/
protected def liftM {M : Type u → Type w} [Monad M] {α : Type u} :
    FreeM F α → ({β : Type u} → F β → M β) → M α
  | .pure a, _ => pure a
  | .liftBind op cont, interp => interp op >>= fun result => (cont result).liftM interp

@[simp]
lemma liftM_pure {M : Type u → Type w} [Monad M] {α : Type u}
    (interp : {β : Type u} → F β → M β) (a : α) :
    pure a = (pure a : FreeM F α).liftM interp := rfl

@[simp]
lemma liftM_liftBind {M : Type u → Type w} [Monad M] {α β : Type u}
    (interp : {γ : Type u} → F γ → M γ) (op : F β) (cont : β → FreeM F α) :
    (do let b ← interp op; (cont b).liftM interp) = (liftBind op cont).liftM interp := by
  rfl

@[simp]
lemma liftM_bind {M : Type u → Type w} [Monad M] [LawfulMonad M] {α β : Type u}
    (interp : {β : Type u} → F β → M β) (x : FreeM F α) (f : α → FreeM F β) :
    (do let a ← x.liftM interp; (f a).liftM interp) = (x >>= f : FreeM F β).liftM interp := by
  induction x generalizing f with
  | pure a => simp only [← pure_eq_purePure, ← liftM_pure, pure_bind, bind, FreeM.bind]
  | liftBind op cont ih =>
    simp_rw [bind_eq_bindBind] at *
    rw [FreeM.bind, ← liftM_liftBind, ← liftM_liftBind, bind_assoc]
    simp_rw [ih]

@[simp]
lemma liftM_lift {M : Type u → Type w} [Monad M] [LawfulMonad M] {α : Type u}
    (interp : {β : Type u} → F β → M β) (op : F α) :
    (FreeM.liftBind op FreeM.pure).liftM interp = interp op := by
  simp [← pure_eq_purePure, ← liftM_liftBind, ← liftM_pure]

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
structure ExtendsHandler {M : Type u → Type w} [Monad M] {α : Type u}
    (f : {ι : Type u} → F ι → M ι)
    (g : FreeM F α → M α) : Prop where
  apply_pure : ∀ a, g (pure a) = pure a
  apply_liftBind : ∀ {ι} (op : F ι) (k : ι → FreeM F α),
    g (liftBind op k) = f op >>= fun x => g (k x)

/--
The universal property of the free monad `FreeM`. That is, `liftM f` is the unique interpreter that
extends the effect handler `f` to interpret `FreeM F` computations in monad `M`.
-/
theorem extendsHandler_iff
{F : Type u → Type v} {m : Type u → Type w} [Monad m] {α : Type u}
    (f : {ι : Type u} → F ι → m ι) (g : FreeM F α → m α) :
    ExtendsHandler @f g ↔ g = (·.liftM @f) := by
  refine ⟨fun h => funext fun x => ?_, fun h => ?_⟩
  · induction x with
    | pure a => exact h.apply_pure a
    | liftBind op cont ih =>
      rw [← liftM_liftBind, h.apply_liftBind]
      simp [ih]
  · subst h
    exact ⟨fun _ => rfl, fun _ _ => rfl⟩

inductive Expr where
  | val : Int → Expr
  | var : String → Expr
  | add : Expr → Expr → Expr
  | div : Expr → Expr → Expr

abbrev Env := List (String × Int)

inductive StateEff : Type → Type where
  | Get : StateEff Env
  | Put : Env → StateEff Unit

inductive ErrorEff : Type → Type where
  | Fail : String → ErrorEff Unit

inductive TraceEff : Type → Type where
  | Log : String → TraceEff Unit

inductive FSum (F G : Type → Type) (α : Type) where
  | inl : F α → FSum F G α
  | inr : G α → FSum F G α

infixl:50 "⊕" => FSum

abbrev Eff := StateEff ⊕ (ErrorEff ⊕ TraceEff)

def getEnv : FreeM Eff Env :=
  FreeM.lift (FSum.inl StateEff.Get)

def putEnv (e : Env) : FreeM Eff Unit :=
  FreeM.lift (FSum.inl (StateEff.Put e))

def fail (msg : String) : FreeM Eff Unit :=
  FreeM.lift (FSum.inr (FSum.inl (ErrorEff.Fail msg)))

def log (msg : String) : FreeM Eff Unit :=
  FreeM.lift (FSum.inr (FSum.inr (TraceEff.Log msg)))

def ex : FreeM Eff Int := do
  log "Starting"
  putEnv [("x", 10)]
  let env ← getEnv
  match env.find? (·.fst = "x") with
  | some (_, x) => pure (x + 1)
  | none => do fail "x not found"; pure 0

abbrev Trace := List String

/-- Interpret `Eff` operations into the target monad. -/
def effInterp : {α : Type} → Eff α → Env → Trace → Except String (α × Env × Trace)
  | _, .inl StateEff.Get => fun env trace => .ok (env, env, trace)
  | _, .inl (StateEff.Put newEnv) => fun _ trace => .ok ((), newEnv, trace)
  | _, .inr (.inl (ErrorEff.Fail msg)) => fun _ _ => .error msg
  | _, .inr (.inr (TraceEff.Log msg)) => fun env trace => .ok ((), env, trace ++ [msg])

/-- Catamorphism for the `FreeM` monad. The unique morphism from the initial algebra
to any other algebra of the endofunctor `FreeM F`.
-/
def cataFreeM {F : Type u → Type v} {α β : Type w}
  (pureCase : α → β)
  (bindCase : {ι : Type u} → F ι → (ι → β) → β)
  : FreeM F α → β
| .pure a => pureCase a
| .liftBind op k => bindCase op (fun x => cataFreeM pureCase bindCase (k x))

abbrev EffAction (α : Type) := Env → Trace → Except String (α × Env × Trace)

/-- Pure case of the algebra. -/
def effPure {α} (a : α) : EffAction α :=
  fun env tr => .ok (a, env, tr)

/-- Bind case of the algebra. -/
def effStep {α} :
    {ι : Type} → Eff ι → (ι → EffAction α) → EffAction α
  | _, .inl StateEff.Get,        k => fun env tr => k env env tr
  | _, .inl (StateEff.Put σ),    k => fun _   tr => k () σ tr
  | _, .inr (.inl (ErrorEff.Fail msg)), _ =>
        fun _ _  => .error msg
  | _, .inr (.inr (TraceEff.Log msg)), k =>
        fun env tr => k () env (tr ++ [msg])

def runEff {α} : FreeM Eff α → EffAction α :=
  cataFreeM effPure effStep

/-
Operational semantics for the AST
-/
inductive EvalRel : Expr → Env → Trace → Except String (Int × Env × Trace) → Prop where
| val :
    ∀ n env trace,
    EvalRel (.val n) env trace (.ok (n, env, trace))
| var_found :
    ∀ x env trace v,
    env.find? (·.fst = x) = some (x, v) →
    EvalRel (.var x) env trace (.ok (v, env, trace))
| var_missing :
    ∀ x env trace,
    env.find? (·.fst = x) = none →
    EvalRel (.var x) env trace (.error s!"unbound variable {x}")
| add :
    ∀ e1 e2 env trace₁ trace₂ trace₃ v1 v2 env₂ env₃,
    EvalRel e1 env trace₁ (.ok (v1, env₂, trace₂)) →
    EvalRel e2 env₂ trace₂ (.ok (v2, env₃, trace₃)) →
    EvalRel (.add e1 e2) env trace₁ (.ok (v1 + v2, env₃, trace₃))
| div_ok :
    ∀ e1 e2 env trace₁ trace₂ trace₃ v1 v2 env₂ env₃,
    v2 ≠ 0 →
    EvalRel e1 env trace₁ (.ok (v1, env₂, trace₂)) →
    EvalRel e2 env₂ trace₂ (.ok (v2, env₃, trace₃)) →
    EvalRel (.div e1 e2) env trace₁ (.ok (v1 / v2, env₃, trace₃))
| div_zero :
    ∀ e1 e2 env trace₁ trace₂ trace₃ v1 v2 env₂ env₃,
    v2 = 0 →
    EvalRel e1 env trace₁ (.ok (v1, env₂, trace₂)) →
    EvalRel e2 env₂ trace₂ (.ok (v2, env₃, trace₃)) →
    EvalRel (.div e1 e2) env trace₁ (.error "divide by zero")

def eval : Expr → FreeM Eff Int
  | .val n => pure n
  | .var x => do
      let env ← getEnv
      match env.find? (·.fst = x) with
      | some (_, v) => pure v
      | none => do
          fail s!"unbound variable {x}"
          pure 0
  | .add e1 e2 => do
      let v1 ← eval e1
      let v2 ← eval e2
      pure (v1 + v2)
  | .div e1 e2 => do
      let v1 ← eval e1
      let v2 ← eval e2
      if v2 = 0 then
        fail "divide by zero"
        pure 0
      else
        pure (v1 / v2)

-- correctness (catamorphism-based)

/-- Running a `bind` when the prefix succeeds. -/
theorem runEff_bind_ok {α β}
    {p : FreeM Eff α} {k : α → FreeM Eff β}
    {env env' : Env} {tr tr' : Trace} {v : α} (h : runEff p env tr = .ok (v, env', tr')) :
    runEff (p >>= k) env tr = runEff (k v) env' tr' := by
  revert env env' tr tr' v
  induction p <;> simp [runEff, bind, cataFreeM] at *
  · case pure a =>
    intros env env' tr tr' v h
    simp [effPure] at h
    rw [h.1, h.2.1, h.2.2]
  · case liftBind ι op cont ih =>
    intros env env' tr tr' v h
    cases op
    · case inl s =>
      cases s
      case Get => simp [effStep] at *; apply ih; exact h
      case Put => simp [effStep] at *; apply ih; exact h
    · case inr s =>
      cases s
      case inl s =>
        cases s
        case Fail => simp [effStep] at *
      case inr s =>
        cases s
        case Log => simp [effStep] at *; apply ih; exact h

/-- Running a `bind` when the prefix raises an error. -/
theorem runEff_bind_err {α β}
    {p : FreeM Eff α} {k : α → FreeM Eff β}
    {env : Env} {tr : Trace} {msg : String} :
  runEff p env tr = .error msg →
  runEff (p >>= k) env tr = .error msg := by
  revert env tr msg
  induction p <;> simp [runEff, bind, cataFreeM] at *
  · case pure a => intros env tr msg h; simp [effPure] at *;
  · case liftBind ι op cont ih =>
    intros env tr msg h
    cases op
    · case inl s =>
      cases s
      case Get => simp [effStep] at *; apply ih; exact h
      case Put => simp [effStep] at *; apply ih; exact h
    · case inr s =>
      cases s
      case inl s =>
        cases s
        case Fail msg' =>
        simp [effStep] at h
        subst h
        simp [FreeM.bind, runEff, cataFreeM, effStep]
      case inr s =>
        cases s
        case Log msg' => simp [effStep] at *; apply ih; exact h

/-- Correctness of the evaluator, with respect to the operational semantics. -/
theorem runEff_eval_correct (e : Expr) (env : Env) (trace : Trace)
    (res : Except String (Int × Env × Trace))
    (h : EvalRel e env trace res) :
    runEff (eval e) env trace = res := by
    induction' h
    · case val z env trace =>
      simp [eval, pure_eq_purePure, runEff, cataFreeM, effPure]
    · case var_found x env trace v h =>
      simp [runEff, eval, getEnv, bind_pure_comp, lift_def, cataFreeM, effStep, h, effPure]
    · case var_missing x env trace h =>
      simp [runEff, eval, bind, getEnv, fail, lift_def, cataFreeM, effStep, h]
    · case add e₁ e₂ env trace₁ trace₂ trace₃ v1 v2 env₂ env₃ h₁ h₂ ih₁ ih₂ =>
      simp [eval, bind]
      have step₁ := runEff_bind_ok (p := eval e₁ ) (k := fun v1 => do
        let v2 ← eval e₂
        pure (v1 + v2)) ih₁
      simp [bind] at step₁; simp [step₁]
      have step₂ := runEff_bind_ok (p := eval e₂) (k := fun v2 => pure (v1 + v2)) ih₂
      simp [bind] at step₂; simp [step₂]; congr
    · case div_ok e₁ e₂ env trace₁ trace₂ trace₃ v₁ v₂ env₂ env₃ v₂_ne_0 h₁ h₂ ih₁ ih₂  =>
      simp [eval, bind]
      have step₁ := runEff_bind_ok (p := eval e₁) (k := fun v1 => do
        let v2 ← eval e₂
        if v2 = 0 then do fail "divide by zero"; pure 0 else pure (v1 / v2)) ih₁
      simp [bind] at step₁; simp [step₁]
      have step₂ := runEff_bind_ok (p := eval e₂) (k := fun v₂ =>
        if v₂ = 0 then do fail "divide by zero"; pure 0 else pure (v₁ / v₂)) ih₂
      simp [bind] at step₂; simp [step₂, v₂_ne_0]
      congr
    · case div_zero e₁ e₂ env' trace₁ trace₂ trace₃ v₁ v₂ env₂ env₃ v₂_ne_0 h₁ h₂ ih₁ ih₂ =>
      simp [eval, bind]
      have step₁ := runEff_bind_ok (p := eval e₁) (k := fun v₁ => do let v₂ ← eval e₂; if v₂ = 0 then fail "divide by zero"; pure 0 else pure (v₁ / v₂)) ih₁
      simp [bind] at step₁; simp [step₁]
      have step₂ := runEff_bind_ok (p := eval e₂) (k := fun v₂ => if v₂ = 0 then (do fail "divide by zero"; pure 0) else pure (v₁ / v₂)) ih₂
      simp [bind] at step₂; simp [step₂, v₂_ne_0]
      simp [pure, fail, lift, runEff]
      congr
