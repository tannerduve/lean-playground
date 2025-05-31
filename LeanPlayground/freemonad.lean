inductive Free (f : Type -> Type) (a : Type) where
| pure : a -> Free f a
| bind : ∀ x, f x -> (x -> Free f a) -> Free f a

/-
Map will take a function f : α → β and type constructor F : Type u → Type v and return a
function Free Ff : Fα → Fβ
-/
def Free.map {α β : Type} (F : Type → Type) (f : α → β) : Free F α → Free F β :=
λ FFa =>
match FFa with
| pure a => Free.pure (f a)
| bind X Fx k => Free.bind X Fx (λ z => map F f (k z))

instance : Functor (Free F) where
map := Free.map F

instance : LawfulFunctor (Free F) where
map_const := by
  intro α β
  simp [Functor.mapConst, Functor.map]
id_map := by
  intro α x
  simp [Functor.map]
  induction x
  case pure a =>
    simp [Free.map]
  case bind X Fx f ih =>
    simp [Free.map, ih]
comp_map := by
  intro α β γ g h x
  simp [Functor.map]
  induction x
  case pure a =>
    simp [Free.map]
  case bind X Fx f ih =>
    simp [Free.map, ih]

/--
Now we define our pure and bind morphisms for the Free Monad.
-/

def bindFree {a b : Type} (F : Type → Type) (x : Free F a) (f : a → Free F b) : Free F b :=
match x with
| .pure a => f a
| .bind X Fx k => .bind X Fx (λ z => bindFree F (k z) f)

instance FreeMonad (F : Type → Type) : Monad (Free F) where
  pure := Free.pure
  bind := bindFree F

/-
class LawfulMonad (m : Type u → Type v) [Monad m] : Prop extends LawfulApplicative m where
  /--
  A `bind` followed by `pure` composed with a function is equivalent to a functorial map.

  This means that `pure` really is pure after a `bind` and has no effects.
  -/
  bind_pure_comp (f : α → β) (x : m α) : x >>= (fun a => pure (f a)) = f <$> x
  /--
  A `bind` followed by a functorial map is equivalent to `Applicative` sequencing.

  This means that the effect sequencing from `Monad` and `Applicative` are the same.
  -/
  bind_map       {α β : Type u} (f : m (α → β)) (x : m α) : f >>= (. <$> x) = f <*> x
  /--
  `pure` followed by `bind` is equivalent to function application.

  This means that `pure` really is pure before a `bind` and has no effects.
  -/
  pure_bind      (x : α) (f : α → m β) : pure x >>= f = f x
  /--
  `bind` is associative.

  Changing the nesting of `bind` calls while maintaining the order of computations results in an
  equivalent computation. This means that `bind` is not doing more than data-dependent sequencing.
  -/
  bind_assoc     (x : m α) (f : α → m β) (g : β → m γ) : x >>= f >>= g = x >>= fun x => f x >>= g
  map_pure g x    := (by rw [← bind_pure_comp, pure_bind])
  seq_pure g x    := (by rw [← bind_map]; simp [map_pure, bind_pure_comp])
  seq_assoc x g h := (by simp [← bind_pure_comp, ← bind_map, bind_assoc, pure_bind])
-/

instance : LawfulMonad (Free F) where
bind_pure_comp := by
  intro α β x y; simp [Functor.map, bind, pure]; induction y
  · case pure a => simp [bindFree, Free.map]
  · case bind X Fx k ih => simp [bindFree, Free.map, ih]
bind_map := by
  intro α β f x; simp [bind, Seq.seq]
pure_bind := by
  intro α x a f; simp [bind, pure, bindFree]
bind_assoc := by
  intro α β γ x f g; simp [bind]; induction x
  case pure a => simp [bindFree, Free.map]
  case bind X Fx k ih => simp [bindFree, Free.map, ih]
seqLeft_eq := by
  intro α β x y; simp [Functor.map, SeqLeft.seqLeft, Seq.seq]; induction x
  case pure a =>
    simp [bindFree, Free.map]
    induction y
    case pure b => simp [bindFree, Free.map]
    case bind X Fy k ih => simp [bindFree, Free.map, ih]
  case bind X Fx k ih => simp [bindFree, Free.map, ih]
seqRight_eq := by
  intro α β x y; simp [Functor.map, bindFree, Free.map]; induction x
  case pure a =>
    simp [bindFree, Free.map]
    induction y
    case pure b => simp [SeqRight.seqRight, Seq.seq, Functor.map, bindFree, Free.map]
    case bind X Fy k ih =>
      simp [SeqRight.seqRight, Seq.seq, Functor.map, bindFree, Free.map, ih] at ih ⊢
      apply funext; intro x; exact ih x
  case bind X Fx k ih =>
    simp [Free.map, Seq.seq, bindFree, Functor.map, SeqRight.seqRight] at ih ⊢
    apply funext; intro x; exact ih x
pure_seq := by
  intro α β f x; simp [Seq.seq, Functor.map, pure, bindFree]

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

def getEnv : Free Eff Env :=
  Free.bind _ (FSum.inl StateEff.Get) Free.pure

def putEnv (e : Env) : Free Eff Unit :=
  Free.bind _ (FSum.inl (StateEff.Put e)) Free.pure

def fail (msg : String) : Free Eff Unit :=
  Free.bind _ (FSum.inr (FSum.inl (ErrorEff.Fail msg))) Free.pure

def log (msg : String) : Free Eff Unit :=
  Free.bind _ (FSum.inr (FSum.inr (TraceEff.Log msg))) Free.pure

def ex : Free Eff Int := do
  log "Starting"
  putEnv [("x", 10)]
  let env ← getEnv
  match env.find? (·.fst = "x") with
  | some (_, x) => pure (x + 1)
  | none => do fail "x not found"; pure 0

abbrev Trace := List String

def run {α : Type} : Free Eff α → Env → Trace → Except String (α × Env × Trace)
  | .pure a, env, trace => .ok (a, env, trace)
  | .bind _ fx k, env, trace =>
    match fx with
    | .inl sfx =>
      match sfx with
      | StateEff.Get => run (k env) env trace
      | StateEff.Put newEnv => run (k ()) newEnv trace
    | .inr sfx =>
      match sfx with
      | .inl efx =>
        match efx with
        | ErrorEff.Fail msg => .error msg
      | .inr tfx =>
        match tfx with
        | TraceEff.Log msg => run (k ()) env (trace ++ [msg])

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

def eval : Expr → Free Eff Int
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


theorem run_bind_ok {α β}
    {p : Free Eff α} {k : α → Free Eff β}
    {env env' : Env} {tr tr' : Trace} {v : α} :
  run p env tr = .ok (v, env', tr') →
  run (p >>= k) env tr = run (k v) env' tr' := by
  intro h
  -- cases p exhaustively and rewrite with h; simp finishes.
  revert env env' tr tr' v
  induction p <;> simp [run, bind, bindFree] at *
  · case pure a =>
    intro env env' tr h; simp [h]
  · case bind X Fx k' ih =>
    intro env env' tr tr' a h
    cases Fx
    case inl sfx =>
      cases sfx
      case Get => simp [run, bindFree, ih] at *; apply ih; exact h
      case Put newEnv =>
        simp [run, bindFree, ih] at *; apply ih; exact h
    case inr sfx =>
      cases sfx
      case inl efx =>
        cases efx
        case Fail msg => simp [run, bindFree, ih] at *
      case inr tfx =>
        cases tfx
        case Log msg => simp [run, bindFree, ih] at *; apply ih; exact h

/-- Running a `bind` when the prefix raises an error. -/
theorem run_bind_err {α β}
    {p : Free Eff α} {k : α → Free Eff β}
    {env : Env} {tr : Trace} {msg : String} :
  run p env tr = .error msg →
  run (p >>= k) env tr = .error msg := by
  intro h
  revert env tr msg
  induction p <;> simp [run, bind, bindFree] at *
  case bind X Fx k' ih =>
    intro env tr msg h; cases Fx
    case inl sfx =>
      cases sfx
      case Get => simp [run, bindFree, ih] at *; apply ih; exact h
      case Put newEnv => simp [run, bindFree, ih] at *; apply ih; exact h
    case inr sfx =>
      cases sfx
      case inl efx =>
        cases efx
        case Fail msg' =>
          simp [run, bindFree, ih] at *; exact h
      case inr tfx =>
        cases tfx
        case Log msg' => simp [run, bindFree, ih] at *; apply ih; exact h

-- correctness
theorem eval_correct :
  ∀ (e : Expr) (env : Env) (trace : Trace) (res : Except String (Int × Env × Trace)),
    EvalRel e env trace res →
    run (eval e) env trace = res := by
    intro e env trace res h
    induction h
    case val n env' trace' =>
      simp [eval, pure, run]
    case var_found x env' trace' v hfind =>
      simp [eval, getEnv, run, bind, bindFree, FSum.inl, hfind]
    case var_missing x' env' t hfind =>
      simp [eval, getEnv, run, bind, bindFree, FSum.inl, hfind, Eff, fail, FSum.inr]
    case add e1 e2 env' trace₁ trace₂ trace₃ v1 v2 env₂ env₃ he1 he2 ih₁ ih₂ =>
      simp [eval, bind]
      have step₁ :=
      run_bind_ok
        (p := eval e1)
        (k := fun v1 : Int => do
          let v2 ← eval e2; pure (v1 + v2))
        ih₁
      simp [bind] at step₁; simp [step₁]
      have step₂ := run_bind_ok
        (p := eval e2)
        (k := fun v2 : Int => pure (v1 + v2))
        ih₂
      simp [bind] at step₂; simp [step₂, run]
    case div_ok e1 e2 env' trace₁ trace₂ trace₃ v1 v2 env₂ env₃ hne he1 he2 ih₁ ih₂ =>
      simp [eval, bind]
      have step₁ :=
          run_bind_ok
            (p := eval e1)
            (k := fun v1 : Int => do
              let v2 ← eval e2
              if v2 = 0 then
                fail "divide by zero"
                pure 0
              else
                pure (v1 / v2))
            ih₁
      simp [bind] at step₁; simp [step₁]
      have step₂ :=
        run_bind_ok
          (p := eval e2)
          (k := fun v2 : Int => do
            if v2 = 0 then
              fail "divide by zero"
              pure 0
            else
              pure (v1 / v2))
          ih₂
      simp [bind] at step₂; simp [step₂, hne]; simp [run]
    case div_zero e1 e2 env' trace₁ trace₂ trace₃ v1 v2 env₂ env₃ heq he1 he2 ih₁ ih₂ =>
      simp [eval, bind]
      have step₁ :=
        run_bind_ok
          (p := eval e1)
          (k := fun v1 : Int => do
            let v2 ← eval e2
            if v2 = 0 then
              fail "divide by zero"
              pure 0
            else
              pure (v1 / v2))
          ih₁
      simp [bind] at step₁; simp [step₁]
      have step₂ :=
        run_bind_ok
          (p := eval e2)
          (k := fun v2 : Int => do
            if v2 = 0 then
              fail "divide by zero"
              pure 0
            else
              pure (v1 / v2))
          ih₂
      simp [bind] at step₂; simp [step₂, heq]; simp [fail, run, bindFree]
