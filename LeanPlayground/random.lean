
def yoneda [Functor F] {a : Type} : (∀ x, ((x → a) → F x)) → F a :=
  λ g => g a id

def yoneda' [Functor F] {a : Type} : F a → (∀ x, ((a → x) → F x)) :=
  λ y _ g => Functor.map g y

inductive coyoneda (F : Type → Type) (a : Type) where
| coyoneda : ∀ x, F x → (x → a) → coyoneda F a

-- f x -> (x -> a) -> FreeFunctor f a
inductive Free (f : Type -> Type) (a : Type) where
| pure : a -> Free f a
| bind : ∀ x, f x -> (x -> Free f a) -> Free f a

inductive Cofree (f : Type → Type) (a : Type) where
| cofree : ∀ x, a → f x -> (x -> Cofree f a) → Cofree f a 


instance : Functor (coyoneda F) where
  map := 
  λ g C =>
    match C with
    | coyoneda.coyoneda x Fx f => coyoneda.coyoneda x Fx (g ∘ f)






