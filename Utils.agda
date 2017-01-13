module Utils where

  data Id {A : Set} (a : A) : A -> Set where
    refl : Id a a

  transport : {A : Set} {B : A -> Set} {a1 a2 : A} -> Id a1 a2 -> B a1 -> B a2
  transport refl b = b


  data List (A : Set) : Set where
    [] : List A
    _::_ : A -> List A -> List A

  map : {X Y : Set} -> (X -> Y) -> List X -> List Y
  map f [] = []
  map f (x :: xs) = f x :: map f xs

  append : {X : Set} -> List X -> List X -> List X
  append [] ys = ys
  append (x :: xs) ys = x :: append xs ys

  listReturn : {X : Set} -> X -> List X
  listReturn x = x :: []

  listBind : {X Y : Set} -> List X -> (X -> List Y) -> List Y
  listBind [] f = []
  listBind (x :: xs) f = append (f x) (listBind xs f)


  data NEList (A : Set) : Set where
    [_] : A -> NEList A
    _::_ : A -> NEList A -> NEList A


  data One : Set where
    * : One


  data Sigma (A : Set) (B : A -> Set) : Set where
    _,_ : (a : A) -> (b : B a) -> Sigma A B

  fst : {A : Set} {B : A -> Set} -> Sigma A B -> A
  fst (a , b) = a

  snd : {A : Set} {B : A -> Set} -> (p : Sigma A B) -> B (fst p)
  snd (a , b) = b

  _x_ : Set -> Set -> Set
  A x B = Sigma A (\ _ -> B)


  data Zero : Set where


  data _+_ (A B : Set) : Set where
    inl : A -> A + B
    inr : B -> A + B

  +-elim : {A B : Set} {C : A + B -> Set} -> (ab : A + B) -> ((a : A) -> C (inl a)) -> ((b : B) -> C (inr b)) -> C ab
  +-elim (inl a) f g = f a
  +-elim (inr b) f g = g b
