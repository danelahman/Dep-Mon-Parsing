-------------------------------------------------------
-------------------------------------------------------
---------- A dependently typed monadic parser ---------
-------- for a very simple functional language --------
-------------------------------------------------------
-------------------------------------------------------
--------------------- Danel Ahman ---------------------
-------------------------------------------------------
-------------------------------------------------------

open import Utils 


-- we parametrise the definition of the parser over the type of tokens, constants and function symbols and
-- various conversion functions from tokens to constants, functions symbols, etc.

module Parser
    (Token : Set)
    (Types : Set)
    (ConstSym : Set) 
    (FunSym : Set) 
    (tokenToType : Token -> Types + One)
    (decTypeEq : (ty1 ty2 : Types) -> (Id ty1 ty2) + (Id ty1 ty2 -> Zero))
    (tokenToConstSym : Token -> ConstSym + One)
    (typeOfConst : ConstSym -> Types) 
    (tokenToFunSym : Token -> FunSym + One)
    (typeOfFun : FunSym -> (NEList Types) x Types) where


  -- lists of tokens

  Tokens : Set
  Tokens = List Token


  -- the (fibred) parser monad and its return and bind (based on Hutton and Meijer's Monadic Parsing in Haskell)

  P : Set -> Set
  P A = Tokens -> (List (Tokens x A))

  Pf : {A B : Set} -> (A -> B) -> (P A -> P B)
  Pf f p tok = map (\ x -> (fst x) , f (snd x)) (p tok)

  return : {A : Set} -> A -> P A
  return a tok = listReturn (tok , a)

  bind : {A : Set} {B : Set} -> P A -> (A -> P B) -> P B
  bind p f tok = listBind (p tok) (\ x -> f (snd x) (fst x))


  -- syntactic sugar for the composition of the parser monad with the sima-type

  PSigma : (A : Set) -> (B : A -> Set) -> Set
  PSigma A B = P (Sigma A B)


  -- algebraic operations and generic effects for the parser monad, based on the observation that the parser monad
  -- is nothing but the tensor product of the global state monad with the lists-based nondeterminism monad
  -- for convenience, we present global state using generic effects and nondeterminism using algebraic operations

  lkp : P Tokens
  lkp toks = (toks , toks) :: []

  upd : Tokens -> P One
  upd toks1 toks2 = (toks1 , *) :: []

  or : {A : Set} -> P A -> P A -> P A
  or p1 p2 tok = append (p1 tok) (p2 tok)

  fail : {A : Set} -> P A
  fail tok = []
  

  -- some monadic parser combinators, defined using generic effects, bind and return

  parseToken : P Token
  parseToken = bind lkp
                    (\ { [] -> fail; 
                         (tok :: toks) -> bind (upd toks)
                                               (\ _ -> return tok) })

  parseAndConvert : {X : Set} -> (Token -> X) -> P X
  parseAndConvert f = bind parseToken
                           (\ tok -> return (f tok))

  parseAndTest : {X : Set} -> (Token -> X + One) -> P X
  parseAndTest f = bind (parseAndConvert f)
                        (\ p -> +-elim p (\ x -> return x) (\ _ -> fail))

  
  -- typed ASTs for a very simple functional language, given by the grammar
  --
  --   t ::= c | f t1 ... tn
  --
  -- it consists of constants and applications of function symbols to non-empty lists of terms

  mutual 
  
    data Terms : Types -> Set where
      const  : (c : ConstSym) -> Terms (typeOfConst c)
      app : (f : FunSym)   -> NEArgumentList (fst (typeOfFun f)) -> Terms (snd (typeOfFun f))

    data NEArgumentList : NEList Types -> Set where
      [_]  : {ty : Types}                      -> Terms ty -> NEArgumentList [ ty ]
      _::_ : {ty : Types} {tys : NEList Types} -> Terms ty -> NEArgumentList tys -> NEArgumentList (ty :: tys)
  
  
  -- monadic parsing of typed ASTs

  mutual
  
    {-# NO_TERMINATION_CHECK #-}

    -- the top-level parser for the whole language

    parser : PSigma Types Terms
    parser = or parseConst parseFunApp
                

    -- parsing a term of given type

    parseTermOfGivenType : (ty : Types) -> P (Terms ty)
    parseTermOfGivenType ty = 
      bind parser 
           (\ p -> +-elim {C = \ _ -> P (Terms ty)} (decTypeEq (fst p) ty) (\ q -> return (transport {B = Terms} q (snd p))) (\ _ -> fail))


    -- the sub-parser for constants

    parseConst : PSigma Types Terms
    parseConst = bind (parseAndTest tokenToConstSym) (\ c -> return (typeOfConst c , const c))


    -- parsing the non-empty list of arguments in function applications

    parseNEArgumentList : (tys : NEList Types) -> P (NEArgumentList tys)
    parseNEArgumentList [ ty ]      = bind (parseTermOfGivenType ty) (\ tm -> return [ tm ])
    parseNEArgumentList (ty :: tys) = bind (parseTermOfGivenType ty)
                                           (\ tm -> bind (parseNEArgumentList tys)
                                                         (\ tms -> return (tm :: tms)))


    -- the sub-parser for function applications

    parseFunApp : PSigma Types Terms
    parseFunApp = bind (parseAndTest tokenToFunSym)
                       (\ f -> bind (parseNEArgumentList (fst (typeOfFun f)))
                                    (\ args -> return (snd (typeOfFun f) , app f args)))
                                                 
