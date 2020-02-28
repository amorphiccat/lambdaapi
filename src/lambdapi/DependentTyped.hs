module LambdaPi.DependentTyped where

import Control.Monad
import Debug.Trace

data TermInfer
    = Ann TermCheck TermCheck 
    | Star
    | Pi TermCheck TermCheck
    | Bound Int
    | Free Name
    | TermInfer :@ TermCheck
    deriving (Show, Eq)

data TermCheck
    = Inf TermInfer
    | Lam TermCheck
    deriving (Show, Eq)

data Name
    = Global String
    | Local Int
    | Quote Int
    deriving (Show, Eq)

data Value
    = VLam (Value -> Value)
    | VStar
    | VPi Value (Value -> Value)
    | VNeutral Neutral

data Neutral 
    = NFree Name
    | NApp Neutral Value

vfree :: Name -> Value
vfree = VNeutral . NFree

type Env = [Value]

evalInfer :: TermInfer -> Env -> Value
evalInfer Star env = VStar
evalInfer (Pi t t') env = VPi (evalCheck t env) (\x -> evalCheck t' (x:env))
evalInfer (Ann e _) env = evalCheck e env
evalInfer (Free x) env = vfree x
evalInfer (Bound i) env = env !! i
evalInfer (e1 :@ e2) env = vapp (evalInfer e1 env) (evalCheck e2 env)

vapp :: Value -> Value -> Value
vapp (VLam f) v = f v
vapp (VNeutral n) v = VNeutral (NApp n v)

evalCheck :: TermCheck -> Env -> Value
evalCheck (Inf i) env = evalInfer i env
evalCheck (Lam e) env = VLam (\x -> evalCheck e (x:env))

type Type = Value
type Context = [(Name, Type)]

type Result a = Either String a

throwError :: String -> Result a
throwError = Left


typeInfer0 :: Context -> TermInfer -> Result Type
typeInfer0 = typeInfer 0

typeInfer :: Int -> Context -> TermInfer -> Result Type
typeInfer i ctx (Ann e p) = do 
    typeCheck i ctx p VStar
    let t = evalCheck p []
    typeCheck i ctx e t
    return t
typeInfer i ctx (Pi p p') = do
    typeCheck i ctx p VStar
    let t = evalCheck p []
    typeCheck (i+1) ((Local i, t): ctx) 
        (substCheck 0 (Free (Local i)) p') VStar
    return VStar
typeInfer i ctx Star = return VStar
typeInfer i ctx (Free x) =
    case lookup x ctx of
        Just t -> return t 
        Nothing -> throwError "unknown identifier"
typeInfer i ctx (e :@ e') = do
    s <- typeInfer i ctx e
    case s of 
        VPi t t' -> do
            typeCheck i ctx e' t
            return (t' (evalCheck e' []))
        _ -> throwError "illegal application"

typeCheck :: Int -> Context -> TermCheck -> Type -> Result ()
typeCheck i ctx (Inf e) v = do
    v' <- typeInfer i ctx e 
    unless (quote0 v == quote0 v') $ throwError "type mismatch"
typeCheck i ctx (Lam e) (VPi t t') =
    typeCheck (i+1) ((Local i, t):ctx) (substCheck 0 (Free (Local i)) e) (t' (vfree (Local i)))
typeCheck i ctx e t = throwError "type mismatch"

substInfer :: Int -> TermInfer -> TermInfer -> TermInfer
substInfer i r Star = Star
substInfer i r (Pi t t') = Pi (substCheck i r t) (substCheck (i+1) r t')
substInfer i r (Ann e t) = Ann (substCheck i r e) t
substInfer i r (Bound j) = if i == j then r else Bound j
substInfer i r (Free y) = Free y
substinfer i r (e :@ e') = substInfer i r e :@ substCheck i r e'

substCheck :: Int -> TermInfer -> TermCheck -> TermCheck
substCheck i r (Inf e) = Inf (substInfer i r e)
substCheck i r (Lam e) = Lam (substCheck (i+1) r e)

quote0 :: Value -> TermCheck
quote0 = quote 0

quote :: Int -> Value -> TermCheck
quote i VStar = Inf Star
quote i (VPi v f) = Inf (Pi (quote i v) (quote (i+1) (f (vfree (Quote i)))))
quote i (VLam f) = Lam (quote (i+1) (f (vfree (Quote i))))
quote i (VNeutral n) = Inf (neutralQuote i n)

neutralQuote :: Int -> Neutral -> TermInfer
neutralQuote i (NFree x) = boundfree i x
neutralQuote i (NApp n v) = neutralQuote i n :@ quote i v

boundfree :: Int -> Name -> TermInfer
boundfree i (Quote k) = Bound (i-k-1)
boundfree i x = Free x

id' = Lam (Inf (Bound 0))
const' = Lam (Lam (Inf (Bound 1)))

{-
tfree a = TFree (Global a)
free x = Inf (Free (Global x))

term1 = Ann id' (tfree "a" :-> tfree "a") :@ free "y"
term2 = Ann const' ((tfree "b" :-> tfree "b") :-> (tfree "a" :-> (tfree "b" :-> tfree "b")))
term3 = term2 :@ id' :@ free "y"

env1 = [(Global "y", HasType (tfree "a")), (Global "a", HasKind Star)]
env2 = [(Global "b", HasKind Star)] ++ env1
-}

