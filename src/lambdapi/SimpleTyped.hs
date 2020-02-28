module LambdaPi.SimpleTyped where

import Control.Monad
import Debug.Trace

data TermInfer
    = Ann TermCheck Type
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

data Type 
    = TFree Name
    | Type :-> Type
    deriving (Show, Eq)

infixr 6 :->

data Value
    = VLam (Value -> Value)
    | VNeutral Neutral

data Neutral 
    = NFree Name
    | NApp Neutral Value

vfree :: Name -> Value
vfree = VNeutral . NFree

type Env = [Value]

evalInfer :: TermInfer -> Env -> Value
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

data Kind = Star
    deriving (Show)

data Info
    = HasKind Kind
    | HasType Type
    deriving (Show)

type Context = [(Name, Info)]

type Result a = Either String a

throwError :: String -> Result a
throwError = Left

kindCheck :: Context -> Type -> Kind -> Result ()
kindCheck ctx (TFree x) Star =
    case lookup x ctx of
        Just (HasKind Star) -> return ()
        Nothing -> throwError "unknown identifier"
kindCheck ctx (a :-> b) Star = do
    kindCheck ctx a Star
    kindCheck ctx b Star

typeInfer0 :: Context -> TermInfer -> Result Type
typeInfer0 = typeInfer 0

typeInfer :: Int -> Context -> TermInfer -> Result Type
typeInfer i ctx (Ann e t) = do 
    kindCheck ctx t Star
    typeCheck i ctx e t
    return t
typeInfer i ctx (Free x) =
    case lookup x ctx of
        Just (HasType t) -> return t 
        Nothing -> throwError "unknown identifier"
typeInfer i ctx (e :@ e') = do
    t <- typeInfer i ctx e
    case t of 
        t' :-> t'' -> do
            typeCheck i ctx e' t'
            return t''
        _ -> throwError "illegal application"

typeCheck :: Int -> Context -> TermCheck -> Type -> Result ()
typeCheck i ctx (Inf e) t = do
    t' <- typeInfer i ctx e 
    unless (t == t') $ trace (show (Inf e) ++ " /// " ++ show t ++ " /// " ++ show t') $ throwError "type mismatch"
typeCheck i ctx (Lam e) (t :-> t') =
    typeCheck (i+1) ((Local i, HasType t):ctx) (substCheck 0 (Free (Local i)) e) t'
typeCheck i ctx e t = trace (show e ++ " /// " ++ show t) $ throwError "type mismatch"

substInfer :: Int -> TermInfer -> TermInfer -> TermInfer
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

tfree a = TFree (Global a)
free x = Inf (Free (Global x))

term1 = Ann id' (tfree "a" :-> tfree "a") :@ free "y"
term2 = Ann const' ((tfree "b" :-> tfree "b") :-> (tfree "a" :-> (tfree "b" :-> tfree "b")))
term3 = term2 :@ id' :@ free "y"

env1 = [(Global "y", HasType (tfree "a")), (Global "a", HasKind Star)]
env2 = [(Global "b", HasKind Star)] ++ env1


