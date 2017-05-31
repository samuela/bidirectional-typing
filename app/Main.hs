module Main where

import Data.Map (Map)
import qualified Data.Map as Map

-- import Control.Monad (void)
import Debug.Trace (trace)

import Lib


type Id = String

newtype Loc = Loc Integer
  deriving (Show, Eq, Ord)

data Expr =
    EUnit Loc
  | EIdent Loc Id
  | ELam Loc Id Expr
  | EApp Loc Expr Expr
  deriving (Show, Eq, Ord)

-- instance Show Expr where
--   show (EUnit _) = "1"
--   show (EIdent _ (Id x)) = x
--   show (ELam _ (Id x) body) = "(" ++ x ++ " => " ++ (show body) ++ ")"
--   show (EApp _ f a) = "(" ++ (show f) ++ " " ++ (show a) ++ ")"

data Val =
    VUnit
  | VLam Env Id Expr
  deriving (Show, Eq, Ord)

type Env = Map Id Val

--------------------------------------------------------------------------------
data SimpleExpr =
    SUnit
  | SIdent Id
  | SLam Id SimpleExpr
  | SApp SimpleExpr SimpleExpr
  deriving (Show, Eq, Ord)

localizedExpr :: SimpleExpr -> Expr
localizedExpr se = snd $ loc 0 se
  where
    loc :: Integer -> SimpleExpr -> (Integer, Expr)
    loc n SUnit = (n + 1, EUnit (Loc n))
    loc n (SIdent x) = (n + 1, EIdent (Loc n) x)
    loc n (SLam x body) = (n', ELam (Loc n) x body')
      where (n', body') = loc (n + 1) body
    loc n (SApp f a) = (n'', EApp (Loc n) f' a')
      where
        (n', f') = loc (n + 1) f
        (n'', a') = loc n' a

interp :: Env -> Expr -> Maybe Val
interp _ (EUnit _) = Just VUnit
interp env (EIdent _ x) = Map.lookup x env
interp env (ELam _ x body) = Just (VLam env x body)
interp env (EApp _ f a) = case ((interp env f), (interp env a)) of
  (Just (VLam fenv y body), Just xval) -> interp (Map.insert y xval fenv) body
  otherwise -> Nothing

run :: Expr -> Maybe Val
run = interp Map.empty

newtype TypeId = TypeId Integer
  deriving (Show, Eq, Ord)

data Type =
    TUnit
  | TIdent TypeId
  | TLam Type Type
  | TUnbounded
  deriving (Show, Eq, Ord)

data TypeEnv = TypeEnv Integer (Map Expr TypeId) (Map TypeId Type)
  deriving (Show, Eq, Ord)

emptyTypeEnv = TypeEnv 0 Map.empty Map.empty

allStrings = [c : s | s <- "" : allStrings, c <- ['a'..'z']]

showType :: Type -> TypeEnv -> Maybe String
showType typ tenv@(TypeEnv _ _ idmap) = do { (s, _, _) <- showType' allStrings Map.empty typ; return s }
  where
    showType' :: [String] -> Map TypeId String -> Type -> Maybe (String, [String], Map TypeId String)
    showType' unused idents TUnit = Just ("1", unused, idents)
    showType' (nextId : unused) idents (TIdent x) = do
      xtyp <- Map.lookup x idmap
      case xtyp of
        TUnbounded -> case Map.lookup x idents of
          Just s -> return (s, unused, idents)
          Nothing -> return (nextId, unused, Map.insert x nextId idents)
        otherwise -> showType' (nextId : unused) idents xtyp
    showType' unused idents (TLam a b) = do
      (sa, unused', idents') <- showType' unused idents a
      (sb, unused'', idents'') <- showType' unused' idents' b
      return ("(" ++ sa ++ " -> " ++ sb ++ ")", unused'', idents'')

-- addIdType :: TypeId -> Type -> TypeEnv -> TypeEnv
-- addIdType tid typ (TypeEnv n exprmap idmap) = (TypeEnv n' exprmap idmap')
--   where
--     n' = n + 1
--     idmap' = Map.insert tid typ idmap

addExprType :: Expr -> Type -> TypeEnv -> TypeEnv
addExprType expr typ (TypeEnv n exprmap idmap) = TypeEnv n' exprmap' idmap'
  where
    n' = n + 1
    exprmap' = Map.insert expr (TypeId n) exprmap
    idmap' = Map.insert (TypeId n) typ idmap

updateIdType :: TypeId -> Type -> TypeEnv -> TypeEnv
updateIdType tid typ (TypeEnv n exprmap idmap) =
  TypeEnv n exprmap (Map.insert tid typ idmap)

updateExprType :: Expr -> Type -> TypeEnv -> TypeEnv
updateExprType expr typ tenv@(TypeEnv n exprmap idmap) =
  case (Map.lookup expr exprmap) of
    Nothing -> tenv
    Just tid -> updateIdType tid typ tenv

findIdents :: Id -> Expr -> [Expr]
findIdents _ (EUnit _) = []
findIdents x expr@(EIdent _ y)
  | (x == y) = [expr]
  | otherwise = []
findIdents x expr@(ELam _ y body)
  | (x /= y) = findIdents x body
  | otherwise = []
findIdents x expr@(EApp _ f a) = (findIdents x f) ++ (findIdents x a)

containsTypeId :: Type -> TypeId -> Bool
containsTypeId TUnit _ = False
containsTypeId (TIdent x) tid = (x == tid)
containsTypeId (TLam a b) tid =
  containsTypeId a tid || containsTypeId b tid
containsTypeId TUnbounded tid = False

subtype :: TypeEnv -> Type -> Type -> Maybe TypeEnv
subtype tenv a b | trace ("subtype " ++ (show a) ++ " <: " ++ (show b)) False = undefined

-- <:Var, <:Unit, and <:Exvar
subtype tenv a b | (a == b) = Just tenv

-- <:->
subtype tenv (TLam a1 b1) (TLam a2 b2) = do
  tenv' <- subtype tenv a2 a1
  tenv'' <- subtype tenv' b1 b2
  return tenv''

subtype tenv@(TypeEnv n exprmap idmap) (TIdent u) b = do
  ut <- Map.lookup u idmap
  case ut of
    -- <:InstantiateL and InstLSolve
    TUnbounded -> if containsTypeId b u
      -- Attempt to instantiate a cyclical type reference
      then Nothing
      else return (updateIdType u b tenv)
    otherwise -> subtype tenv ut b

subtype tenv@(TypeEnv n exprmap idmap) a (TIdent u) = do
  ut <- Map.lookup u idmap
  case ut of
    -- <:InstantiateR and InstRSolve
    TUnbounded -> if containsTypeId a u
      -- Attempt to instantiate a cyclical type reference
      then Nothing
      else return (updateIdType u a tenv)
    otherwise -> subtype tenv a ut

subtype _ _ _ = Nothing
-- subtype tenv a TUnbounded = Just tenv

synth :: TypeEnv -> Expr -> Maybe (Type, TypeEnv)
synth tenv@(TypeEnv n exprmap idmap) expr | trace ("synth " ++ (show expr) ++ "\n  " ++ (show exprmap) ++ "\n  " ++ (show idmap)) False = undefined

-- Var
synth tenv@(TypeEnv _ exprmap idmap) expr
  | Just tid <- Map.lookup expr exprmap
  , Just typ <- Map.lookup tid idmap
  = Just (typ, tenv)

-- 1I=>
synth tenv expr@(EUnit _) = Just (TUnit, addExprType expr TUnit tenv)

-- All EIdent expressions should be handled by Var, otherwise it's an unbound
-- identifier.
synth _ expr@(EIdent _ _) = Nothing

-- synth tenv@(TypeEnv n exprmap idmap) expr@(EIdent _ x) = do
--   tid <- Map.lookup expr exprmap
--   typ <- Map.lookup tid idmap
--   return (typ, tenv)

-- ->I=>
synth tenv@(TypeEnv n exprmap idmap) expr@(ELam _ x body) = do
  -- insert x
  let xtid = TypeId n
  let idents = findIdents x body
  let exprmap' = foldl (\m e -> Map.insert e xtid m) exprmap idents
  let idmap' = Map.insert xtid TUnbounded idmap
  let tenv' = TypeEnv (n + 1) exprmap' idmap'

  -- insert y
  (bodytyp, tenv'') <- synth tenv' body

  -- insert (x -> y)
  let funtyp = TLam (TIdent xtid) bodytyp
  return (funtyp, addExprType expr funtyp tenv'')

-- ->E
synth tenv@(TypeEnv n exprmap idmap) expr@(EApp _ f a) = do
  (ftyp, tenv'@(TypeEnv n' exprmap' idmap')) <- synth tenv f
  case (trace ("    " ++ show ftyp) ftyp) of
    -- ->App
    TLam x y -> do
      tenv'' <- check tenv' a x
      return (y, tenv'')

    -- âApp
    TUnbounded -> do
      -- Instantiate the function type
      let xtid = TypeId n'
      let ytid = TypeId (n' + 1)
      let idmap'' = Map.insert xtid TUnbounded idmap'
      let idmap''' = Map.insert ytid TUnbounded idmap''
      let tenv'' = TypeEnv (n' + 2) exprmap' idmap'''
      let ftyp' = TLam (TIdent xtid) (TIdent ytid)
      let tenv''' = updateExprType f ftyp' tenv''

      -- Check a against x
      tenv'''' <- check tenv''' a (TIdent xtid)
      return (TIdent ytid, tenv'''')

    otherwise -> Nothing

check :: TypeEnv -> Expr -> Type -> Maybe TypeEnv
check tenv expr typ | trace ("check " ++ (show expr) ++ " against " ++ (show typ)) False = undefined

-- Sub
check tenv expr typ = do
  (typ', tenv') <- synth tenv expr
  tenv'' <- subtype tenv' typ' typ
  return tenv''

typeInfer :: SimpleExpr -> Maybe String
typeInfer sexpr = do
  (typ, tenv) <- synth emptyTypeEnv (localizedExpr sexpr)
  showType typ tenv

main :: IO ()
main = someFunc
