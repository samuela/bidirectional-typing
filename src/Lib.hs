module Lib where

import Data.List (nub, intersect)
import Data.Map (Map, (!))
import qualified Data.Map as Map
import qualified Data.Set as Set
-- import Debug.Trace (trace)

type Id = String
type AnnoTypeId = String

newtype Loc = Loc Integer
  deriving (Show, Eq, Ord)

data AnnoType =
    AUnit
  | AIdent AnnoTypeId
  | ALam AnnoType AnnoType
  | AForall AnnoTypeId AnnoType
  deriving (Show, Eq, Ord)

data SourceExpr =
    SUnit Loc
  | SIdent Loc Id
  | SAnno Loc SourceExpr AnnoType
  | SLam Loc Id SourceExpr
  | SApp Loc SourceExpr SourceExpr
  deriving (Show, Eq, Ord)

-- A convenience form of expressions that do not require source locations. These
-- are used for testing and debugging. A SimpleExpr can be converted to a
-- SourceExpr with simpleToSource.
data SimpleExpr =
    Unit
  | Ident Id
  | Anno SimpleExpr AnnoType
  | Lam Id SimpleExpr
  | App SimpleExpr SimpleExpr
  deriving (Show, Eq, Ord)

data Expr =
    EUnit Loc
  | EIdent Loc Id
  | EAnno Loc Expr Type
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

newtype TypeId = TypeId Integer
  deriving (Show, Eq, Ord)

data Type =
    TUnit
  | TIdent TypeId
  | TLam Type Type
  deriving (Show, Eq, Ord)

data TypeStatus =
    Exists
  | Forall
  | Typed Type
  deriving (Show, Eq, Ord)

data TypeEnv = TypeEnv Integer (Map Expr TypeId) (Map TypeId TypeStatus)
  deriving (Show, Eq, Ord)

emptyTypeEnv = TypeEnv 0 Map.empty Map.empty

--------------------------------------------------------------------------------

simpleToSource :: SimpleExpr -> SourceExpr
simpleToSource se = snd $ loc 0 se
  where
    loc :: Integer -> SimpleExpr -> (Integer, SourceExpr)
    loc n Unit = (n + 1, SUnit (Loc n))
    loc n (Ident x) = (n + 1, SIdent (Loc n) x)
    loc n (Anno body at) = (n', SAnno (Loc n) body' at)
      where (n', body') = loc (n + 1) body
    loc n (Lam x body) = (n', SLam (Loc n) x body')
      where (n', body') = loc (n + 1) body
    loc n (App f a) = (n'', SApp (Loc n) f' a')
      where
        (n', f') = loc (n + 1) f
        (n'', a') = loc n' a

-- Convert a SourceExpr to a Expr by instantiating TypeIds for each of the type
-- annotation quantifiers and converting the type annotations to Types.
reduceAnnoTypes :: SourceExpr -> Maybe (Expr, TypeEnv)
reduceAnnoTypes = reduceSE emptyTypeEnv
  where
    reduceT' :: Map AnnoTypeId TypeId -> TypeEnv -> AnnoType -> Maybe (Type, TypeEnv)
    reduceT' _ tenv AUnit = Just (TUnit, tenv)
    reduceT' mapping tenv (AIdent aid) = do
      tid <- Map.lookup aid mapping
      return (TIdent tid, tenv)
    reduceT' mapping tenv (ALam a b) = do
      (typa, tenv') <- reduceT' mapping tenv a
      (typb, tenv'') <- reduceT' mapping tenv' b
      return (TLam typa typb, tenv'')
    reduceT' mapping tenv (AForall x t) = do
      let (tid, tenv') = createForall tenv
      reduceT' (Map.insert x tid mapping) tenv' t

    reduceT :: TypeEnv -> AnnoType -> Maybe (Type, TypeEnv)
    reduceT = reduceT' Map.empty

    reduceSE :: TypeEnv -> SourceExpr -> Maybe (Expr, TypeEnv)
    reduceSE tenv (SUnit loc) = Just (EUnit loc, tenv)
    reduceSE tenv (SIdent loc x) = Just (EIdent loc x, tenv)
    reduceSE tenv (SAnno loc se at) = do
      (typ, tenv') <- reduceT tenv at
      (expr, tenv'') <- reduceSE tenv' se
      return (EAnno loc expr typ, tenv'')
    reduceSE tenv (SLam loc x body) = do
      (body', tenv') <- reduceSE tenv body
      return (ELam loc x body', tenv')
    reduceSE tenv (SApp loc f a) = do
      (f', tenv') <- reduceSE tenv f
      (a', tenv'') <- reduceSE tenv' a
      return (EApp loc f' a', tenv'')

interp :: Env -> Expr -> Maybe Val
interp _ (EUnit _) = Just VUnit
interp env (EIdent _ x) = Map.lookup x env
interp env (EAnno _ body _) = interp env body
interp env (ELam _ x body) = Just (VLam env x body)
interp env (EApp _ f a) = case ((interp env f), (interp env a)) of
  (Just (VLam fenv y body), Just xval) -> interp (Map.insert y xval fenv) body
  otherwise -> Nothing

run :: Expr -> Maybe Val
run = interp Map.empty

-- TypeIds can cyclically reference each other so this is non-trivial
-- resolveTypeId :: TypeId -> TypeEnv -> Maybe Type
-- resolveTypeId = resolve []
--   where
--     resolve :: [TypeId] -> TypeId -> TypeEnv -> Maybe Type
--     resolve seen tid tenv@(TypeEnv _ _ idmap) = if tid `elem` seen
--       then Nothing
--       else case (Map.lookup tid idmap) of
--         Just (TIdent tid') -> resolve (tid:seen) tid' tenv
--         Just typ -> Just typ
--         otherwise -> Nothing

allStrings = [c : s | s <- "" : allStrings, c <- ['a'..'z']]

sanitizeTypeEnv :: TypeEnv -> TypeEnv
sanitizeTypeEnv tenv@(TypeEnv n exprmap idmap) = TypeEnv n exprmap' idmap'
  where
    newTypeId' :: [TypeId] -> TypeId -> TypeId
    newTypeId' seen tid = case (idmap ! tid) of
      Typed (TIdent tid') -> if tid `elem` seen
        -- We've reached a cycle, so we just return the minimum TypeId of the
        -- cycle
        then (minimum seen)
        else newTypeId' (tid:seen) tid'

      -- Either tid is not in idmap or it maps to an actual type, so we're done
      otherwise -> tid

    newTypeId :: TypeId -> TypeId
    newTypeId = newTypeId' []

    -- We start with TypeId 0 and we've used up to n - 1, but not yet n
    allTids = [TypeId i | i <- [0..(n - 1)]]
    newIds = [newTypeId tid | tid <- allTids]
    newIdsMap = Map.fromList (zip allTids newIds)

    -- This lookup will only fail if the exprmap is corrupted
    exprmap' = Map.fromList [(e, newIdsMap ! tid) | (e, tid) <- Map.toList exprmap]

    fixType :: Type -> Type
    fixType TUnit = TUnit
    fixType (TIdent tid) = TIdent (newIdsMap ! tid)
    fixType (TLam a b) = TLam (fixType a) (fixType b)

    fixTypeStatus :: TypeStatus -> TypeStatus
    fixTypeStatus Exists = Exists
    fixTypeStatus Forall = Forall
    fixTypeStatus (Typed typ) = Typed (fixType typ)

    idmap' = Map.fromList [(tid, fixTypeStatus (idmap ! tid))
                            -- Intersect with the keys of idmap
                            | tid <- nub (newIds `intersect` Map.keys idmap),
                            -- Avoid the remaining (trivial) cycles!
                            (Typed (TIdent tid)) /= fixTypeStatus (idmap ! tid)]

showType :: Type -> TypeEnv -> Maybe String
-- showType typ tenv@(TypeEnv _ _ idmap) | trace ("showType " ++ (show typ) ++ "\n  " ++ (show idmap)) False = undefined
showType typ tenv@(TypeEnv _ _ idmap) = do { (s, _, _) <- showType' allStrings Map.empty typ; return s }
  where
    showType' :: [String] -> Map TypeId String -> Type -> Maybe (String, [String], Map TypeId String)
    -- showType' unused labels typ | trace ("showType " ++ (show typ)) False = undefined
    showType' unused labels TUnit = Just ("1", unused, labels)
    showType' (nextId : unused) labels (TIdent x) =
      case (Map.lookup x labels) of
        -- Unlabeled TypeId
        Nothing -> case (idmap ! x) of
          -- This TypeId is bound to a type
          Typed typ -> showType' (nextId : unused) labels typ

          -- The TypeId is either an unbounded existential or a forall type
          otherwise -> return (nextId, unused, Map.insert x nextId labels)

        -- We've already labeled this TypeId
        Just s -> return (s, nextId : unused, labels)
    showType' unused labels (TLam a b) = do
      (sa, unused', labels') <- showType' unused labels a
      (sb, unused'', labels'') <- showType' unused' labels' b
      return ("(" ++ sa ++ " -> " ++ sb ++ ")", unused'', labels'')

addExprType :: Expr -> Type -> TypeEnv -> TypeEnv
addExprType expr typ (TypeEnv n exprmap idmap) = TypeEnv n' exprmap' idmap'
  where
    n' = n + 1
    exprmap' = Map.insert expr (TypeId n) exprmap
    idmap' = Map.insert (TypeId n) (Typed typ) idmap

createExistential :: TypeEnv -> (TypeId, TypeEnv)
createExistential (TypeEnv n exprmap idmap) =
  (TypeId n, TypeEnv (n + 1) exprmap (Map.insert (TypeId n) Exists idmap))

createForall :: TypeEnv -> (TypeId, TypeEnv)
createForall (TypeEnv n exprmap idmap) =
  (TypeId n, TypeEnv (n + 1) exprmap (Map.insert (TypeId n) Forall idmap))

updateTypeId :: TypeId -> TypeStatus -> TypeEnv -> TypeEnv
updateTypeId tid ts (TypeEnv n exprmap idmap) =
  TypeEnv n exprmap (Map.insert tid ts idmap)

updateExprType :: Expr -> Type -> TypeEnv -> TypeEnv
updateExprType expr typ tenv@(TypeEnv n exprmap idmap) =
  case (Map.lookup expr exprmap) of
    Nothing -> tenv
    Just tid -> updateTypeId tid (Typed typ) tenv

findIdents :: Id -> Expr -> [Expr]
findIdents _ (EUnit _) = []
findIdents x expr@(EIdent _ y)
  | (x == y) = [expr]
  | otherwise = []
findIdents x (EAnno _ body _) = findIdents x body
findIdents x (ELam _ y body)
  | (x /= y) = findIdents x body
  | otherwise = []
findIdents x (EApp _ f a) = (findIdents x f) ++ (findIdents x a)

containsTypeId :: Type -> TypeId -> Bool
containsTypeId TUnit _ = False
containsTypeId (TIdent x) tid = (x == tid)
containsTypeId (TLam a b) tid =
  containsTypeId a tid || containsTypeId b tid

subtype :: TypeEnv -> Type -> Type -> Maybe TypeEnv
-- subtype tenv@(TypeEnv n exprmap idmap) a b | trace ("subtype " ++ (show a) ++ " <: " ++ (show b) ++ "\n  " ++ (show exprmap) ++ "\n  " ++ (show idmap)) False = undefined

-- <:Var, <:Unit, and <:Exvar
subtype tenv a b | (a == b) = Just tenv

-- <:->
subtype tenv (TLam a1 b1) (TLam a2 b2) = do
  tenv' <- subtype tenv a2 a1
  tenv'' <- subtype tenv' b1 b2
  return tenv''

-- <:InstantiateL
subtype tenv@(TypeEnv _ _ idmap) (TIdent u) b = do
  case (idmap ! u) of
    -- InstLSolve
    Exists -> if containsTypeId b u
      -- Don't instantiate a cyclical type reference
      then Nothing
      else return (updateTypeId u (Typed b) tenv)

    Forall -> case b of
      TIdent v -> case (idmap ! v) of
        -- Instantiate v to be universal
        Exists -> Just (updateTypeId v Forall tenv)
        Forall -> Just tenv
        Typed typ -> subtype tenv (TIdent u) typ

      -- b must be a TUnit or TLam
      otherwise -> Nothing

    Typed utyp -> subtype tenv utyp b

-- <:InstantiateR
subtype tenv@(TypeEnv _ _ idmap) a (TIdent u) = do
  case (idmap ! u) of
    -- InstRSolve
    Exists -> if containsTypeId a u
      -- Don't instantiate a cyclical type reference
      then Nothing
      else return (updateTypeId u (Typed a) tenv)
    -- Forall -> return tenv
    Typed utyp -> subtype tenv a utyp

subtype _ _ _ = Nothing

-- This should maybe return Maybe (TypeId, TypeEnv)
synth :: TypeEnv -> Expr -> Maybe (Type, TypeEnv)
-- synth tenv@(TypeEnv n exprmap idmap) expr | trace ("synth " ++ (show expr) ++ "\n  " ++ (show exprmap) ++ "\n  " ++ (show idmap)) False = undefined

-- If we've already synthed a type for this expr, then re-use it
synth tenv@(TypeEnv _ exprmap idmap) expr
  | Just tid <- Map.lookup expr exprmap
  = case (idmap ! tid) of
      -- Var
      Typed typ -> Just (typ, tenv)

      -- This TypeId is a (so far) unbounded existential or a universal type, so
      -- we produce a TIdent
      otherwise -> Just (TIdent tid, tenv)

-- All EIdent expressions should be handled by Var, otherwise it's an unbound
-- identifier.
synth _ expr@(EIdent _ _) = Nothing

synth tenv expr@(EAnno _ body typ) = do
  tenv' <- check tenv body typ
  return (typ, tenv')

-- 1I=>
synth tenv expr@(EUnit _) = Just (TUnit, addExprType expr TUnit tenv)

-- ->I=>
synth tenv@(TypeEnv n exprmap idmap) expr@(ELam _ x body) = do
  -- insert x and y
  let xtid = TypeId n
  let ytid = TypeId (n + 1)
  let idents = findIdents x body
  let exprmap' = foldl (\m e -> Map.insert e xtid m) exprmap idents
  let idmap' = Map.insert xtid Exists (Map.insert ytid Exists idmap)
  let tenv' = TypeEnv (n + 2) exprmap' idmap'

  tenv'' <- check tenv' body (TIdent ytid)

  -- insert (x -> y)
  let funtyp = TLam (TIdent xtid) (TIdent ytid)
  return (funtyp, addExprType expr funtyp tenv'')

-- ->E
synth tenv@(TypeEnv n exprmap idmap) expr@(EApp _ f a) = do
  (ftyp, tenv'@(TypeEnv n' exprmap' idmap')) <- synth tenv f
  case ftyp of
    -- ->App
    TLam x y -> do
      tenv'' <- check tenv' a x
      return (y, tenv'')

    -- âApp
    TIdent tid | Exists <- idmap ! tid -> do
      -- Instantiate the function type
      let xtid = TypeId n'
      let ytid = TypeId (n' + 1)
      let idmap'' = Map.insert xtid Exists (Map.insert ytid Exists idmap')
      let tenv'' = TypeEnv (n' + 2) exprmap' idmap''
      let ftyp' = TLam (TIdent xtid) (TIdent ytid)
      let tenv''' = updateExprType f ftyp' tenv''

      -- Check a against x
      tenv'''' <- check tenv''' a (TIdent xtid)
      return (TIdent ytid, tenv'''')

    otherwise -> Nothing

check :: TypeEnv -> Expr -> Type -> Maybe TypeEnv
-- check tenv expr typ | trace ("check " ++ (show expr) ++ " against " ++ (show typ)) False = undefined

-- Sub
check tenv expr typ = do
  (typ', tenv') <- synth tenv expr
  tenv'' <- subtype tenv' typ' typ
  return tenv''

typeInfer :: SimpleExpr -> Maybe String
typeInfer sexpr = do
  let sourceExpr = simpleToSource sexpr
  (expr, tenv) <- reduceAnnoTypes sourceExpr
  (typ, tenv') <- synth tenv expr
  let sanitaryTenv = sanitizeTypeEnv tenv'
  showType typ sanitaryTenv
