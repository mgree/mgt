module Types where

import Data.List as L
import Data.Map as M
import Data.Set as S
import Data.Char
import Control.Monad.State

type Cname = String
type Name = String

data Vtype = Tint
           | Tchar
           | Tbool
           | Tvar Int
           | Vtype `Tfun` Vtype
           | Tc Cname Vtype Vtype
           | Forall [Vtype] Vtype
           | Tlist Vtype
           | Tcon Name [Vtype]
           | Ttop       -- For typing patterns
           | Tbot
           | TDyn
           | Tprog [Vtype]  -- Solely for performance evaluation. Shouldn't be included in normal use
           deriving (Eq,Ord)

data Sel = Lft Cname | Rgt Cname deriving Show

ve :: Vtype -> [[Sel]]
ve Tbot = []
ve Ttop = [[]]
ve (Tc nm l r) = L.map (Lft nm :) (ve l) ++ L.map (Rgt nm:) (ve r)
ve p = error $ show p

nve :: Vtype -> Int
nve (Tprog (tp:tps)) = nve tp + nve (Tprog tps)
nve (Tprog []) = 0
nve tp = length . ve $ tp

data Loc = NoNewChc | Loc Int deriving (Eq,Ord)
           

data Term = Vi Int 
          | Vb Bool 
          | Vv Name
          | Vc Char
          | App Term Term 
          | Lam Name Term         -- Normal lambdas
          | DynLam Name Term      -- Lambdas with Dyns but will not generate choices
          | CDLam Name Term       -- Lambdas with Dyns and will generate choices
          | LetList [Term] Term       -- No polymorphism, just for sharing at this time
          | Let Name Term Term
          | If Term Term Term
          | Fix Name Term
          | Binding Name Term
          | Prog [Term]    -- Solely for performance evaluation. Shouldn't be included in normal use
            deriving(Eq)



-- An approximation of functions with variational parameters

numDArgs :: Term -> Int
numDArgs (App t1 t2) = numDArgs t1 + numDArgs t2
numDArgs (Lam _ t) = numDArgs t
numDArgs (DynLam _ t) = numDArgs t
numDArgs (CDLam _ t) = 1 + numDArgs t
numDArgs (LetList ts t) = (sum . L.map numDArgs) ts + numDArgs t
numDArgs (Let _ t1 t2) = numDArgs t1 + numDArgs t2
numDArgs (If t1 t2 t3) = numDArgs t1 + numDArgs t2 + numDArgs t3
numDArgs (Fix _ t) = numDArgs t
numDArgs (Binding _ t) = numDArgs t
numDArgs (Prog ts) = (sum . L.map numDArgs) ts
numDArgs _ = 0

numFuncs' _ (App t1 t2) = numFuncs' True t1 + numFuncs' True t2
numFuncs' True (Lam _ t) = numFuncs' False t
numFuncs' True (DynLam _ t) = numFuncs' False t
numFuncs' True (CDLam _ t) = 1 + numFuncs' False t
numFuncs' False (Lam _ t) = numFuncs' False t
numFuncs' False (DynLam _ t) = numFuncs' False t
numFuncs' False (CDLam _ t) = numFuncs' False t
numFuncs' _ (LetList ts t) = (sum . L.map (numFuncs' True)) ts + numFuncs' True t
numFuncs' _ (Let _ t1 t2) = numFuncs' True t1 + numFuncs' True t2
numFuncs' _ (If t1 t2 t3) = numFuncs' True t1 + numFuncs' True t2 + numFuncs' True t3
numFuncs' _ (Fix _ t) = numFuncs' True t
numFuncs' _ (Binding _ t) = numFuncs' True t
numFuncs' _ (Prog ts) = (sum . L.map (numFuncs' True))  ts
numFuncs' _ _ = 0

numFuncs :: Term -> Int
numFuncs = numFuncs' True

numLeaves (Vi _) = 1
numLeaves (Vb _) = 1
numLeaves (Vv _) = 1
numLeaves (Vc _) = 1
numLeaves (App t1 t2) = numLeaves t1 + numLeaves t2
numLeaves (Lam _ t) = numLeaves t
numLeaves (DynLam _ t) = numLeaves t
numLeaves (CDLam _ t) = numLeaves t
numLeaves (LetList ts t) = (sum . L.map numLeaves) ts + numLeaves t
numLeaves (Let _ t1 t2) = numLeaves t1 + numLeaves t2
numLeaves (If t1 t2 t3) = numLeaves t1 + numLeaves t2 + numLeaves t3
numLeaves (Fix _ t) = numLeaves t
numLeaves (Binding _ t) = numLeaves t
numLeaves (Prog ts) = (sum . L.map numLeaves) ts

replace' idx [] t _ = (idx, [], t)
replace' idx ids lf@(Vi _) _
  | idx+1 == head ids = (idx+1, tail ids, lf)
  | True              = (idx+1, ids,      lf)
replace' idx ids lf@(Vb _) _
  | idx+1 == head ids = (idx+1, tail ids, lf)
  | True              = (idx+1, ids,      lf)
replace' idx ids lf@(Vv nm) dnames
  | idx+1 == head ids && nm `elem` dnames = (idx+1, tail ids, Let "abc_def" (Vv "+" <> i0 <> Vv nm) lf)
  | idx+1 == head ids                     = (idx+1, tail ids, lf)
  | True              = (idx+1, ids,      lf)
replace' idx ids lf@(Vc _) _
  | idx+1 == head ids = (idx+1, tail ids, lf)
  | True              = (idx+1, ids,      lf)
replace' idx ids (App t1 t2) dnames =
  let (idx1, ids1, t1n) = replace' idx ids t1 dnames
      (idx2, ids2, t2n) = replace' idx1 ids1 t2 dnames
  in (idx2, ids2, App t1n t2n)
replace' idx ids (Lam nm t) dnames = 
  let (idx1, ids1, tn) = replace' idx ids t dnames
  in  (idx1, ids1, Lam nm tn)
replace' idx ids (DynLam nm t) dnames = 
  let (idx1, ids1, tn) = replace' idx ids t dnames
  in  (idx1, ids1, DynLam nm tn)
replace' idx ids (CDLam nm t) dnames = 
  let (idx1, ids1, tn) = replace' idx ids t (nm:dnames)
  in  (idx1, ids1, CDLam nm tn)
replace' idx ids (LetList (t:ts) body) dnames =
  let (idx1, ids1, t1n) = replace' idx ids t dnames
      (idx2, ids2, LetList tsn bodyn) = replace' idx1 ids1 (LetList ts body) dnames
  in (idx2, ids2, LetList (t1n:tsn) bodyn)
replace' idx ids (LetList [] body) dnames =
  let (idx1, ids1, bodyn) = replace' idx ids body dnames
  in (idx1, ids1, LetList [] bodyn)
replace' idx ids (Let nm t1 t2) dnames =
  let (idx1, ids1, t1n) = replace' idx ids t1 dnames
      (idx2, ids2, t2n) = replace' idx1 ids1 t2 dnames
  in (idx2, ids2, Let nm t1n t2n)
replace' idx ids (If t1 t2 t3) dnames =
  let (idx1, ids1, t1n) = replace' idx ids t1 dnames
      (idx2, ids2, t2n) = replace' idx1 ids1 t2 dnames
      (idx3, ids3, t3n) = replace' idx2 ids2 t3 dnames
  in (idx3, ids3, If t1n t2n t3n)
replace' idx ids (Fix nm t) dnames = 
  let (idx1, ids1, tn) = replace' idx ids t dnames
  in  (idx1, ids1, Fix nm tn)
replace' idx ids (Binding nm t) dnames = 
  let (idx1, ids1, tn) = replace' idx ids t dnames
  in  (idx1, ids1, Binding nm tn)
replace' idx ids (Prog (t:ts)) dnames =
  let (idx1, ids1, t1n) = replace' idx ids t dnames
      (idx2, ids2, Prog tsn) = replace' idx1 ids1 (Prog ts) dnames
  in (idx2, ids2, Prog (t1n:tsn) )
replace' idx ids (Prog []) dnames = (idx, ids, Prog [] )

replace ids t = let (_ ,_ , nt ) = replace' 0 ids t [] in nt

{-
numLeaves (Fix _ t) = numLeaves t
numLeaves (Binding _ t) = numLeaves t
numLeaves (Prog ts) = (sum . L.map numLeaves) ts
-}



vv = Vv
tru = Vb True
fls = Vb False
i3 = Vi 3 
i1 = Vi 1
i2 = Vi 2
i0 = Vi 0
vc = Vc ' '
llc = vv "llc"
tbl = vv "tbl"
str = vv "str"
vi = Vi

(<>) = App 
infixl 3 <>

type Sub = M.Map Vtype Vtype
type Env = [(Name,Vtype)]

isTfun, isTchc :: Vtype -> Bool
isTfun (Tfun _ _) = True
isTfun _ = False
isTchc (Tc _ _ _) = True
isTchc _ = False

part del t = if isTfun t || isTchc t then del else ""
lpart = part "("
rpart = part ")"    

type Loc2Term = M.Map Cname Term
type ChangInf = M.Map Loc Vtype
type Log = [String]
type VIdx = Int
type DIdx = Int

type IState = (VIdx, DIdx, ChangInf, ChangInf, Log, Loc2Term)

initChg = M.empty

newVn :: State IState Vtype
newVn = do
    (vi,di,cc,oc,log,locs) <- get
    put (vi+1,di,cc,oc,log,locs)
    
    record ("Type variable " ++ show (vi) ++ " generated\n")
    return (Tvar vi)

newDn :: State IState Cname
newDn = do
    (vi,di,cc,oc,log, locs) <- get
    put (vi,di+1,cc,oc,log, locs)
    if di == 2 then newDn 
    else return [chr(di `mod` 25 + 65), chr (di `mod` 625 `div` 25 + 65), chr (di `div` 625 + 65)]
    -- else return [chr (di + 65)]

record :: String -> State IState ()
record log = do
    (vi,di,cc,oc,logs, locs) <- get
    put (vi,di,cc,oc,log:logs, locs)
    
addChg :: Loc -> Vtype -> State IState ()
addChg loc t = do
    (vi,di,cc,oc,log, locs) <- get
    put (vi,di,cc,M.insert loc t oc,log, locs)

addLoc :: Cname -> Term -> State IState ()
addLoc loc trm = do
    (vi,di,cc,oc,log, locs) <- get
    put (vi,di,cc,oc,log, M.insert loc trm locs)

idempOnce vt@(Tc n l r)
    | l == r    = l
    | otherwise = vt
idempOnce t = t

sell, selr :: Cname -> Vtype -> Vtype
sell n (Tc nc tl tr)
    | n == nc = sell n tl
    | otherwise = Tc nc (sell n tl) (sell n tr)
sell n (tl `Tfun` tr) = sell n tl `Tfun` sell n tr
sell n (Forall vars t) = Forall vars (sell n t)
sell n (Tlist t) = Tlist (sell n t)
sell n (Tcon nm typs) = Tcon nm (L.map (sell n) typs)
sell _ t = t

selr n (Tc nc tl tr)
    | n == nc = selr n tr
    | otherwise = Tc nc (selr n tl) (selr n tr)
selr n (tl `Tfun` tr) = selr n tl `Tfun` selr n tr
selr n (Forall vars t) = Forall vars (selr n t)
selr n (Tlist t) = Tlist (selr n t)
selr n (Tcon nm typs) = Tcon nm (L.map (selr n) typs)
selr _ t = t

remDeadId :: Vtype -> Vtype
remDeadId (Tc nc tl tr) = 
    let tl' = (remDeadId . sell nc) tl
        tr' = (remDeadId . selr nc) tr
    in if tl' == tr' then tl' else Tc nc tl' tr'
remDeadId (tl `Tfun` tr) = remDeadId tl `Tfun` remDeadId tr
remDeadId (Forall vars t) = Forall vars (remDeadId t)
remDeadId (Tlist t) = Tlist (remDeadId t)
remDeadId (Tcon nm typs) = Tcon nm (L.map remDeadId typs)
remDeadId t = t

-- given substitution sub and type t, calculate sub(t)
subst :: Sub -> Vtype -> Vtype
-- subst sub TDyn = TDyn
subst sub v@(Tvar _) = M.findWithDefault v v sub
subst sub (Tfun l r) = subst sub l `Tfun` subst sub r
subst sub (Tc n l r) = Tc n (subst sub l) (subst sub r)
-- subst sub (Forall bs tp) = Forall bs $ subst [item | item <- sub, not $ elem (fst item) bs] tp
subst sub (Forall bs tp) = Forall bs $ subst (L.foldr (\k m -> M.delete k m) sub bs) tp
subst sub (Tlist t) = Tlist (subst sub t)
subst sub (Tcon nm typs) = Tcon nm (L.map (subst sub) typs)
subst _ t = t

vars :: Vtype -> S.Set Vtype
vars var@(Tvar _) = S.singleton var
vars (Tc _ l r) = vars l `S.union` vars r
vars (Tfun l r) = vars l `S.union` vars r
vars (Forall bs t) = vars t `S.difference` S.fromList bs
vars (Tlist t) = vars t
vars (Tcon nm typs) = S.unions (L.map vars typs)
vars _ = S.empty

varsL ts = L.foldr (\t old -> vars t `S.union` old) S.empty ts

-- Compute free variables of type environment
fvs = varsL . L.map snd 

chcs :: Vtype -> S.Set Cname
chcs (Tc n l r) = S.singleton n `S.union` chcs l `S.union` chcs r
chcs (Tfun l r) = chcs l `S.union` chcs r
chcs (Forall bs t) = chcs t
chcs (Tlist t) = chcs t
chcs (Tcon nm typs) = S.unions (L.map chcs typs)
chcs _ = S.empty

intP :: Vtype -> Vtype -> Vtype
intP Tbot _ = Tbot
intP _ Tbot = Tbot
intP Ttop t = t
intP t Ttop = t
intP (Tc n l r) c@(Tc n' l' r')
    | n == n' = idempOnce (Tc n (intP l l') (intP r r'))
    | True    = idempOnce $ Tc n (intP l (sell n c))  (intP r (selr n c))

-- type substitution then remove dead alternatives and idempotent choices
sub >>> t = remDeadId (subst sub t)

-- Substitution compositions l \circ r
(@@) :: Sub -> Sub ->Sub
l @@ r = M.map (l >>> ) r `M.union` l

infixr @@

instance Show Vtype where
    show Tint = "Int"
    show Tbool = "Bool"
    show Tchar = "Char"
    -- show (Tvar i) = chr    (i + 97) : []
    show (Tvar i) = "Tv"++ show i
    show (l `Tfun` r) = lpart l ++ show l ++ rpart l ++ "->" ++ show r
    show (Tc n l r) = n ++ "<" ++ show l ++ "," ++ show r ++ ">"
    show (Tlist t) = "[" ++ show t ++ "]"
    show (Forall bs t) = "forall " ++ (concat . intersperse "\\" . L.map show) bs ++ "." ++ show t
    show (Tcon nm typs) = nm ++ (concat . intersperse " " . L.map show) typs
    show Ttop = "T"
    show Tbot = "L"
    show TDyn = "?"
    show (Tprog types) = (concat . intersperse "\n\n" . L.map show) types

-- To latex typeseting
-- instance Show Vtype where
--     show Tint = "\\Int"
--     show Tchar = "\\Char"
--     show Tbool = "\\Bool"
--     show (Tvar i) = "\\tv_{"++ show i ++ "}"
--     show (l `Tfun` r) = lpart l ++ show l ++ rpart l ++ "\\to" ++ show r
--     show (Tc n l r) = "\\chc"++n ++ "{" ++ show l ++ "," ++ show r ++ "}"
--     show (Tlist t) = "[" ++ show t ++ "]"
--     show (Forall bs t) = "\\forall " ++ (concat . intersperse "\\" . L.map show) bs ++ "." ++ show t
--     show Ttop = "\\ok"
--     show Tbot = "\\err"
--     show TDyn = "\\dyn"

-- Decide if the term contains only one value, name, ...
primitive :: Term -> Bool
primitive (Vi _) = True
primitive (Vb _) = True
primitive (Vv _) = True
primitive (Vc _) = True
primitive _ = False

isApp :: Term -> Bool
isApp (App _ _) = True
isApp _ = False

pp :: Term -> (Term -> Bool) -> String
pp t f = if f t then "(" ++ show t ++ ")" else show t

pForFun :: Term -> Bool
pForFun trm = not (isApp trm || primitive trm)

instance Show Term where
    show (Vi i) = show i
    show (Vb b) = show b
    show (Vv n) = n
    show (Vc c) = show c
    
    show (App (Vv n) r) | n `elem` ins = show r ++ " " ++ n 
    
    -- show (App l r ) = "(" ++ show l ++ " " ++ show r ++ ")" 
    show (App l r ) = pp l pForFun ++ " " ++ pp r (not . primitive) 

    
    -- show (Lam n t ) = "(\\" ++ n ++ "." ++ show t ++ ")" 
    -- show (DynLam n t) = "(\\?" ++ n ++ "." ++ show t ++ ")" 
    -- show (CDLam n t) = "(\\C?" ++ n ++ "." ++ show t ++ ")" 
    show (Lam n t ) = "\\" ++ n ++ "." ++ show t 
    show (DynLam n t) = "\\?" ++ n ++ "." ++ show t
    show (CDLam n t) = "\\C?" ++ n ++ "." ++ show t

    show (LetList bindings e2 ) = 
        let substrs = L.map show bindings
        in  "\nlet " ++ (concat . intersperse "\n    ") substrs ++ "\nin " ++ show e2 
    show (Let nm bound trm) = "Let " ++ nm ++ " = " ++ show bound ++ " in " ++ show trm 
    show (Binding n t) = n ++ " = " ++ show t
    show (If e1 e2 e3) = "\nIf " ++ show e1 ++ "\n\tThen " ++ show e2 ++ "\n\tElse " ++ show e3
    show (Fix f body) =  f ++ " = "++show body
    show (Prog trms) = (concat . intersperse "\n\n" . L.map show) trms

ins = ["-","+",":","<=",">","++","*","==", "&&", "!!"]
    
isV :: Term -> Bool
isV (Vv _ ) = True
isV _ = False
    
showSub :: (Show a, Show b) => M.Map a b -> String
showSub = concat . L.map (\(from, to) -> show from ++ " |-> " ++ show to ++ "\n") . M.assocs

farg, fres :: Vtype -> Vtype
farg (Tfun arg _) = arg
farg t = error "non function type:\t"

fres (Tfun _ res) = res
fres t = error "non functoin type\t"

instance Show Loc where
    show NoNewChc = ""
    show (Loc i) = show i


annotSpace :: Term -> [Term]
annotSpace (App fun arg) = [App l r | l <- annotSpace fun, r <- annotSpace arg]
annotSpace (Let nm bound body) = [Let nm l r | l <- annotSpace bound, r <- annotSpace body]
annotSpace (Lam nm trm) = L.map (Lam nm) (annotSpace trm)
annotSpace (DynLam nm trm) = L.map (DynLam nm) (annotSpace trm)
annotSpace (CDLam nm trm) = let trms = annotSpace trm 
                            in L.map (DynLam nm) trms ++ L.map (Lam nm) trms
annotSpace ll@(LetList bindings body) = annotSpace (desugar ll)
annotSpace (If cond thn els) = [If c t e | c <- annotSpace cond, t <- annotSpace thn, e <- annotSpace els]
annotSpace (Fix nm trm) = L.map (Fix nm) (annotSpace trm)
annotSpace (Binding nm trm) = L.map (Binding nm) (annotSpace trm)

annotSpace (Prog [trm]) = L.map (\t -> Prog [t]) (annotSpace trm)
annotSpace (Prog (trm:trms)) = [Prog (t:ts) | t <- annotSpace trm, Prog ts <- annotSpace (Prog trms)]

annotSpace trm = [trm]


desugar (LetList [Binding nm bound] term) = Let nm bound term
desugar (LetList ((Binding nm bound):others) term) = Let nm bound (desugar (LetList others term))
desugar trm = trm












