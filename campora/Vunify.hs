module Vunify where

import Types

import Data.List as L
import Data.Map as M
import Data.Set as S
import Data.Char
import Control.Monad.State

-- Substitution merge with a given choice name
oplus :: Cname -> Sub -> Sub -> Sub
oplus n l r = M.mapWithKey (\k tl -> idempOnce (Tc n tl (M.findWithDefault k k r)) ) l 
              `M.union`
              M.mapWithKey (\k tr -> Tc n k tr) (M.difference r l)

-- vjoin, compute the join of two types and perform unification in needs
-- The second returned result is the pattern, and the thrid returned result is
-- the joined type. 
-- For example, vjoin TDyn Int = ({},Ttop,Int)
--              vjoin Bool Int = ({},Tbot,TDyn)

vjoin :: Vtype -> Vtype -> State IState (Sub, Vtype, Vtype)
vjoin TDyn t = return (M.empty, Ttop, t)
vjoin t TDyn = return (M.empty, Ttop, t)
vjoin lft@(Tc n1 l1 r1) rgt@(Tc n2 l2 r2)
    | n1 == n2 = do (subl,patl,typl) <- vjoin l1 l2
                    (subr,patr, typr) <- vjoin r1 r2
--                    error $ "The subl: " ++ show subl ++ "\nThe subr: " ++ show subr ++ "\nThe r1: " ++ show r1 ++ "\tThe r2: " ++ show r2 
                    return (oplus n1 subl subr, 
                            idempOnce (Tc n1 patl patr), 
                            idempOnce (Tc n1 typl typr))
    | otherwise = vjoin lft (Tc n1 (sell n1 rgt) (selr n1 rgt))  

vjoin v@(Tvar _) vt
    | v == vt = return (M.empty, Ttop, v)
    | v `S.notMember` varset && hasDyn vt == False = return (M.singleton v vt, Ttop, v)
    | not (S.null cset) = vjoin  (Tc splitc v v) 
                                 (Tc splitc (sell splitc vt) (selr splitc vt))
    | v `S.notMember` varset && isTfun vt = do
        nv1 <- newVn
        nv2 <- newVn
        (sub, pat, join) <- vjoin (nv1 `Tfun` nv2) vt
        return (sub @@ M.singleton v (nv1 `Tfun` nv2), pat, sub >>> join)
    -- Also need a case for unifying a variable against Tcon
    | True = return (M.empty, Tbot, TDyn)
    where cset = chcs vt 
          splitc = S.findMin cset
          varset = vars vt

vjoin vt var@(Tvar _) = vjoin var vt

vjoin (Tfun arg1 ret1) (Tfun arg2 ret2) = do
    (sub1, tp1, arg) <- vjoin arg1 arg2
    (sub2, tp2, ret) <- vjoin (sub1 >>> ret1) (sub1 >>> ret2)
    return (sub2 @@ sub1, intP tp1 tp2, arg `Tfun` ret)

vjoin chc@(Tc n _ _) vt = do
--    error $ "The choice type: " ++ show chc ++ "\tThe vt: " ++ show vt
    vjoin chc (Tc n (sell n vt) (selr n vt))
vjoin vt chc@(Tc n _ _) = vjoin chc vt

vjoin (Tlist t1) (Tlist t2) = fmap (\(x,y,z) -> (x,y,Tlist z)) (vjoin t1 t2)

vjoin (Tcon nm1 typs1) (Tcon nm2 typs2)
    | nm1 == nm2 || length typs1 /= length typs2 = return (M.empty, Tbot, TDyn)
    | True = vjoinL typs1 typs2 M.empty >>= \(sub, pat, rs) -> return (sub, pat, Tcon nm1 rs)

-- Unifying constant types
vjoin t1 t2 
    | t1 == t2 = return (M.empty, Ttop, t1)
    | True     = return (M.empty, Tbot, t1)
--    | True     = return (M.empty, Tbot, TDyn)

vjoinL [x] [y] sub = vjoin (sub >>>x) (sub >>> y) >>= \(sub, pat, r) -> return (sub, pat, [r])    
vjoinL (x:xs) (y:ys) subo = do
    (sub1,tp1, r) <- vjoin (subo >>> x) (subo >>> y)
    (subr,tpr, rs) <- vjoinL xs ys (sub1 @@ subo)
    return (subr @@ sub1, tp1 `intP` tpr, r:rs)


-- Unifying two types, returning a substitution and a typing pattern
vunify :: Vtype -> Vtype -> State IState (Sub, Vtype)
vunify l r = fmap (\(x,y,z) -> (x,y)) (vjoin l r)
    
hasDyn :: Vtype -> Bool
hasDyn TDyn = True
hasDyn (Tfun l r) = hasDyn l || hasDyn r
hasDyn (Tc _ l r) = hasDyn l || hasDyn r
hasDyn (Tcon _ typs) = any hasDyn typs
hasDyn _ = False



















    
    
    