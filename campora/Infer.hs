module Infer where

import Types
import Vunify

import Data.List as L
import Data.Map as M
import Data.Set as S
import Control.Monad.State
import System.IO.Unsafe
import Data.Foldable (foldlM)

import Data.Functor.Identity

instance MonadFail Identity where
  fail s = error s

-- Returns substitution, result type, typing patterns
infer :: Env -> Term -> State IState (Sub,Vtype,Vtype)

infer _ (Vi _) = return (M.empty, Tint, Ttop)

infer _ (Vc _) = return (M.empty, Tchar, Ttop)

infer _ (Vb _) = return (M.empty, Tbool, Ttop)
    
infer env (Vv name) 
    = inst (query name env) >>= \t ->
      return (M.empty, t, varBound t)
      
infer env (Lam n term)
    = newVn >>= \nv ->
      infer ((n,nv):env) term >>= \(sub,t,tp) ->
      return (sub, sub >>> nv `Tfun` t,tp)

infer env (DynLam n term)
    = infer ((n,TDyn):env) term >>= \(sub,t,tp) -> 
      return (sub, sub >>> (TDyn `Tfun` t), tp)

infer env (CDLam n term) = do

    freshd <- newDn
    freshv <- newVn
    
    let parTyp = Tc freshd TDyn freshv

    (sub,t,tp) <- infer ((n,parTyp) : env) term

    return (sub, sub >>> (parTyp `Tfun` t), tp)

infer env (App fun val) = do
    (subl,lt,tpl) <- infer env fun
    (dom, cdom, tp2, sub) <- deArrow lt
    let sl = sub @@ subl

    -- error $ "The func type: " ++ show lt ++ "\tdom: " ++ show dom ++ "\tcodom: "++ show cdom

    (subr,rt,tpr) <- infer (upEnv sl env) val

    (sub,tp) <- vunify ( (subr @@ sl) >>> dom) rt

    let subres = sub @@ subr @@ sl

    return (subres, subres >>> cdom, idempOnce $ tpl `intP` tp2 `intP` tpr `intP` tp)

infer env (If cond thn els) = do
    (subc, tc, tpc) <- infer env cond
    (subt, tt, tpt) <- infer (upEnv subc env) thn
    (sube, te, tpe) <- infer (upEnv (subt @@ subc) env) els

    -- error $ "The cond type: " ++ show tc ++ "\tthen type: " ++ show tt ++ "\telse type: " ++ show te

    let sub = sube @@ subt @@ subc

    (subu, tpu) <- vunify Tbool (sub >>> tc)

--     error $ "The type of tc: " ++ show subu

    (subte,tpte,tte) <- vjoin ((subu @@ sube) >>> tt) (subu >>> te)

    let subres = subte @@ subu @@ sub

    return (subres, subres >>> tte, tpc `intP` tpt `intP` tpe `intP` tpu `intP` tpte) 


infer env letl@(LetList bindings term) = infer env (desugar letl)

infer env (Let nm bound trm) = do
    (sub,t,pat) <- infer env bound
    (sub2,res,pat2) <- infer (upEnv sub ((nm,t):env)) trm

    return (sub2 @@ sub, res , pat `intP` pat2)

infer env (Fix nm trm) = do
    nv <- newVn
    (sub,t,tp) <- infer ((nm,nv):env) trm 
    
    let old = sub >>> nv 
    (nsub, ntp) <- old `vunify` t
        
    return (nsub @@ sub, nsub >>> t, idempOnce (ntp `intP` tp))
    


infer env (Prog [Binding nm trm]) = do
    (sub,typ,pat) <- infer env trm

    return (sub, Tprog [typ] , Tprog [pat])

infer env (Prog ((Binding nm trm):trms)) = do
    (sub,typ,pat) <- infer env trm

    (sub2, Tprog res, Tprog pat2) <- infer (upEnv sub ((nm,typ):env)) (Prog trms)

    return (sub2, Tprog (typ:res) , Tprog (pat:pat2))



upEnv sub env = L.map (\(from,to) -> (from, sub >>> to)) env
      
inst :: Vtype -> State IState Vtype
inst (Forall bs t) 
    = forM bs (\b -> (newVn >>= \nv -> return (b,nv))) >>=
      \lists -> return (M.fromList lists >>> t )
inst t = return t
    
-- Use the following query for error-tolerant    
-- query name env = maybe Tbot id (L.lookup name env)
query name env = maybe (error $ "Unbound variable: " ++ show name) id (L.lookup name env)

-- Returns Bot if the argument is the error type and Top otherwise
varBound :: Vtype -> Vtype
varBound Tbot = Tbot
varBound _ = Ttop

deArrow :: Vtype -> State IState (Vtype,Vtype,Vtype,Sub)

deArrow (Tfun l r) = return (l, r, Ttop, M.empty)
deArrow (TDyn) = return (TDyn, TDyn, Ttop, M.empty)

deArrow tv@(Tvar _) 
  = newVn >>= \nv1 ->
    newVn >>= \nv2 -> 
    return (nv1, nv2, Ttop, M.singleton tv (nv1 `Tfun` nv2) )

deArrow (Tc n l r) 
  = deArrow l >>= \(tll, tlr, tpl, subl) -> 
    deArrow r >>= \(trl, trr, tpr, subr) ->
    return (idempOnce (Tc n tll trl), 
            idempOnce (Tc n tlr trr), 
            idempOnce (Tc n tpl tpr), oplus n subl subr)

-- For all other types, we can't turn them into arrows.
-- We return Dyn as both the argument type and the return type. 
-- This is because an unificaton problem involving Dyns is 
-- immediately discarded. 
-- More importantly, we return Tbot as the pattern to indicate
-- that the result is invalid. 

deArrow _ = return (TDyn, TDyn, Tbot, M.empty)













