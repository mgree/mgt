module Basics where

import Prelude as P

import Types


(->>) = Tfun
infixr ->>

(@>) = Lam    -- Abstractions with inferred parameter types
infixr 2 @>

(\>) = DynLam -- Abstractions with dynamic parameter types
infixr 2 \>

(\\>) = CDLam -- Abstractions with variational parameter types 
infixr 2 \\>

[tca, tcb, tcc, tcd,tce] = P.map Tc ["A", "B", "C", "D", "E"]
[tv1,tv2,tv3,tv4,tv5,tv6,tv7,tv8,tv9] = P.map Tvar [1..9]
[tva,tvb,tvc,tvd,tve,tvf,tvg,tvh,tvi] = P.map Tvar [0..8]

[t0,t1,t2,t3] = P.map Tvar [0,1,2,3]


