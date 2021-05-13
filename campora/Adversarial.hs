module Adversarial where

import Prelude hiding ((<>))

import Control.Monad.State

import Types
import Vunify
import Infer
import Basics

-- 01-farg-mismatch.gtlc
a01_farg_mismatch = ("f" @> (vv "f") <> tru) <> ("x" @> plus (vv "x") (Vi 100))

-- 02-rank2-poly-id.gtlc
a02_rank2_poly_id = ("i" \\> ("a" \\> (vv "i") <> tru) <> (vv "i" <> (Vi 5))) <> ("x" \\> vv "x")

-- 03-unreachable-error.gtlc
a03_unreachable_error =
  ("b" \\> vv "b" <> ("c" \\> (("x" \\> vv "x" <> vv "x") <> (Vi 5)) <> (Vi 5)) <> ("d" \\> (Vi 0))) <>
  ("t" \\> "f" \\> vv "f")

-- 04-f-in-f-out.gtlc
a04_fin_fout = ("f" \\> ("y" \\> vv "f") <> (vv "f" <> (Vi 5))) <> ("x" \\> plus (Vi 10) (vv "x"))

-- 05-order3-fun.gtlc
a05_order3_fun = "f" \\> "x" \\> vv "x" <> (vv "f" <> vv "x")

-- 06-order3-intfun.gtlc
a06_order3_intfun = "f" \\> "g" \\> (vv "f" <> vv "g") <> (plus (vv "g" <> Vi 10) (Vi 1))

-- 07-double-f.gtlc
a07_double_f = "f" \\> vv "f" <> (vv "f" <> tru)

-- 08-outflows.gtlc
a08_outflows = ("x" \\> plus (vv "x" <> Vi 5) (vv "x")) <> Vi 5

-- 09-precision-relation.gtlc
a09_precision_relation = ("f" \\> plus (vv "f" <> tru) (("g" \\> vv "g" <> Vi 5) <> vv "f")) <> ("x" \\> Vi 5)

-- 10-if-tag.gtlc
a10_if_tag = ("tag" \\> "x" \\>
              If (vv "tag")
              (plus (vv "x") (Vi 1))
              (If (vv "x") (Vi 1) (Vi 0)))

plusEnv = [("plus",Tint `Tfun` (Tint `Tfun` Tint))]
plus a1 a2 = vv "plus" <> a1 <> a2

-- NB they don't bother instantiating things not found in the final pattern
--
-- >>> > go ("x" \\> vv "x")
-- (fromList [],(AAA<?,Tv0>)->AAA<?,Tv0>,T)
go e = fst $ runState (infer plusEnv e) (0,0,initChg,initChg,[],initChg)
