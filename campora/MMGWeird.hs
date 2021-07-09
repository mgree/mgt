module MMGWeird where

import Prelude hiding ((<>))

import Control.Monad.State

import Types
import Vunify
import Infer
import Basics

f = "x" \\> If (vv "x") ("y" \> vv "x") fls
f' = "x" \\> If (vv "x") ("y" \\> vv "x") fls

g = Let "id" ("x" \\> vv "x") (If (vv "id" <> tru) (vv "id" <> i0) (vv "id" <> i1))
g' = Let "id" ("x" \\> vv "x") (If (vv "id" <> tru) (vv "id" <> tru) (vv "id" <> fls))

h = Let "id" ("x" \> vv "x") (If (vv "id" <> tru) (vv "id" <> i0) (vv "id" <> i1))
h' = Let "id" ("x" \> vv "x") (If (vv "id" <> tru) (vv "id" <> tru) (vv "id" <> fls))

i = Let "id" ("x" @> vv "x") (If (vv "id" <> tru) (vv "id" <> i0) (vv "id" <> i1))
i' = Let "id" ("x" @> vv "x") (If (vv "id" <> tru) (vv "id" <> tru) (vv "id" <> fls))

poly = Let "id" ("x" \\> vv "x")
         (Let "res" (If (vv "id" <> tru) (vv "id" <> i0) (vv "id" <> i1))
                    (vv "id"))


-- NB they don't both instantiating things not found in the final pattern
--
-- >>> > go ("x" \\> vv "x")
-- (fromList [],(AAA<?,Tv0>)->AAA<?,Tv0>,T)
go e = fst $ runState (infer [] e) (0,0,initChg,initChg,[],initChg)
