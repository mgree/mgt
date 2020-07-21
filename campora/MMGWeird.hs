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
