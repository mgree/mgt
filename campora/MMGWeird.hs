module MMGWeird where

import Prelude hiding ((<>))

import Types
import Vunify
import Infer
import Basics

f = "x" \\> If (vv "x") ("y" \> vv "x") fls
f' = "x" \\> If (vv "x") ("y" \\> vv "x") fls
