-- 24 Loc

module EncFql132 where

import Types
import Vunify
import Infer
import Basics


{-

projectsubsubsub :: String -> [String] -> [String]
projectsubsubsub _ [] = []
projectsubsubsub x (y:ys) | eqString x y = (y:ys)
                          | otherwise = []

projectsubsub :: String -> Table -> Table
projectsubsub _ [] = []
projectsubsub x t = ( [projectsubsubsub x (head(transpose t))]) 
                 ++ (projectsubsub x (transpose(tail(transpose t))))


projectsub :: [String] -> Table -> Table
projectsub [] _ = []
projectsub (x:xs) t = (projectsubsub x t) ++ (projectsub xs t)

project :: [String] -> Table -> Table
project xs t = transpose( projectsub xs t )

kolomnr :: String -> [String] -> Int
kolomnr _ [] = 0
kolomnr x (y:ys) | (eqString x y) = 0
                 | otherwise = 1 + (kolomnr x ys)


rij :: [String] -> Int  -> (String->Bool) -> [String]
rij xs y f | f (xs!!y) = xs
           | otherwise = []

bouwTable :: String -> (String -> Bool) -> Table -> Int -> Table
bouwTable _ _ [] _ = []
bouwTable x f t y | null (rij (head t) y f) = (bouwTable x f (tail t) y)
                  | otherwise = (rij (head t) y f) : (bouwTable x f (tail t) y)

-}


progf132 = Prog [
             Binding "projectsubsubsub132" projectsubsubsub132
           , Binding "projectsubsub132" projectsubsub132
           , Binding "projectsub132" projectsub132
           , Binding "project132" project132
           , Binding "kolomnr132" kolomnr132
           , Binding "rij132" rij132
           , Binding "bouwTable132" bouwTable132
          ]



-- expf130 = Binding "writeTable130" writeTable130


projectsubsubsub132 = "x" \\> "ys" \\>
    If (vv "null" <> vv "ys")
       (vv "[]")
       ( If (vv "eqString" <> vv "x" <> (vv "head" <> vv "ys") )
            ( vv "ys")
            (vv "[]")
       )




projectsubsub132 = Fix "projectsubsub132" $ "x" \\> "t" \\>
    If (vv "null" <> vv "t")
       (vv "[]")
       (vv "++" <> ( vv "single" <> (vv "projectsubsubsub132" <> vv "x" <> (vv "head" <> (vv "transpose" <> vv "t"))))
                <> ( vv "projectsubsub132" <> vv "x" <> (vv "transpose" <> (vv "tail" <> (vv "transpose" <> vv "t"))))
       )



projectsub132 = Fix "projectsub132" $ "xs" \\> "t" \\>
    If (vv "null" <> vv "xs")
       (vv "[]")
       (vv "++" <> ( vv "projectsubsub132" <> (vv "head" <> vv "xs") <> vv "t")
                <> ( vv "projectsub132" <> (vv "tail" <> vv "xs") <> vv "t"))


project132 = "xs" \\> "t" \\>
  vv "transpose" <> (vv "projectsub132" <> vv "xs" <> vv "t")

kolomnr132 = Fix "kolomnr132" $ "x" \\> "ys" \\>
    If (vv "null" <> vv "ys")
       i0
       ( If (vv "eqString" <> vv "x" <> (vv "head" <> vv "ys"))
            i0
            (vv "+" <> i1 <> (vv "kolomnr132" <> vv "x" <> (vv "tail" <> vv "ys")))

       )


rij132 = "xs" \\> "y" \\> "f" \\>
    If (vv "f" <>  (vv "!!" <> vv "xs" <> vv "y") )
       (vv "xs")
       (vv "[]")

bouwTable132 = Fix "bouwTable132" $ "x" \\> "f" \\> "t" \\> "y" \\>
    LetList [
             Binding "projectsubsubsub132" projectsubsubsub132
           , Binding "projectsubsub132" projectsubsub132
           , Binding "projectsub132" projectsub132
           , Binding "project132" project132
           , Binding "kolomnr132" kolomnr132
           , Binding "rij132" rij132
--           , Binding "bouwTable132" bouwTable132
          ]
  (
    If (vv "null" <> ( vv "rij132" <> (vv "head" <> vv "t") <> vv "y" <> vv "f" ))
       (vv "bouwTable132" <> vv "x" <> vv "f" <> (vv "tail" <> vv "t") <> vv "y")
       ( vv ":" <> (vv "rij132" <> (vv "head" <> vv "t") <> vv "y" <> vv "f")
                <> (vv "bouwTable132" <> vv "x" <> vv "f" <> (vv "tail" <> vv "t") <> vv "y")
       )
  )


expf132 = Binding "bouwTable132" bouwTable132












