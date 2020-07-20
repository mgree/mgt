-- 36 Loc

module EncFql147 where

import Types
import Vunify
import Infer
import Basics



vergelijk147 = Fix "vergelijk147" $ "xs" \\> "y" \\>
    If (vv "eqString" <> vv "y" <> str)
       (vv "[]")
       ( If (vv "null" <> vv "xs")
            (vv "[]")
            ( If (vv "eqString" <> (vv "head" <> (vv "head" <> vv "xs")) <> vv "y" )
                 (vv "++" <> (vv "head" <> vv "xs")
                          <> (vv "vergelijk147" <> (vv "tail" <> vv "xs") <> vv "y"))
                 (vv "vergelijk147" <> (vv "tail" <> vv "xs") <> vv "y")
            )

       )


vergelijkLijst147 = Fix "vergelijkLijst147" $ "table" \\> "ys" \\>
    If (vv "null" <> vv "table")
       ( vv "[]")
       ( If (vv "null" <> vv "ys")
            (vv "[]")
            (vv ":" <> (vv "vergelijk147" <> vv "table" <> (vv "head" <> vv "ys"))
                    <> (vv "vergelijkLijst147" <> vv "table" <> (vv "tail" <> vv "ys"))
              )
       )

project147 = "string" \\> "table" \\>
    vv "transpose" <> (vv "vergelijkLijst147" <> (vv "transpose" <> vv "table") <> vv "string")



neemIndex147 = Fix "neemIndex147" $ "naam" \\> "lijst1" \\>
      If (vv "eqString" <> (vv "head" <> vv "lijst1") <> vv "naam")
          i0
          (vv "+" <> i1 <> (vv "neemIndex147" <> vv "naam" <> (vv "tail" <> vv "lijst1") )) 

select147 = "naam" \\> "p" \\> "table" \\>
  LetList [ Binding "kolomnummer" (vv "neemIndex147" <> vv "naam" <> (vv "head" <> vv "table"))
          , Binding "g"  ("rij" @> vv "p" <> (vv "!!" <> vv "rij" <> vv "kolomnummer" ))
          ]
      ( vv ":" <> ( vv "head" <> vv "table")
               <> ( vv "filter" <> vv "g" <> (vv "tail" <> vv "table"))

      )


verwijderKolom147 = "xs" \\> "n" \\>
    vv "++" <> ( vv "take" <> vv "n" <> vv "xs")
            <> (vv "drop" <> (vv "-" <> vv "n" <> i1) <> vv "xs")

zelfdeVeld147 = vv "zelfdeVeld"

{-
zelfdeVeld147 = Fix "zelfdeVeld147" $ "xs" \\> "ys" \\>
    If (vv "elemBy" <> vv "eqString" <> (vv "head" <> (vv "head" <> vv "xs")) <> (vv "head" <> vv "ys"))
       (vv "head" <> (vv "head" <> vv "xs"))
       (vv "zelfdeVeld147" <> (vv ":" <> (vv "tail" <> (vv "head" <> vv "xs"))
                                   <> (vv "tail" <> vv "xs") ) <> vv "ys" )
-}

-- The translation of joinTables is slightly different from the original program
join147 = "table1" \\> "table2" \\> 
  LetList [  Binding "vergelijk147" vergelijk147
           , Binding "vergelijkLijst147" vergelijkLijst147
           , Binding "project147" project147
           , Binding "neemIndex147" neemIndex147
           , Binding "select147" select147
           , Binding "verwijderKolom147" verwijderKolom147
           , Binding "zelfdeVeld147" zelfdeVeld147
           , Binding "veld" (vv "zelfdeVeld147" <> vv "table1" <> vv "table2"  )
           , Binding "index1" (vv "neemIndex147" <> vv "veld" <> (vv "head" <> vv "table1") )
           , Binding "index2" (vv "neemIndex147" <> vv "veld" <> (vv "head" <> vv "table2") )
           , Binding "x" (vv "head" <> (vv "tail" <> vv "table1"))
           , Binding "y" (vv "head" <> (vv "tail" <> vv "table2"))
          ]
          ( If (vv "eqString" <> (vv "!!" <> vv "x" <> vv "index1") 
                              <> (vv "!!" <> vv "y" <> vv "index2"))
               (vv "single" <> vv "x")
               (vv "single" <> ( vv "verwijderKolom147" <> vv "y" <> vv "index2") )
          )

expf147 = Binding "join147" join147


{-

vergelijk:: [[String]] -> String -> [String]
vergelijk _ "" = []
vergelijk [] _  = []
vergelijk (x:xs) y
                    |(eqString (head x) y)  = x ++ vergelijk (xs) y
                    | otherwise   = vergelijk xs y


vergelijkLijst :: [[String]] -> [String] -> [[String]]
vergelijkLijst [] [] = []
vergelijkLijst _ [] = []
vergelijkLijst table (y:ys) = vergelijk table y : vergelijkLijst  table ys

project :: [String] -> Table -> Table
project string table = transpose(vergelijkLijst (transpose table) string)


neemIndex :: String -> [String] -> Int
neemIndex x (y:ys)
                  |eqString x y = 0
                  |otherwise    = 1 + neemIndex x ys


select :: String -> (String -> Bool) -> Table -> Table
select naam p table = head table : filter g (tail table)
                          where g rij = p  (rij !! kolomnummer)
                                kolomnummer = (neemIndex naam (head table))

verwijderKolom:: [String] -> Int -> [String]
verwijderKolom (xs) n = take (n) xs ++ drop (n+1) xs

zelfdeVeld :: Table -> Table -> String
zelfdeVeld ((x:xn):xs) (y:ys)
                       | elemBy eqString (x) y = (x)
                       | otherwise             = zelfdeVeld (xn:xs) ((y:ys))



join:: Table-> Table -> Table
join table1 table2 =
  [ x ++ (verwijderKolom y index2)
  | x <- table1
  , y <- table2
  , eqString (x !! index1) (y !! index2)
  ]
  where
     veld   = zelfdeVeld table1 table2
     index1 =  neemIndex veld (head table1)
     index2 =  neemIndex veld (head table2)
-}

