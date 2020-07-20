-- 56 Loc

module EncFql156 where

import Types
import Vunify
import Infer
import Basics


{-
lengteStrings:: [[String]]-> [[Int]]
lengteStrings [] = [[0]]
lengteStrings (x: xs) =  (map length x) : lengteStrings xs

maxBreedte::[[Int]] -> [Int]
maxBreedte lijst = map maximum lijst

combineer::[[String]] -> [Int]
combineer table =  maxBreedte(transpose(lengteStrings table))

vulAan::[String] -> [Int] -> String
vulAan [] [] = "|" ++ "\n"
vulAan [] _ = error ("kan niet")
vulAan _ [] = error ("kan niet")
vulAan (x:xs) (y:ys)= ( "|" ++ x ++ (take (y-(length x)) (repeat ' ')))++ vulAan xs ys

tabelVulAan::[[String]]-> [Int]-> String
tabelVulAan [] _ = ""
tabelVulAan (x:xs) breedtes = vulAan x breedtes ++ tabelVulAan xs breedtes


scheiding:: [Int] -> String
scheiding [] = "+" ++ "\n"
scheiding (y:ys)= ( "+" ++ (take (y) (repeat '-'))) ++ scheiding ys


writeTable:: [[String]] -> String
writeTable (x:xs) = scheiding breedtes ++ vulAan x breedtes ++
                    scheiding breedtes ++((tabelVulAan xs (breedtes))) ++
                    scheiding breedtes
                             where breedtes = combineer (x:xs)

-}

lengteStrings156 = Fix "lengteStrings156" $ "xs" \\>
    If (vv "null" <> vv "xs")
       (vv "single" <> (vv "single" <> i0))
       (vv ":" <> (vv "map" <> vv "length" <> (vv "head" <> vv "xs"))
               <> (vv "lengteStrings156" <> (vv "tail" <> vv "xs")) )

maxBreedte156 = "lijst" \\>
  vv "map" <> vv "maximum" <> vv "lijst"

combineer156 = "table" \\>
  vv "maxBreedte156" <> (vv "transpose" <> (vv "lengteStrings156" <> vv "table"))

vulAan156 = Fix "vulAan156" $ "xs" \\> "ys" \\>
    If (vv "null" <> vv "xs")
       str
       ( If (vv "null" <> vv "ys")
            str
            (vv "++" <> str 
                     <> (vv "++" <> (vv "head" <> vv "xs")
                                 <> (vv "++" <> (vv "take" <> (vv "-" <> (vv "head" <> vv "ys") <> (vv "length" <> (vv "head" <> vv "xs")))
                                                           <>  (vv "repeat" <> vc)
                                                )
                                             <> (vv "vulAan156" <> (vv "tail" <> vv "xs") <> (vv "tail" <> vv "ys"))
                                    )
                        )
            )
       )



tabelVulAan156 = Fix "tabelVulAan156" $ "xs" \\> "breedtes" \\>
    If (vv "null" <> vv "xs")
       str
       ( vv "++" <> (vv "vulAan156" <> (vv "head" <> vv "xs") <> vv "breedtes")
                 <> (vv "tabelVulAan156" <> (vv "tail" <> vv "xs") <> vv "breedtes")
       )

scheiding156 = Fix "scheiding156" $ "ys" \\>
    If (vv "null" <> vv "ys") 
       (vv "++" <> str <> str)
       (vv "++" <> (vv "++" <> str 
                            <> (vv "take" <> (vv "head" <> vv "ys") <> (vv "repeat" <> vc) ))
                <> (vv "scheiding156" <> (vv "tail" <> vv "ys")) )

progf156 = Prog [
             Binding "lengteStrings156" lengteStrings156
           , Binding "maxBreedte156" maxBreedte156
           , Binding "combineer156" combineer156
           , Binding "vulAan156" vulAan156
           , Binding "tabelVulAan156" tabelVulAan156
           , Binding "scheiding156" scheiding156
           , Binding "writeTable156" writeTable156
           , Binding "vergelijk156" vergelijk156
           , Binding "vergelijkLijst156" vergelijkLijst156
           , Binding "project156" project156
           , Binding "neemIndex156" neemIndex156
           , Binding "select156" select156
           , Binding "verwijderKolom156" verwijderKolom156
           , Binding "zelfdeVeld156" zelfdeVeld156
           , Binding "join156" join156
          ]


vergelijk156 = Fix "vergelijk156" $ "xs" \\> "y" \\>
    If (vv "eqString" <> vv "y" <> str)
       (vv "[]")
       ( If (vv "null" <> vv "xs")
            (vv "[]")
            ( If (vv "eqString" <> (vv "head" <> (vv "head" <> vv "xs")) <> vv "y" )
                 (vv "++" <> (vv "head" <> vv "xs")
                          <> (vv "vergelijk156" <> (vv "tail" <> vv "xs") <> vv "y"))
                 (vv "vergelijk156" <> (vv "tail" <> vv "xs") <> vv "y")
            )

       )


vergelijkLijst156 = Fix "vergelijkLijst156" $ "table" \\> "ys" \\>
    If (vv "null" <> vv "table")
       ( vv "[]")
       ( If (vv "null" <> vv "ys")
            (vv "[]")
            (vv ":" <> (vv "vergelijk156" <> vv "table" <> (vv "head" <> vv "ys"))
                    <> (vv "vergelijkLijst156" <> vv "table" <> (vv "tail" <> vv "ys"))
              )
       )

project156 = "string" \\> "table" \\>
    vv "transpose" <> (vv "vergelijkLijst156" <> (vv "transpose" <> vv "table") <> vv "string")



neemIndex156 = Fix "neemIndex156" $ "naam" \\> "lijst1" \\>
      If (vv "eqString" <> (vv "head" <> vv "lijst1") <> vv "naam")
          i0
          (vv "+" <> i1 <> (vv "neemIndex156" <> vv "naam" <> (vv "tail" <> vv "lijst1") )) 

select156 = "naam" \\> "p" \\> "table" \\>
  LetList [ Binding "kolomnummer" (vv "neemIndex156" <> vv "naam" <> (vv "head" <> vv "table"))
          , Binding "g"  ("rij" @> vv "p" <> (vv "!!" <> vv "rij" <> vv "kolomnummer" ))
          ]
      ( vv ":" <> ( vv "head" <> vv "table")
               <> ( vv "filter" <> vv "g" <> (vv "tail" <> vv "table"))

      )


verwijderKolom156 = "xs" \\> "n" \\>
    vv "++" <> ( vv "take" <> vv "n" <> vv "xs")
            <> (vv "drop" <> (vv "-" <> vv "n" <> i1) <> vv "xs")

zelfdeVeld156 = Fix "zelfdeVeld156" $ "xs" \\> "ys" \\>
    If (vv "elemBy" <> vv "eqString" <> (vv "head" <> (vv "head" <> vv "xs")) <> (vv "head" <> vv "ys"))
       (vv "head" <> (vv "head" <> vv "xs"))
       (vv "zelfdeVeld156" <> (vv ":" <> (vv "tail" <> (vv "head" <> vv "xs"))
                                   <> (vv "tail" <> vv "xs") ) <> vv "ys" )

-- The translation of joinTables is slightly different from the original program
join156 = "table1" \\> "table2" \\> 
  LetList [ Binding "veld" (vv "zelfdeVeld156" <> vv "table1" <> vv "table2"  )
          , Binding "index1" (vv "neemIndex156" <> vv "veld" <> (vv "head" <> vv "table1") )
          , Binding "index2" (vv "neemIndex156" <> vv "veld" <> (vv "head" <> vv "table2") )
          , Binding "x" (vv "head" <> (vv "tail" <> vv "table1"))
          , Binding "y" (vv "head" <> (vv "tail" <> vv "table2"))
          ]
          ( If (vv "eqString" <> (vv "!!" <> vv "x" <> vv "index1") 
                              <> (vv "!!" <> vv "y" <> vv "index2"))
               (vv "single" <> vv "x")
               (vv "single" <> ( vv "verwijderKolom156" <> vv "y" <> vv "index2") )
          )

writeTable156 = "xs" \\>
    LetList [
             Binding "lengteStrings156" lengteStrings156
           , Binding "vergelijk156" vergelijk156
           , Binding "vergelijkLijst156" vergelijkLijst156
           , Binding "project156" project156
           , Binding "neemIndex156" neemIndex156
           , Binding "select156" select156
           , Binding "verwijderKolom156" verwijderKolom156
--           , Binding "zelfdeVeld156" zelfdeVeld156
--            , Binding "join156" join156
           , Binding "maxBreedte156" maxBreedte156
           , Binding "combineer156" combineer156
           , Binding "vulAan156" vulAan156
           , Binding "tabelVulAan156" tabelVulAan156
           , Binding "scheiding156" scheiding156
           , Binding "breedtes" (vv "combineer156" <> vv "xs")
      ]
  (
    Let "breedtes" (vv "combineer156" <> vv "xs")
        ( vv "++" <> ( vv "scheiding156" <> vv "breedtes")
                  <> ( vv "++" <> (vv "vulAan156" <> (vv "head" <> vv "xs") <> vv "breedtes") 
                               <> ( vv "++" <> (vv "scheiding156" <> vv "breedtes")
                                            <> (vv "++" <> (vv "tabelVulAan156" <> (vv "tail" <> vv "xs") <> vv "breedtes")
                                                        <> (vv "scheiding156" <> vv "breedtes")
                                               )
                                  )
                     )

        )
  )

expf156 = Binding "writeTable156" writeTable156

