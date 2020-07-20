-- 23 Loc

module EncFql138 where

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

lengteStrings138 = Fix "lengteStrings138" $ "xs" \\>
    If (vv "null" <> vv "xs")
       (vv "single" <> (vv "single" <> i0))
       (vv ":" <> (vv "map" <> vv "length" <> (vv "head" <> vv "xs"))
               <> (vv "lengteStrings138" <> (vv "tail" <> vv "xs")) )

maxBreedte138 = "lijst" \\>
  vv "map" <> vv "maximum" <> vv "lijst"

combineer138 = "table" \\>
  vv "maxBreedte138" <> (vv "transpose" <> (vv "lengteStrings138" <> vv "table"))

vulAan138 = Fix "vulAan138" $ "xs" \\> "ys" \\>
    If (vv "null" <> vv "xs")
       str
       ( If (vv "null" <> vv "ys")
            str
            (vv "++" <> str 
                     <> (vv "++" <> (vv "head" <> vv "xs")
                                 <> (vv "++" <> (vv "take" <> (vv "-" <> (vv "head" <> vv "ys") <> (vv "length" <> (vv "head" <> vv "xs")))
                                                           <>  (vv "repeat" <> vc)
                                                )
                                             <> (vv "vulAan138" <> (vv "tail" <> vv "xs") <> (vv "tail" <> vv "ys"))
                                    )
                        )
            )
       )



tabelVulAan138 = Fix "tabelVulAan138" $ "xs" \\> "breedtes" \\>
    If (vv "null" <> vv "xs")
       str
       ( vv "++" <> (vv "vulAan138" <> (vv "head" <> vv "xs") <> vv "breedtes")
                 <> (vv "tabelVulAan138" <> (vv "tail" <> vv "xs") <> vv "breedtes")
       )

scheiding138 = Fix "scheiding138" $ "ys" \\>
    If (vv "null" <> vv "ys") 
       (vv "++" <> str <> str)
       (vv "++" <> (vv "++" <> str 
                            <> (vv "take" <> (vv "head" <> vv "ys") <> (vv "repeat" <> vc) ))
                <> (vv "scheiding138" <> (vv "tail" <> vv "ys")) )


writeTable138 = "xs" \\>
    LetList [
             Binding "lengteStrings138" lengteStrings138
           , Binding "maxBreedte138" maxBreedte138
           , Binding "combineer138" combineer138
           , Binding "vulAan138" vulAan138
           , Binding "tabelVulAan138" tabelVulAan138
           , Binding "scheiding138" scheiding138
           , Binding "breedtes" (vv "combineer138" <> vv "xs")
      ]
  (
    Let "breedtes" (vv "combineer138" <> vv "xs")
        ( vv "++" <> ( vv "scheiding138" <> vv "breedtes")
                  <> ( vv "++" <> (vv "vulAan138" <> (vv "head" <> vv "xs") <> vv "breedtes") 
                               <> ( vv "++" <> (vv "scheiding138" <> vv "breedtes")
                                            <> (vv "++" <> (vv "tabelVulAan138" <> (vv "tail" <> vv "xs") <> vv "breedtes")
                                                        <> (vv "scheiding138" <> vv "breedtes")
                                               )
                                  )
                     )

        )
  )

expf138 = Binding "writeTable138" writeTable138

