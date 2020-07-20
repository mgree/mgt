-- 22 Loc

module EncFql42 where

import Types
import Vunify
import Infer
import Basics


{-
expf42 = "table1" \\> "table2" \\>
      LetList [
             Binding "columnWidths12" columnWidths12
          ]
      (vv "remove112" <> (vv "transpose" <> (vv "joinTables12" <> vv "table1" <> vv "table2")) <> vv "naam")

progrep12 = Binding "expf12" expf12

progf12 = Prog $ replicate 330 progrep12
-}



vulAan42 = "kortWoord" \\> "wensLengte" \\>
  Let "n" (vv "-" <> vv "wensLengte" <> (vv "length" <> vv "kortWoord"))
          (vv "++" <> vv "kortWoord" <> (vv "replicate" <> vv "n" <> vc))


schrijfLijn42 = Fix "schrijfLijn42" $ "x" \\> "y" \\>
    If (vv "null" <> vv "x")
       (vv "[]")
       ( If (vv "null" <> vv "y")
            (vv "[]")
            (vv ":" <> vc
                    <> ( vv "++" <> (vv "vulAan42" <> (vv "head" <> vv "y") <> (vv "head" <> vv "x") )
                                 <> (vv "schrijfLijn42" <> (vv "tail" <> vv "x") <> (vv "tail" <> vv "y")  )

                       )
            )
       )

langsteWoorden42 = Fix "langsteWoorden42" $ "xs" \\>
    If (vv "null" <> vv "xs")
       i0
       ( If (vv "==" <> (vv "length" <> vv "xs") <> i1)
            (vv "head" <> vv "xs")
            ( LetList [
                   Binding "hx" (vv "head" <> vv "xs")
                 , Binding "hy" (vv "head" <> (vv "tail" <> vv "xs"))
                 , Binding "txs" (vv "tail" <> (vv "tail" <> vv "xs"))
                ]
                ( If (vv ">" <> vv "hx" <> vv "hy")
                     (vv "langsteWoorden42" <> (vv ":" <> vv "hx" <> vv "txs"))
                     (vv "langsteWoorden42" <> (vv ":" <> vv "hy" <> vv "txs"))
                )
            )

       )


progf42 = Prog [
             Binding "vulAan42" vulAan42
           , Binding "schrijfLijn42" schrijfLijn42
           , Binding "langsteWoorden42" langsteWoorden42
           , Binding "breedteKolom42" breedteKolom42
           , Binding "schrijfBegrenzing42" schrijfBegrenzing42
           , Binding "writeTable42" writeTable42
          ]



breedteKolom42 = vv "." <> ( vv "map" <> (vv "." <> vv "langsteWoorden42"
                                               <> (vv "map" <> vv "length"))
                         ) <> vv "transpose"

schrijfBegrenzing42 = Fix "schrijfBegrenzing42" $ "xs" \\> 
    If (vv "null" <> vv "xs")
       (vv "[]")
       (vv ":" <> vc
               <> ( vv "++" <> (vv "replicate" <> (vv "head" <> vv "xs") <> vc)
                            <> (vv "schrijfBegrenzing42" <> (vv "tail" <> vv "xs"))
                  ))

writeTable42 = "tab" \\>
  LetList [  Binding "vulAan42" vulAan42
           , Binding "schrijfLijn42" schrijfLijn42
           , Binding "langsteWoorden42" langsteWoorden42
           , Binding "breedteKolom42" breedteKolom42
           , Binding "schrijfBegrenzing42" schrijfBegrenzing42
           , Binding "br" (vv "breedteKolom42" <> vv "tab")
           , Binding "str" (vv "head" <> vv "tab") ]
          (vv "++" <> (vv "schrijfLijn42" <> vv "br" <> vv "str") 
                   <> (vv "schrijfBegrenzing42" <> vv "br"))

expf42 = Binding "writeTable42" writeTable42


{-

vulAan :: String -> Int-> String
vulAan kortWoord wensLengte = kortWoord ++ (replicate n ' ')
           where n = wensLengte - length kortWoord

schrijfLijn :: [Int] -> [String] -> String
schrijfLijn [] _ = []
schrijfLijn _ [] = []
schrijfLijn (y:ys) (x:xs) = '|' : (vulAan x y) ++ schrijfLijn ys xs

langsteWoorden :: [Int] -> Int
langsteWoorden [] = 0
langsteWoorden [x] = x
langsteWoorden (x:(y:xs))
                | (x >= y)   = langsteWoorden (x:xs)
                | otherwise  = langsteWoorden (y:xs)

breedteKolom :: Table -> [Int]
breedteKolom = (map (langsteWoorden.(map length)) ).transpose


schrijfBegrenzing :: [Int] -> String
schrijfBegrenzing [] = []
schrijfBegrenzing (x:xs) = '+' : (replicate x '-') ++ schrijfBegrenzing xs


writeTable :: Table -> String
writeTable tab = schrijfLijn br str ++ schrijfBegrenzing br
           where br = breedteKolom tab
                 str = head tab
-}














