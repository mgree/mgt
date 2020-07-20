-- 28 Loc

module EncFql130 where

import Types
import Vunify
import Infer
import Basics


{-

brs         ::        Table -> [Int]
brs t       =       map (maximum.map length) (transpose t)

zetStreepSub :: Table -> String
zetStreepSub [] = ""
zetStreepSub t = "+"
               ++ (replicate ((brs t)!!0) '-')
               ++ zetStreepSub (transpose(tail(transpose t)))

zetStreep :: Table -> String
zetStreep t = zetStreepSub t
              ++ "+\n"


zetRegelSub :: [Int] -> [String] -> String
zetRegelSub (_ : _) [] = ""
zetRegelSub [] (_ : _) = ""
zetRegelSub [] [] = ""
zetRegelSub (b:bs) (x:xs) = "|"
               ++ x
               ++ (replicate (b-length (x)) ' ')
               ++ zetRegelSub bs xs


zetRegel :: [Int] -> [String] -> String
zetRegel bs xs = zetRegelSub bs xs
              ++ "|\n"


writeTable :: Table -> String
writeTable [] = "Empty Table"
writeTable t =         zetStreep t
                    ++ zetRegel (brs t) (head t)
                    ++ zetStreep t
                    ++ concatMap (zetRegel (brs t)) (tail t)
                    ++ zetStreep t               
-}


brs130 = "t" \\>
  vv "map" <> (vv "." <> vv "maximum" <> (vv "map" <> vv "length")) <> (vv "transpose" <> vv "t")

zetStreepSub130 = Fix "zetStreepSub130" $ "t" \\>
    If (vv "null" <> vv "t")
       str
       (vv "++" <> str 
                <> ( vv "++" <> ( vv "replicate" <> (vv "!!" <> (vv "brs130" <> vv "t") <> i0) <> vc )
                             <> (vv "zetStreepSub130" <> (vv "transpose" <> (vv "tail" <> (vv "transpose" <> vv "t"))))
                  ))

               
zetStreep130 = "t" \\>
    vv "++" <> (vv "zetStreepSub130" <> vv "t") <> str              

zetRegelSub130  = Fix "zetRegelSub130" $ "bs" \\> "xs" \\> 
    If (vv "null" <> vv "bs")
       str
       ( If (vv "null" <> vv "xs")
         str
         (vv "++" <> str 
                  <> (vv "++" <> (vv "head" <> vv "xs")
                              <> (vv "++" <> (vv "replicate" <> (vv "-" <> (vv "head" <> vv "bs") 
                                                                        <> (vv "length" <> (vv "head" <> vv "xs")) )
                                                             <> vc)
                                          <> (vv "zetRegelSub130" <> (vv "tail" <> vv "bs") <> (vv "tail" <> vv "xs") ) )
                      )                     
         )
       )


progf130 = Prog [
             Binding "brs130" brs130
           , Binding "zetStreepSub130" zetStreepSub130
           , Binding "zetStreep130" zetStreep130
           , Binding "zetRegelSub130" zetRegelSub130
           , Binding "zetRegel130" zetRegel130
           , Binding "writeTable130" writeTable130
          ]


zetRegel130 = "bs" \\> "xs" \\>
  vv "++" <> (vv "zetRegelSub130" <> vv "bs" <> vv "xs")
          <> str


writeTable130 = "t" \\>
           LetList [
             Binding "brs130" brs130
           , Binding "zetStreepSub130" zetStreepSub130
           , Binding "zetStreep130" zetStreep130
           , Binding "zetRegelSub130" zetRegelSub130
           , Binding "zetRegel130" zetRegel130
           ] 
  (
       If (vv "null" <> vv "t")
       str
       (vv "++" <> ( vv "zetStreep130" <> vv "t")
                <> ( vv "++" <> (vv "zetRegel130" <> (vv "brs130" <> vv "t") <> (vv "head" <> vv "t")) 
                             <> ( vv "++" <> (vv "zetStreep130" <> vv "t")
                                          <> (vv "++" <> (vv "concatMap" <> (vv "zetRegel130" <> (vv "brs130" <> vv "t")) <> (vv "tail" <> vv "t"))
                                                      <> (vv "zetStreep130" <> vv "t")
                                             )
                                )
                   ) 
       )
  )

expf130 = Binding "writeTable130" writeTable130

