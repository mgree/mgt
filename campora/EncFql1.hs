-- 20 Loc

module EncFql1 where

import Types
import Vunify
import Infer
import Basics


listLength = "list" \\> vv "map" <> vv "length" <> vv "list"

maxColumnWidth = "column" \\> vv "foldr" <> vv "max" <> i3 <> (vv "listLength" <> vv "column")


maxColumnWidths = 
  Fix "maxColumnWidths" $
    "list" \\> If (vv "null" <> vv "list")
                  (vv "[]")
                  (vv ":" <> (vv "maxColumnWidth" <> (vv "head" <> vv "list"))
                          <> (vv "maxColumnWidths" <> (vv "tail" <> vv "list")))

maxColumnWidths2 = 
  Fix "maxColumnWidths" $
    "list" \\> If (vv "null" <> vv "list")
                  (vv "[]")
                  (vv ":" <> (vv "maxColumnWidth" <> (vv "head" <> vv "list"))
                          <> (vv "maxColumnWidths" <> (vv "tail" <> vv "list")))


newLine = 
  Fix "newLine" $
    "list" \\> If (vv "null" <> vv "list")
                  llc
                  (vv "++" <> llc <> 
                        (vv "++" <> (vv "concat" <> (vv "replicate" <> (vv "head" <> vv "list") <> llc) ) 
                                 <> (vv "newLine" <> (vv "tail" <> vv "list")) ) )

newEntry = "list1" \\> "list2" \\>
              If (vv "null" <> vv "list1")
              llc
              (vv "++" <> llc <> (vv "head" <> vv "list1"))

lengths = vv "maxColumnWidths" <> (vv "transpose" <> vv "table")
writeFieldDefs = 
  "table" \\> If (vv "null" <> vv "table")
                 llc 
                 (LetList [Binding "lengths" lengths] 
                 (vv "++" <> (vv "newLine" <> vv "lengths")
                          <> (vv "++" <> (vv "newEntry" <> (vv "head" <> vv "table") <> vv "lengths") 
                                      <> (vv "newLine" <> vv "lengths")) )
                  )

writeRows = Fix "writeRows" $
  "table" \\> If (vv "null" <> vv "table")
                 llc
                 (
                    LetList [Binding "lengths" lengths]
                    (vv "++" <> (vv "newEntry" <> (vv "head" <> vv "table") <> vv "lengths")
                             <> (vv "writeRows" <> (vv "tail" <> vv "table"))
                    )
                  ) 
                 
writeTable = 
    "table" \\> vv "++" <> (vv "writeFieldDefs" <> (vv "head" <> vv "table")) 
                        <> (vv "writeRows" <> (vv "tail" <> vv "table")) 

writeTable3 = 
    "table" \\> LetList [ Binding "listLength" listLength
                        , Binding "maxColumnWidth" maxColumnWidth
                        , Binding "maxColumnWidths" maxColumnWidths
                        , Binding "newLine" newLine
                        , Binding "newEntry" newEntry
                        , Binding "writeFieldDefs" writeFieldDefs
                        , Binding "writeRows" writeRows]
                (vv "++" <> (vv "writeFieldDefs" <> (vv "head" <> vv "table")) 
                        <> (vv "writeRows" <> (vv "tail" <> vv "table")) )

writeTableBind = Binding "writeTable3" writeTable3

prog3 = Prog [ Binding "listLength" listLength
          , Binding "maxColumnWidth" maxColumnWidth
          , Binding "maxColumnWidths" maxColumnWidths
          , Binding "newLine" newLine
          , Binding "newEntry" newEntry
          , Binding "writeFieldDefs" writeFieldDefs
          , Binding "writeRows" writeRows
          , Binding "writeTable" writeTable]

prog4 = Prog [ Binding "listLength" listLength
          , Binding "maxColumnWidth" maxColumnWidth
          , Binding "maxColumnWidths" maxColumnWidths
          , Binding "newLine" newLine
          , Binding "newEntry" newEntry
          , Binding "writeFieldDefs" writeFieldDefs
          , Binding "writeRows" writeRows
          , Binding "writeTable" writeTable
          ]

{-
type Table = [[String]]

listLength1 lijst = L.map length lijst

maxColumnWidth1 :: [String] -> Int
maxColumnWidth1 column = L.foldr (max) 0 (listLength1 column)

maxColumnWidths1 :: [[String]] -> [Int]
maxColumnWidths1 lijst  | L.null lijst = []
                        | otherwise = maxColumnWidth1 (head lijst) : maxColumnWidths1 (tail lijst)

newLine1 :: [Int] -> String
newLine1 lijst | L.null lijst = "+\n"
               | otherwise = "+" ++ concat (replicate (head lijst)  "-") ++ newLine1 (tail lijst)

newEntry1 :: [String] -> [Int] -> String
newEntry1 lijst1 lijst2 | L.null lijst1 = "|\n"
                        | otherwise = "|" ++ (head lijst1) ++ concat(replicate ((head lijst2) - (length (head lijst1))) " ") ++ newEntry1 (tail lijst1) (tail lijst2)

writeFieldDefs1 :: Table -> String
writeFieldDefs1 table  | L.null table = ""
                       | otherwise  = newLine1 a  ++
                                     newEntry1 (head table) a ++
                                     newLine1 a
                        where a   = maxColumnWidths1 $ transpose table

writeRows1 :: Table -> String
writeRows1 table  | L.null table = ""
                  | otherwise  = newEntry1 (head table) a ++
                                     writeRows1 (tail table)
                        where a   = maxColumnWidths1 $ transpose table

writeTable1 table = writeFieldDefs1 (head undefined) ++ writeRows1 (tail undefined)
-}



















