-- 80 Loc

module EncFql12 where

import Types
import Vunify
import Infer
import Basics


columnWidths12 = "aList" \\> vv "map" <> vv "length" <> vv "aList"

maxColumnWidth12 = "aColumn" \\> vv "foldr" <> vv "max" <> i0 <> ( vv "columnWidths12" <> vv "aColumn")

maxColumnWidths12 = 
  Fix "maxColumnWidths12" $
    "aTable" \\> If (vv "null" <> vv "aTable")
                  (vv "[]")
                  (vv ":" <> (vv "maxColumnWidth12" <> (vv "head" <> vv "aTable"))
                          <> (vv "maxColumnWidths12" <> (vv "tail" <> vv "aTable")))  

separator12 = 
  Fix "separator12" $
    "aColumnWidths" \\>
        If (vv "null" <> vv "aColumnWidths")
        str
        (vv "++" <> str 
                 <> (vv "++" <> (vv "concat" <> (vv "replicate" <> (vv "head" <> vv "aColumnWidths") <> str)) 
                             <> (vv "separator12" <> (vv "tail" <> vv "aColumnWidths"))  ) )

separateField12 = 
  Fix "separateField12" $
    "aFields" \\> "aColumnWidths" \\>
        If (vv "null" <> vv "aFields")
        str
        (vv "++" <> str 
                 <> (vv "++" <> (vv "head" <> vv "aFields") 
                             <> (vv "++" <> (vv "concat" <> (vv "replicate" 
                                                 <> (vv "-"  
                                                      <> (vv "head" <> vv "aColumnWidths") 
                                                      <> (vv "length" <> (vv "head" <> vv "aFields") )
                                                    )
                                                 <> str) 
                                             )
                                         <>  (vv "separateField12" <> (vv "tail" <> vv "aFields") <> (vv "tail" <> vv "aColumnWidths")) 
                                )
                    ) 
        )


writeFieldDefs12 = "aFieldDefs" \\> "aColumnWidths" \\>
  vv "++" <> (vv "separator12" <> vv "aColumnWidths")
          <> (vv "++" <> (vv "separateField12" <> (vv "head" <> vv "aFieldDefs") <> vv "aColumnWidths") 
                      <> (vv "separator12" <> vv "aColumnWidths")
             )


writeDataSet12 = Fix "writeDataSet12" $
  "aDataSet" \\> "aColumnWidths" \\>
        If (vv "null" <> vv "aDataSet")
        (vv "separator12" <> vv "aColumnWidths")
        (vv "++" <> (vv "separateField12" <> (vv "head" <> vv "aDataSet") <> vv "aColumnWidths")
                 <> (vv "writeDataSet12" <> (vv "tail" <> vv "aDataSet") <> vv "aColumnWidths")
        )

writeTable12 = "aTable" \\>
  Let "aColumnWidths" 
      (vv "maxColumnWidths12" <> (vv "transpose" <> vv "aTable"))
      (vv "++" <> (vv "writeFieldDefs12" <> vv "aTable" <> vv "aColumnWidths")
               <> (vv "writeDataSet12" <> (vv "tail" <> vv "aTable") <> vv "aColumnWidths")
      )
            

findField12 = Fix "findField12" $ "aColumnName" \\> "aTable" \\>
  If (vv "null" <> vv "aTable")
     (vv "[]")
     ( If (vv "eqString" <> vv "aColumnName" <> (vv "head" <> (vv "head" <> vv "aTable")))
          (vv "head" <> vv "aTable")
          (vv "findField12" <> vv "aColumnName" <> (vv "tail" <> vv "aTable"))
     )

findFields12 = Fix "findFields12" $
  "aColumns" \\> "aTable" \\>
      If (vv "null" <> vv "aColumns")
      (vv "[]")
      (vv ":" <> (vv "findField12" <> (vv "head" <> vv "aColumns") <> (vv "transpose" <> vv "aTable"))
              <> (vv "findFields12" <> (vv "tail" <> vv "aColumns") <> vv "aTable")
      )


project12 = "aColumns" \\> "aTable" \\>
  vv "transpose" <> (vv "findFields12" <> vv "aColumns" <> vv "aTable")


execQuery12 = "aField" \\>  "aQuery" \\>
  If (vv "aQuery" <> vv "aField")
     (vv "single" <> (vv "single" <> vv "aField"))
     (vv "[]")



column12 = Fix "column12" $
  "aColumn" \\> "aQuery" \\>
      If (vv "null" <> vv "aColumn")
         (vv "[]")
         (vv "++" <> ( vv "execQuery12" <> (vv "head" <> vv "aColumn") <> vv "aQuery")
                  <> (vv "column12" <> (vv "tail" <> vv "aColumn") <> vv "aQuery")
         )


columns12 = "aColumnName" \\> "aFields" \\> "aQuery" \\>
  If (vv "null" <> vv "aFields")
     (vv "[]")
     ( If (vv "eqString" <> (vv "head" <> vv "aFields") <> vv "aColumnName")
          (vv "column12" <> (vv "tail" <> vv "aFields") <> vv "aQuery")
          (vv "[]")
     )


getDataSet12 = Fix "getDataSet12" $ "aColumnName" \\> "aTable" \\> "aQuery" \\>
  If (vv "null" <> vv "aTable")
     (vv "[]")
     (vv "++" <> (vv "columns12" <> vv "aColumnName" <> (vv "head" <> vv "aTable") <> vv "aQuery") 
              <> (vv "getDataSet12" <> vv "aColumnName" <> (vv "tail" <> vv "aTable") <> vv "aQuery")
     )


compareFieldNames12 = Fix "compareFieldNames12" $ "aFieldName" \\> "aFieldNames" \\>
    If (vv "null" <> vv "aFieldNames")
       (vv "[]")
       ( If (vv "eqString" <> vv "aFieldName" <> (vv "head" <> vv "aFieldNames"))
            (vv "head" <> vv "aFieldNames")
            (vv "compareFieldNames12" <> vv "aFieldName" <> (vv "tail" <> vv "aFieldNames"))
       )

findDataSet12 = Fix "findDataSet12" $ "aTable" \\> "aFieldNames" \\>
    If (vv "null" <> vv "aTable")
       (vv "[]")
       ( If (vv "eqString" <> (vv "head" <> vv "aFieldNames") 
                           <> (vv "compareFieldNames12" <> (vv "head" <> vv "aFieldNames") 
                                                        <> (vv "head" <> vv "aTable")))
            (vv "single" <> (vv "head" <> vv "aTable"))
            (vv "findDataSet12" <> (vv "tail" <> vv "aTable") <> vv "aFieldNames")
       )


select12 = "aColumnName" \\> "aQuery" \\> "aTable" \\>
  Let "completeDataSet" ("aFieldNames" @> vv "findDataSet12" <> vv "aTable" <> vv "aFieldNames")
      ( vv ":" <> ( vv "head" <> vv "aTable")
               <> ( vv "concatMap" <> vv "completeDataSet" 
                                   <> (vv "getDataSet12" <> vv "aColumnName" 
                                                         <> (vv "transpose" <> vv "aTable") 
                                                         <> vv "aQuery"))

      )

compareFieldDefs12 = Fix "compareFieldDefs12" $ "lijst1" \\> "lijst2" \\>
    If (vv "null" <> vv "lijst1")
       (vv "[]")
       ( If (vv "eqString" <> (vv "head" <> vv "lijst1")
                           <> ( vv "compareFieldNames12" <> (vv "head" <> vv "lijst1") <> vv "lijst2"))
            (vv "head" <> vv "lijst1")
            (vv "compareFieldDefs12" <> (vv "tail" <> vv "lijst1") <> vv "lijst2")

       )

vindPositie12 = Fix "vindPositie12" $ "lijst1" \\> "naam" \\>
  If (vv "null" <> vv "lijst1")
     i0
     ( If (vv "eqString" <> (vv "head" <> vv "lijst1") <> vv "naam")
          i0
          (vv "+" <> i1 <> (vv "vindPositie12" <> (vv "tail" <> vv "lijst1") <> vv "naam" )) 
     )

remove12 = "lijst1" \\> "lijst2" \\>
  vv "filter" <> (vv "." <> vv "not" 
                         <> (vv "eqString" <> (vv "compareFieldDefs12" <> vv "lijst1" <> vv "lijst2") ))
              <> vv "lijst2"



printHead12 = "lijst1" \\> "lijst2" \\> 
  vv "++" <> vv "lijst1"
          <> (vv "remove12" <> vv "lijst1" <> vv "lijst2")


{-
progf12 = Prog [
             Binding "columnWidths12" columnWidths12
           , Binding "maxColumnWidth12" maxColumnWidth12  
           , Binding "maxColumnWidths12" maxColumnWidths12
           , Binding "separator12" separator12
           , Binding "separateField12" separateField12
           , Binding "writeFieldDefs12" writeFieldDefs12
           , Binding "writeDataSet12" writeDataSet12
           , Binding "writeTable12" writeTable12
           , Binding "findField12" findField12
           , Binding "findFields12" findFields12
           , Binding "project12" project12
           , Binding "execQuery12" execQuery12
           , Binding "column12" column12
           , Binding "columns12" columns12
           , Binding "getDataSet12" getDataSet12
           , Binding "compareFieldNames12" compareFieldNames12
           , Binding "findDataSet12" findDataSet12
           , Binding "select12" select12
           , Binding "compareFieldDefs12" compareFieldDefs12
           , Binding "vindPositie12" vindPositie12
           , Binding "remove12" remove12
           , Binding "printHead12" printHead12
           , Binding "joinTables12" joinTables12
           , Binding "remove112" remove112
           , Binding "join12" join12
          ]
-}

expf12 = "table1" \\> "table2" \\>
      LetList [
             Binding "columnWidths12" columnWidths12
           , Binding "maxColumnWidth12" maxColumnWidth12  
           , Binding "maxColumnWidths12" maxColumnWidths12
           , Binding "separator12" separator12
           , Binding "separateField12" separateField12
           , Binding "writeFieldDefs12" writeFieldDefs12
           , Binding "writeDataSet12" writeDataSet12
           , Binding "writeTable12" writeTable12
           , Binding "findField12" findField12
           , Binding "findFields12" findFields12
           , Binding "project12" project12
           , Binding "execQuery12" execQuery12
           , Binding "column12" column12
           , Binding "columns12" columns12
           , Binding "getDataSet12" getDataSet12
           , Binding "compareFieldNames12" compareFieldNames12
           , Binding "findDataSet12" findDataSet12
           , Binding "select12" select12
           , Binding "compareFieldDefs12" compareFieldDefs12
           , Binding "vindPositie12" vindPositie12
           , Binding "remove12" remove12
           , Binding "printHead12" printHead12
           , Binding "joinTables12" joinTables12
           , Binding "remove112" remove112
           , Binding "naam" (vv "compareFieldDefs12" <> (vv "head" <> vv "table1") <> (vv "head" <> vv "table2"))
          ]
      (vv "remove112" <> (vv "transpose" <> (vv "joinTables12" <> vv "table1" <> vv "table2")) <> vv "naam")

progrep12 = Binding "expf12" expf12

progf12 = Prog $ replicate 330 progrep12



-- The translation of joinTables is slightly different from the original program
joinTables12 = "aLeftTable" \\> "aRightTable" \\> 
  LetList [ Binding "common" (vv "compareFieldDefs12" <> (vv "head" <> vv "aLeftTable")
                                                      <> (vv "head" <> vv "aRightTable") )
          , Binding "index1" (vv "vindPositie12" <> (vv "head" <> vv "aLeftTable") <> vv "common")
          , Binding "index2" (vv "vindPositie12" <> (vv "head" <> vv "aRightTable") <> vv "common")
          , Binding "x" (vv "head" <> (vv "tail" <> vv "aLeftTable"))
          , Binding "y" (vv "head" <> (vv "tail" <> vv "aRightTable"))
          ]
          ( If (vv "eqString" <> (vv "!!" <> vv "x" <> vv "index1") 
                              <> (vv "!!" <> vv "y" <> vv "index2"))
               (vv "single" <> vv "x")
               (vv "single" <> vv "y")
          )



remove112 = Fix "remove112" $ "table" \\> "naam" \\>
    If (vv "null" <> vv "table")
       (vv "[]")
       ( If (vv "eqString" <> (vv "head" <> (vv "head" <> vv "table")) <> vv "naam")
            (vv "tail" <> vv "table")
            (vv ":" <> (vv "head" <> vv "table")
                    <> (vv "remove112" <> (vv "tail" <> vv "table") <> vv "naam") )
       )


join12 = "table1" \\> "table2" \\>
  Let "naam" (vv "compareFieldDefs12" <> (vv "head" <> vv "table1") <> (vv "head" <> vv "table2"))
      (vv "remove112" <> (vv "transpose" <> (vv "joinTables12" <> vv "table1" <> vv "table2")) <> vv "naam")


{-

columnWidths aList = map length aList

maxColumnWidth aColumn = foldr (max) 0 (columnWidths aColumn)

maxColumnWidths :: Table -> [Int]

maxColumnWidths aTable | null aTable = []
                       | otherwise = maxColumnWidth (head aTable) : maxColumnWidths (tail aTable)

separator :: [Int] -> String

separator aColumnWidths | null aColumnWidths = "+\n"
                        | otherwise = "+" ++ concat (replicate (head aColumnWidths) "-") 
                                          ++ separator (tail aColumnWidths)

separateField :: [String] -> [Int] -> String

separateField aFields aColumnWidths 
  | null aFields = "|\n"
  | otherwise = "|" ++ (head aFields) 
                    ++ concat(replicate ((head aColumnWidths)-(length (head aFields))) " ") 
                    ++ separateField (tail aFields) (tail aColumnWidths)

writeFieldDefs :: Table -> [Int] -> String

writeFieldDefs aFieldDefs aColumnWidths = 
  separator aColumnWidths ++ separateField (head aFieldDefs) aColumnWidths ++ 
                             separator aColumnWidths


writeDataSet :: Table -> [Int] -> String

writeDataSet aDataSet aColumnWidths | null aDataSet = separator aColumnWidths
                                    | otherwise = separateField (head aDataSet) aColumnWidths 
                                                  ++ writeDataSet (tail aDataSet) aColumnWidths

writeTable :: Table -> String
writeTable aTable = writeFieldDefs aTable aColumnWidths ++ writeDataSet (tail aTable) aColumnWidths
   where aColumnWidths = maxColumnWidths (transpose aTable)


findField :: String -> Table -> [String]

findField aColumnName aTable | null aTable = []
                             | eqString aColumnName (head (head aTable)) = head aTable
                             | otherwise = findField aColumnName (tail aTable)

findFields :: [String] -> Table -> Table

findFields aColumns aTable | null aColumns  = []
                           | otherwise = findField (head aColumns) (transpose aTable) 
                                         : findFields (tail aColumns) aTable

project aColumns aTable = transpose (findFields aColumns aTable)

execQuery :: String -> (String -> Bool) -> Table

execQuery aField aQuery | aQuery aField = [[aField]]
                        | otherwise = []

column :: [String] -> (String -> Bool) -> Table

column aColumn aQuery | null aColumn = []
                      | otherwise = execQuery (head aColumn) aQuery ++ column (tail aColumn) aQuery


columns :: String -> [String] -> (String -> Bool) -> Table

columns aColumnName aFields aQuery | null aFields = []
                                   | eqString (head aFields) aColumnName = column (tail aFields) aQuery
                                   | otherwise = []

getDataSet :: String -> Table -> (String -> Bool) -> Table

getDataSet aColumnName aTable aQuery | null aTable = []
                                     | otherwise = columns aColumnName (head (aTable)) aQuery 
                                       ++ getDataSet aColumnName (tail (aTable)) aQuery


compareFieldNames aFieldName aFieldNames | null aFieldNames = []
                                         | eqString aFieldName (head aFieldNames) = head aFieldNames
                                         | otherwise = compareFieldNames aFieldName (tail aFieldNames)

findDataSet :: Table -> [String] -> Table

findDataSet aTable aFieldNames | null aTable = []
                               | eqString (head aFieldNames) (compareFieldNames (head aFieldNames) (head aTable)) = [head aTable]
                               | otherwise = findDataSet (tail aTable) aFieldNames

select :: String -> (String -> Bool) -> Table -> Table
select aColumnName aQuery aTable = 
  head aTable : concatMap completeDataSet (getDataSet aColumnName (transpose aTable) aQuery)
   where completeDataSet aFieldNames = findDataSet aTable aFieldNames


compareFieldDefs :: [String] -> [String] -> String
compareFieldDefs lijst1 lijst2 | null lijst1 = []
                               | eqString (head lijst1) (compareFieldNames (head lijst1) lijst2) = (head lijst1)
                               | otherwise = compareFieldDefs (tail lijst1) lijst2


vindPositie :: [String] -> String -> Int
vindPositie lijst1 naam | null lijst1 = 0
                       | eqString (head lijst1) naam = 0
                       | otherwise = 1 + vindPositie (tail lijst1) naam


remove :: [String] -> [String] -> [String]
remove lijst1 lijst2 =  filter (not.eqString (compareFieldDefs lijst1 lijst2)) lijst2


printHead :: [String] -> [String] -> [String]
printHead lijst1 lijst2 = lijst1 ++ remove lijst1 lijst2

joinTables :: Table -> Table -> Table
joinTables aLeftTable aRightTable =  [x++y | x <- (tail aLeftTable), y <- (tail aRightTable), 
                                             eqString (x !! index1) (y !! index2)]
   where common = compareFieldDefs (head aLeftTable) (head aRightTable)
         index1 = vindPositie (head aLeftTable) common
         index2 = vindPositie (head aRightTable) common


remove1 :: Table -> String -> Table
remove1 table naam | null table = []
                   | eqString (head (head table)) naam = tail table
                   | otherwise = (head table) : remove1 (tail table) naam


join :: Table -> Table -> Table
join table1 table2 = remove1 (transpose(joinTables table1 table2)) naam
        where naam =  compareFieldDefs (head table1) (head table2)
-}
