-- 52 Loc

module EncFql9 where

import Types
import Vunify
import Infer
import Basics

  
findField9 = Fix "findField9" $ "aColumnName" \\> "aTable" \\>
  If (vv "null" <> vv "aTable")
     (vv "[]")
     ( If (vv "eqString" <> vv "aColumnName" <> (vv "head" <> (vv "head" <> vv "aTable")))
          (vv "head" <> vv "aTable")
          (vv "findField9" <> vv "aColumnName" <> (vv "tail" <> vv "aTable"))
     )

findFields9 = Fix "findFields9" $
  "aColumns" \\> "aTable" \\>
      If (vv "null" <> vv "aColumns")
      (vv "[]")
      (vv ":" <> (vv "findField9" <> (vv "head" <> vv "aColumns") <> (vv "transpose" <> vv "aTable"))
              <> (vv "findFields9" <> (vv "tail" <> vv "aColumns") <> vv "aTable")
      )


project9 = "aColumns" \\> "aTable" \\>
  vv "transpose" <> (vv "findFields9" <> vv "aColumns" <> vv "aTable")


execQuery9 = "aField" \\>  "aQuery" \\>
  If (vv "aQuery" <> vv "aField")
     (vv "single" <> (vv "single" <> vv "aField"))
     (vv "[]")



column9 = Fix "column9" $
  "aColumn" \\> "aQuery" \\>
      If (vv "null" <> vv "aColumn")
         (vv "[]")
         (vv "++" <> ( vv "execQuery9" <> (vv "head" <> vv "aColumn") <> vv "aQuery")
                  <> (vv "column9" <> (vv "tail" <> vv "aColumn") <> vv "aQuery")
         )


columns9 = "aColumnName" \\> "aFields" \\> "aQuery" \\>
  If (vv "null" <> vv "aFields")
     (vv "[]")
     ( If (vv "eqString" <> (vv "head" <> vv "aFields") <> vv "aColumnName")
          (vv "column9" <> (vv "tail" <> vv "aFields") <> vv "aQuery")
          (vv "[]")
     )


getDataSet9 = Fix "getDataSet9" $ "aColumnName" \\> "aTable" \\> "aQuery" \\>
  If (vv "null" <> vv "aTable")
     (vv "[]")
     (vv "++" <> (vv "columns9" <> vv "aColumnName" <> (vv "head" <> vv "aTable") <> vv "aQuery") 
              <> (vv "getDataSet9" <> vv "aColumnName" <> (vv "tail" <> vv "aTable") <> vv "aQuery")
     )


compareFieldNames9 = Fix "compareFieldNames9" $ "aFieldName" \\> "aFieldNames" \\>
    If (vv "null" <> vv "aFieldNames")
       (vv "[]")
       ( If (vv "eqString" <> vv "aFieldName" <> (vv "head" <> vv "aFieldNames"))
            (vv "head" <> vv "aFieldNames")
            (vv "compareFieldNames9" <> vv "aFieldName" <> (vv "tail" <> vv "aFieldNames"))
       )

findDataSet9 = Fix "findDataSet9" $ "aTable" \\> "aFieldNames" \\>
    If (vv "null" <> vv "aTable")
       (vv "[]")
       ( If (vv "eqString" <> (vv "head" <> vv "aFieldNames") 
                           <> (vv "compareFieldNames9" <> (vv "head" <> vv "aFieldNames") 
                                                        <> (vv "head" <> vv "aTable")))
            (vv "single" <> (vv "head" <> vv "aTable"))
            (vv "findDataSet9" <> (vv "tail" <> vv "aTable") <> vv "aFieldNames")
       )


select9 = "aColumnName" \\> "aQuery" \\> "aTable" \\>
  Let "completeDataSet" ("aFieldNames" @> vv "findDataSet9" <> vv "aTable" <> vv "aFieldNames")
      ( vv ":" <> ( vv "head" <> vv "aTable")
               <> ( vv "concatMap" <> vv "completeDataSet" 
                                   <> (vv "getDataSet9" <> vv "aColumnName" 
                                                         <> (vv "transpose" <> vv "aTable") 
                                                         <> vv "aQuery"))

      )

compareFieldDefs9 = Fix "compareFieldDefs9" $ "lijst1" \\> "lijst2" \\>
    If (vv "null" <> vv "lijst1")
       (vv "[]")
       ( If (vv "eqString" <> (vv "head" <> vv "lijst1")
                           <> ( vv "compareFieldNames9" <> (vv "head" <> vv "lijst1") <> vv "lijst2"))
            (vv "head" <> vv "lijst1")
            (vv "compareFieldDefs9" <> (vv "tail" <> vv "lijst1") <> vv "lijst2")

       )

vindPositie9 = Fix "vindPositie9" $ "lijst1" \\> "naam" \\>
  If (vv "null" <> vv "lijst1")
     i0
     ( If (vv "eqString" <> (vv "head" <> vv "lijst1") <> vv "naam")
          i0
          (vv "+" <> i1 <> (vv "vindPositie9" <> (vv "tail" <> vv "lijst1") <> vv "naam" )) 
     )

remove9 = "lijst1" \\> "lijst2" \\>
  vv "filter" <> (vv "." <> vv "not" 
                         <> (vv "eqString" <> (vv "compareFieldDefs9" <> vv "lijst1" <> vv "lijst2") ))
              <> vv "lijst2"



printHead9 = "lijst1" \\> "lijst2" \\> 
  vv "++" <> vv "lijst1"
          <> (vv "remove9" <> vv "lijst1" <> vv "lijst2")


join9 = "table1" \\> "table2" \\>
      LetList [
             Binding "findField9" findField9
           , Binding "findFields9" findFields9
           , Binding "project9" project9
           , Binding "execQuery9" execQuery9
           , Binding "column9" column9
           , Binding "columns9" columns9
           , Binding "getDataSet9" getDataSet9
           , Binding "compareFieldNames9" compareFieldNames9
           , Binding "findDataSet9" findDataSet9
           , Binding "select9" select9
           , Binding "compareFieldDefs9" compareFieldDefs9
           , Binding "vindPositie9" vindPositie9
           , Binding "remove9" remove9
           , Binding "printHead9" printHead9
           , Binding "joinTables9" joinTables9
           , Binding "remove19" remove19
           , Binding "naam" (vv "compareFieldDefs9" <> (vv "head" <> vv "table1") <> (vv "head" <> vv "table2"))
          ]
      (vv "remove19" <> (vv "transpose" <> (vv "joinTables9" <> vv "table1" <> vv "table2")) <> vv "naam")


expf9 = Binding "join9" join9


-- The translation of joinTables is slightly different from the original program
joinTables9 = "aLeftTable" \\> "aRightTable" \\> 
  LetList [ Binding "common" (vv "compareFieldDefs9" <> (vv "head" <> vv "aLeftTable")
                                                      <> (vv "head" <> vv "aRightTable") )
          , Binding "index1" (vv "vindPositie9" <> (vv "head" <> vv "aLeftTable") <> vv "common")
          , Binding "index2" (vv "vindPositie9" <> (vv "head" <> vv "aRightTable") <> vv "common")
          , Binding "x" (vv "head" <> (vv "tail" <> vv "aLeftTable"))
          , Binding "y" (vv "head" <> (vv "tail" <> vv "aRightTable"))
          ]
          ( If (vv "eqString" <> (vv "!!" <> vv "x" <> vv "index1") 
                              <> (vv "!!" <> vv "y" <> vv "index2"))
               (vv "single" <> vv "x")
               (vv "single" <> vv "y")
          )



remove19 = Fix "remove19" $ "table" \\> "naam" \\>
    If (vv "null" <> vv "table")
       (vv "[]")
       ( If (vv "eqString" <> (vv "head" <> (vv "head" <> vv "table")) <> vv "naam")
            (vv "tail" <> vv "table")
            (vv ":" <> (vv "head" <> vv "table")
                    <> (vv "remove19" <> (vv "tail" <> vv "table") <> vv "naam") )
       )


{-
join9 = "table1" \\> "table2" \\>
  Let "naam" (vv "compareFieldDefs9" <> (vv "head" <> vv "table1") <> (vv "head" <> vv "table2"))
      (vv "remove19" <> (vv "transpose" <> (vv "joinTables9" <> vv "table1" <> vv "table2")) <> vv "naam")
-}

