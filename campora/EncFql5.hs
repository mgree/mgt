-- 24 Loc

module EncFql5 where

import Types
import Vunify
import Infer
import Basics


columnWidths5 = "aList" \\> vv "map" <> vv "length" <> vv "aList"

maxColumnWidth5 = "aColumn" \\> vv "foldr" <> vv "max" <> i0 <> ( vv "columnWidths5" <> vv "aColumn")

maxColumnWidths5 = 
  Fix "maxColumnWidths5" $
    "aTable" \\> If (vv "null" <> vv "aTable")
                  (vv "[]")
                  (vv ":" <> (vv "maxColumnWidth5" <> (vv "head" <> vv "aTable"))
                          <> (vv "maxColumnWidths5" <> (vv "tail" <> vv "aTable")))  

separator5 = 
  Fix "separator5" $
    "aColumnWidths" \\>
        If (vv "null" <> vv "aColumnWidths")
        str
        (vv "++" <> str 
                 <> (vv "++" <> (vv "concat" <> (vv "replicate" <> (vv "head" <> vv "aColumnWidths") <> str)) 
                             <> (vv "separator5" <> (vv "tail" <> vv "aColumnWidths"))  ) )

separateField5 = 
  Fix "separateField5" $
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
                                         <>  (vv "separateField5" <> (vv "tail" <> vv "aFields") <> (vv "tail" <> vv "aColumnWidths")) 
                                )
                    ) 
        )


writeFieldDefs5 = "aFieldDefs" \\> "aColumnWidths" \\>
  vv "++" <> (vv "separator5" <> vv "aColumnWidths")
          <> (vv "++" <> (vv "separateField5" <> (vv "head" <> vv "aFieldDefs") <> vv "aColumnWidths") 
                      <> (vv "separator5" <> vv "aColumnWidths")
             )


writeDataSet5 = Fix "writeDataSet5" $
  "aDataSet" \\> "aColumnWidths" \\>
        If (vv "null" <> vv "aDataSet")
        (vv "separator5" <> vv "aColumnWidths")
        (vv "++" <> (vv "separateField5" <> (vv "head" <> vv "aDataSet") <> vv "aColumnWidths")
                 <> (vv "writeDataSet5" <> (vv "tail" <> vv "aDataSet") <> vv "aColumnWidths")
        )

writeTable5 = "aTable" \\>
        LetList [
             Binding "columnWidths5" columnWidths5
           , Binding "maxColumnWidth5" maxColumnWidth5  
           , Binding "maxColumnWidths5" maxColumnWidths5
           , Binding "separator5" separator5
           , Binding "separateField5" separateField5
           , Binding "writeFieldDefs5" writeFieldDefs5
           , Binding "writeDataSet5" writeDataSet5
           , Binding "aColumnWidths" (vv "maxColumnWidths5" <> (vv "transpose" <> vv "aTable"))
          ]
      (vv "++" <> (vv "writeFieldDefs5" <> vv "aTable" <> vv "aColumnWidths")
               <> (vv "writeDataSet5" <> (vv "tail" <> vv "aTable") <> vv "aColumnWidths")
      )

expf5 = Binding "writeTable5" writeTable5

















