module Eval where

import Types
import Vunify
import Infer
import Basics

import EncFql5
import EncFql9
import EncFql12
import EncFql1
import EncFql42
import EncFql130
import EncFql132
import EncFql138
import EncFql147
import EncFql156


import Data.List as L
import Data.Map as M
import Data.Set as S
import Data.Time.Clock
import Control.Monad.State
import System.Random

import Prelude as P


unify t1 t2 = do
    let ((sub,tp,t),(_,_,_,oc,log,locs)) = runState (vjoin t1 t2) (0,0,initChg,initChg,[],initChg)

    putStrLn $ "Unifying: \n" ++ show t1 ++ "\n" ++ show t2 

    putStrLn $ "\nUnifier: " ++ showSub sub

    putStrLn $ "Pattern: " ++ show tp

    putStrLn $ "Join type: " ++ show t

seed e = do
    let leaves = numLeaves e
    let numChgs = 2 * fromIntegral leaves / 100 + 2

    places <- mapM (const (randomRIO (1,leaves :: Int))) [1..numChgs]
    return $ replace (L.sort places) e

tieCore env e = do
    let (Tvar i) = S.findMin (S.singleton t0 `S.union` fvs env)

    let ((sub,t,tp),(_,_,_,oc,log,locs)) = runState (infer env e) (i,0,initChg,initChg,[],initChg)
    putStrLn $ "\nResult type:\n" ++ show t

    return (nve tp)

bruteForce env el = do
    st <- getCurrentTime
    let space = concatMap annotSpace el
    mapM_ (tieCore env) space
    tt <- getCurrentTime

    return (diffUTCTime tt st)

gradual env el = do
    pret <- getCurrentTime
    let _ = L.map  (head . annotSpace) el
    st <- getCurrentTime
    mapM_ (tieCore env . head . annotSpace) el
    tt <- getCurrentTime

    return ((diffUTCTime tt st) - diffUTCTime st pret)

migrational env el = do
    st <- getCurrentTime
    numBest <- mapM (tieCore env) el
    tt <- getCurrentTime

--     putStrLn "Elapsed time: "
    return (diffUTCTime tt st, sum numBest `div` length el)

measure el = do

  tbf <- bruteForce tenv el
  tov <- gradual tenv el
  (tm, numBest) <- migrational tenv el

  let len = length el

  putStrLn "\n\nSummary of evaluation...."
  putStrLn $ "Brute force time duration: " ++ show (realToFrac tbf/fromIntegral len)++ "s"
  putStrLn $ "Gradua time duraiton: " ++ show (realToFrac tov/fromIntegral len)++ "s"
  putStrLn $ "Migrational time duration: " ++ show (realToFrac tm/fromIntegral len)++ "s"
  putStrLn $ "# of Best migration: " ++ show numBest

measureMG el = do

  (tm,numBest) <- migrational tenv el

  tov <- gradual tenv el

  let len = length el

  putStrLn "\n\nSummary of evaluation...."
  putStrLn $ "Gradual time duration: " ++ show (realToFrac tov/fromIntegral len) ++ "s"
  putStrLn $ "Migrational time duration: " ++ show (realToFrac tm/fromIntegral len) ++ "s"
  putStrLn $ "# of Best migration: " ++ show numBest


sizes = [80, 20, 28, 52, 24, 23, 36, 56, 24, 20]
progs = [progrep12,expf42,expf130, expf9, expf132,expf138,expf147,expf156,expf5, writeTableBind]


-- The main entry for measuring the performance. The first parameter denotes the
-- size of the program (in LOC), such as 10000, 20000, 30000, etc. The second parameter
-- represents how many programs of the specified size need to be generated. 

measureRand target times = do

    -- Generate size specification, using the encoded programs
    configs <- replicateM times (combine sizes target) 

    -- Generate testing programs
    let testprogs = L.map (\config -> Prog . concat $ zipWith replicate config progs) configs

    -- Seed errors
    withErrs <- mapM seed testprogs
    
    -- Call the migrational and gradual inference algorithms
    measureMG withErrs

    -- display results
    let avgSz = sum ( L.map (\config -> sum $ zipWith (*) config sizes) configs) `div` times

    putStrLn $ "Average LOC: " ++ show avgSz
    putStrLn $ "Average # of funcs: " ++ show ((sum . L.map numFuncs) withErrs `div` times)
    putStrLn $ "Average # of dynamic args: " ++ show ((sum . L.map numDArgs) withErrs `div` times)



-- Measure the performance, including the brute-force approach, and is thus not scalable
measureRandBruteForce target times = do
    configs <- replicateM times (combine sizes target) 
    let testprogs = L.map (\config -> Prog . concat $ zipWith replicate config progs) configs

    withErrs <- mapM seed testprogs
    
    measure withErrs

    let avgSz = sum ( L.map (\config -> sum $ zipWith (*) config sizes) configs) `div` times

    putStrLn $ "Average LOC: " ++ show avgSz
    putStrLn $ "Average # of funcs: " ++ show ((sum . L.map numFuncs) withErrs `div` times)
    putStrLn $ "Average # of dynamic args: " ++ show ((sum . L.map numDArgs) withErrs `div` times)



-- The function determines how to generate program with a given number of LOC

combine :: [Int] -> Int -> IO [Int]

combine (sz:[]) target = do
    return [target `div` sz]

combine (sz:szs) target = do
    cnt <- if sz > target then return 1
                   else randomRIO (2,2*target `div` sum (sz:szs))

    putStrLn . show $ cnt 
    rest <- if cnt == 1 then (return $ replicate (length szs) 0)
                        else combine szs (target - cnt*sz)

    return (cnt:rest)

combine [] _ = return []

-- The initial type environment
tenv = 
 [("succ", Tint ->> Tint),
  ("odd", Tint ->> Tbool), 
  ("even", Tint ->> Tbool),
  ("not", Tbool ->> Tbool),
  ("+", Tint ->> Tint ->> Tint),
  ("*", Tint ->> Tint ->> Tint),
  ("cmp",Tint ->> Tint ->> Tbool), 
  (":", Forall [t0] (t0 ->> Tlist t0 ->> Tlist t0)), 
  ("tail", Forall [t0] (Tlist t0 ->> Tlist t0)), 
  ("null", Forall [t0] (Tlist t0 ->> Tbool)),
  ("head", Forall [t0] (Tlist t0 ->> t0)),
  ("single", Forall [t0] (t0 ->> Tlist t0) ),
  ("concat", Forall [t0] (Tlist (Tlist t0) ->> Tlist t0)), 
  ("transpose", Forall [t0] (Tlist (Tlist t0) ->> Tlist (Tlist t0))), 
  ("++", Forall [t0] (Tlist t0 ->> Tlist t0 ->> Tlist t0)), 
  (":'", Forall [t0] (Tlist t0 ->> t0 ->> Tlist t0)), 
  ("[]",Forall [t0] (Tlist t0)),
  ("-", Tint ->> Tint ->> Tint),
  ("<=",Tint ->> Tint ->>Tbool),
  (">",Tint ->> Tint ->>Tbool), 
  ("foldl", Forall [t0,t1] ((t0 ->> t1 ->> t0) ->> t0 ->> (Tlist t1) ->> t0) ),
  ("foldr", Forall [t0,t1] ((t0 ->> t1 ->> t1) ->> t1 ->> (Tlist t0) ->> t1) ),
  ("map", Forall [t0,t1] ((t0 ->> t1) ->> (Tlist t0) ->> Tlist t1)),
  ("concatMap", Forall [t0,t1] ((t0 ->> Tlist t1) ->> (Tlist t0) ->> Tlist t1 )),
  ("length", Forall [t0] (Tlist t0 ->> Tint)),
  ("maximum", Tlist Tint ->> Tint),
  ("max", Forall [t0] (t0 ->> t0 ->> t0)),
  ("replicate", Forall [t0] (Tint ->> t0 ->> Tlist t0)), 
  ("repeat", Forall [t0] (t0 ->> Tlist t0) ),
  ("take", Forall [t0] (Tint ->> Tlist t0 ->> Tlist t0)),
  ("drop", Forall [t0] (Tint ->> Tlist t0 ->> Tlist t0)),
  ("ilist", Tlist Tint),
  ("lli", Tlist (Tlist Tint)),
  ("llc", Tlist (Tlist Tchar)),
  ("tbl", Tlist (Tlist (Tlist Tchar))),
  ("eqString", Tlist Tchar ->> Tlist Tchar ->> Tbool),
  ("str", Tlist Tchar),
  ("filter", Forall [t0] ((t0 ->> Tbool) ->> (Tlist t0) ->> Tlist t0 ) ),
  (".", Forall [t0,t1,t2] ((t0 ->> t1) ->> (t2 ->> t0) ->> t2 ->> t1) ),
  ("zelfdeVeld", (Tlist (Tlist (Tlist Tchar)) ->> Tlist (Tlist (Tlist Tchar)) ->> Tlist Tchar) ),
  -- Patterns
  ("patint", Tint ->> Tint),
  ("triple", Forall [t0,t1,t2] (t0 ->> t1 ->> t2 ->> Tcon "(,,)" [t0,t1,t2])),
  ("tuple", Forall [t0,t1] (t0 ->> t1 ->> Tcon "(,)" [t0,t1])),
  ("==", Forall [t0] (t0 ->> t0 ->> Tbool)),
  ("&&", Tbool ->> Tbool ->> Tbool),
  ("!!", Forall [t0] (Tlist t0 ->> Tint ->> t0))
 ]




widest = vv "maximum" <> (vv "map" <> vv "length" <> vv "table")
row = vv "!!" <> vv "table" <> vv "i"
width = If (vv "fixed")
           (vv "widthFunc" <> vv "fixed")
           (vv "widthFunc" <> vv "widest")

bind1 = Binding "widest" widest
bind2 = Binding "row" row
bind3 = Binding "width" width

thenb = vv "replicate" <> (vv "+" <> vv "width" <> i2) <> vv "border"
elseb = vv "++" <> vv "border" <> (vv "++" <> inner <> vv "border")
inner = vv "take" <> vv "width" <> 
        (vv "++" <> vv "row" <> (vv "replicate" <> (vv "-" <> vv "width" <> (vv "length" <> vv "row")) <>  vc))

body = If (vv "hdOrBt")
          thenb 
          elseb

rowAtIChc = "hdOrBt" @> "fixed" \\> "widthFunc" \\> "table" 
         \\> "border" \\> "i" \\> LetList [bind1, bind2, bind3] body

rowAtI = "hdOrBt" @> "fixed" \> "widthFunc" \> "table" 
         \> "border" \> "i" \> LetList [bind1, bind2, bind3] body

rowAtIInf = "hdOrBt" @> "fixed" @> "widthFunc" @> "table" 
            @> "border" @> "i" @> LetList [bind1, bind2, bind3] body

-- 63 LOC
rowAtIChcBogus = "hdOrBt" @> "fixed" \\> "widthFunc" \\> "table" 
         \\> "border" \\> "i" \\> LetList (replicate 20 bind1 ++ 
                                           replicate 20 bind2 ++ 
                                           replicate 20 bind3) body



row1 = Binding "rowAtIChc" rowAtIChc

-- 63 LOC
row2 = Binding "rowAtIChcBogus" rowAtIChcBogus

prog1 = Prog [row1,row1]

f = "x" \> "func" \> If (vv "x") (vv "func" <> vv "x") (vv "func" <> i3)
fChc = "x" \\> "func" \\> If (vv "x") (vv "func" <> vv "x") (vv "func" <> i3)

barChc = "c" \\> "b" \\> If (vv "c") (vv "b" <> vv "c") (vv "b" <> (vv "+" <> vv "c" <> i1))

prog2 = Prog [Binding "fChc" fChc, Binding "barChc" barChc]


prog9 = Prog (replicate 400 row1)

prog10 = Prog (replicate 4000 row1)

prog11 = Prog (replicate 40000 row1)

-- 237 LOC
prog12 = Prog (replicate 9 writeTableBind ++ replicate 12 row1)

-- 126 Loc
prog13 = Prog (replicate 2 row2)

prog15 = Prog (replicate 300 writeTableBind ++ replicate 50 row2)


-- 40,000 Loc

progcomb = Prog (replicate 1200 writeTableBind ++ replicate 300 progrep12)


prog5 = Prog [writeTableBind, writeTableBind, writeTableBind]

prog6 = Prog (replicate 50 writeTableBind ++ replicate 20 row2)

prog7 = Prog (replicate 1000 writeTableBind)

-- 10,000 LOC
prog16 = Prog (replicate 600 writeTableBind)

-- 20,000 LOC
prog17 = Prog (replicate 1200 writeTableBind)


prog8 = Prog (replicate 10000 writeTableBind)

prog14 = Prog (replicate 500 writeTableBind)




