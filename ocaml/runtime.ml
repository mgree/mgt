type dyn = Bool of bool
         | Int of int
         | String of string
         | Fun of (dyn -> dyn)

type tag = 
    | TBool :tag 
    | TInt : tag
    | TString : tag
    | TFun : tag

exception Coercion_failure of tag * dyn

exception Hole of string

let hole : string -> 'a = fun s -> raise (Hole s)

let tag_of : dyn -> tag = function
    | Bool _   -> TBool
    | Int _    -> TInt
    | String _ -> TString
    | Fun _    -> TFun

let string_of_tag : tag -> string = function
    | TBool -> "bool"
    | TInt -> "int"
    | TString -> "string"
    | TFun -> "fun"

let string_of_dyn : dyn -> string = function
    | Bool b -> if b then "true" else "false"
    | Int i -> string_of_int i
    | String s -> s
    | Fun _ -> "<procedure>"

let check_bool : dyn -> bool = function
    | Bool b -> b
    | v -> raise (Coercion_failure(TBool, v))
let check_int : dyn -> int = function
    | Int i -> i
    | v -> raise (Coercion_failure(TInt, v))    
let check_string : dyn -> string = function
    | String s -> s
    | v -> raise (Coercion_failure(TString, v))    
let check_fun : dyn -> (dyn -> dyn) = function
    | Fun f -> f
    | v -> raise (Coercion_failure(TFun, v))

let tag_bool : bool -> dyn = fun b -> Bool b
let tag_int : int -> dyn = fun i -> Int i
let tag_string : string -> dyn = fun s -> String s
let tag_fun : (dyn -> dyn) -> dyn = fun f -> Fun f

let coerce_id : 'a -> 'a = fun x -> x

let coerce_fun : ('a21 -> 'a11) -> ('a12 -> 'a22) -> ('a11 -> 'a12) -> ('a21 -> 'a22) =
    fun c1 c2 -> fun f -> fun v -> c2 (f (c1 v))

let coerce_seq : ('a -> 'b) -> ('b -> 'c) -> ('a -> 'c) = 
    fun c1 c2 -> fun a -> c2 (c1 a)

let truthy : dyn -> bool = function
    | Bool b -> b
    | Int i -> i <> 0
    | String s -> s <> ""
    | Fun _ -> true

let bop_equaldyn : dyn -> dyn -> bool = fun d1 d2 ->
    match (d1, d2) with
    | (Bool b1, Bool b2) -> b1 = b2
    | (Int i1, Int i2) -> i1 = i2
    | (String s1, String s2) -> s1 = s2
    | (Fun _, _) | (_, Fun _)  -> failwith "please don't try to compare functions, it hurts"
    | (Bool b, v) | (v, Bool b) -> truthy v = b
    | (Int i, String s) | (String s, Int i) ->
        not (truthy d1 || truthy d2) || 
        try i = int_of_string s
        with Failure _ -> false

let int_of_bool b = if b then 1 else 0

let bop_plusdyn : dyn -> dyn -> dyn = fun d1 d2 ->
    match (d1, d2) with
    | (Int i1, Int i2) -> Int (i1 + i2)
    | (Bool b1, Bool b2) -> Int (int_of_bool b1 + int_of_bool b2)
    | (String s1, String s2) -> String (s1 ^ s2)
    | (Fun _, _) | (_, Fun _) -> failwith "please don't try to add functions, it hurts"
    | (v, String s) -> String (string_of_dyn v ^ s)
    | (String s, v) -> String (s ^ string_of_dyn v)
    | (Bool b, Int i) | (Int i, Bool b) -> Int (i + int_of_bool b)
