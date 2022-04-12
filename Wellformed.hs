module Wellformed where

import Data.Monoid as Monoid
import QIO.QioSyn as QS
import QIO.Qdata
import QIO.QioClass
import QIO.Qio
import QIO.QArith as QQA
import Data.Angle as Angle 

import Data

--Hauptfunktion für LExp
wellformed:: LExp String -> [String] -> Bool
wellformed expr vars = check_wellformed expr context vars
    where context = []

--Nur auf Funktionskörper anwenden, Rest egal
check_wellformed:: LExp String -> [LExp String] -> [String] -> Bool  --expr, context, vars für contraction wie bei rename
check_wellformed (Var var ) context vars = check_wellformed' (Var var) context vars --False wenn Wellformed freie vars ohne Bindung rauswerfen soll
check_wellformed (Quantum(q)) context vars = True
check_wellformed (Excl(e)) context vars = check_wellformed' (Excl(e)) context vars
check_wellformed (Lambda v e) context vars = check_wellformed' (Lambda v e) context vars 
check_wellformed (Excl_Lambda v e) context vars = check_wellformed' (Excl_Lambda v e) context vars 

check_wellformed (App e1 e2) context vars = check_wellformed e1 context vars && check_wellformed e2 context vars 

--1) Const, ID, Pomotion 
--2) Dereliction, Contraction, Weakening
--3) oI, -I, oE(LExp String(Term), [LExp String](context),[String](für rename in contraction))
check_wellformed' :: LExp String -> [LExp String] -> [String] -> Bool

--guard macht Overlapping-pattern  weg
check_wellformed' expr context vars
  | (check_contraction expr context)  =
    let var = get_contraction_var expr context --contraction
        context' = drop_context context var
        (expr', context'',vars') = contraction expr context' var vars 
    in check_wellformed' expr' context'' vars'

check_wellformed' (P_h) context vars --leere Ableitung nach Id
  | (null context) = True
  | otherwise = False --vielleicht weakening erst hier

check_wellformed' (Quantum q) context vars  --const
  | check_weakening (Quantum q) context = --gleiches wie bei (Var var)
    let context' = do_weakening (Quantum(q)) context
    in check_wellformed' (Quantum(q)) context' vars
  | (null context) = True
  | otherwise = False

check_wellformed' (Var var) context vars  
  | in_context context (Excl(Var var)) =  --dereliction muss vorher, wenn nur noch Var und ein Excl var in context
    let context' = drop_context context (Excl(Var var))
        context'' = context' ++ [(Var var)]
    in check_wellformed' (Var var) context'' vars

  | check_weakening (Var var) context =  --gleiches bei Weakening
    let context' = do_weakening (Var var) context
    in check_wellformed' (Var var) context' vars

  | in_context context (Var var) = check_wellformed' (P_h) (drop_context context (Var var)) vars --wenn Id zu früh, wird der Kontext nicht mehr abgecheckt

  | otherwise = False

check_wellformed' (Lambda v e) context vars = check_wellformed' e ([(Var v)] ++ context) vars -- oI

check_wellformed' (Excl_Lambda v e) context vars= check_wellformed' e ([Excl(Var v)] ++ context) vars  -- -I

check_wellformed' expr context vars
  | is_excl expr  && allnonlinear context  = check_wellformed' (return_no_excl expr) context vars --Pomotion 

  | app_form expr  =    -- -oE
    let(e1',context1,e2',context2) = divide_context expr context 
       b = distinct context1 context2 
    in check_wellformed' e1' context1 vars && check_wellformed' e2' context2 vars && b 

  | otherwise = False

--nur für App(e1 e2) aufrufen!
--an freie Excl(Var v),(Var v) denken
----------------------------------------------------------------
-- oE

distinct::[LExp String] -> [LExp String] -> Bool
distinct  x [] = True
distinct x (y:ys) 
  | in_context x y /= True = distinct x ys
  | otherwise = False

--nur für Form App e1 e2 aufgerufen wegen guards
divide_context:: LExp String ->[LExp String] ->(LExp String, [LExp String],LExp String,[LExp String])
divide_context (App e1 e2) context =
  let context1 = vars_context e1 context
      context2 = vars_context e2 context
      free_context = control_context context (context1 ++ context2)
  in (e1, context1++free_context,e2, context2 ) --freie vars aus \x.s oder \!x.s die args verwerfen nicht vergessen

-- neuer context, alter context, Rückgabe context mit Vars die in beiden Fehlen 
control_context::[LExp String] -> [LExp String] ->[LExp String]
control_context [] y = [] 
control_context (x:xs) y 
  | in_context y x == False = x:control_context xs y
  | otherwise = control_context xs y

--weist e1 und e2 jeweils die variablen aus dem Kontext zu
vars_context:: LExp String -> [LExp String] ->[LExp String] 
vars_context expr [] = []
vars_context expr (x:xs) 
  | var_in_exp expr x = x:vars_context expr xs
  | otherwise = vars_context expr xs
----------------------------------------------------------------
--weakening

check_weakening:: LExp String -> [LExp String] -> Bool
check_weakening expr [] = False
check_weakening expr (x:xs) 
   |check_amount_var' expr x == 0 && is_excl x = True
   |otherwise = check_weakening expr xs

do_weakening:: LExp String -> [LExp String] -> [LExp String]
do_weakening expr (x:xs) 
   |check_amount_var' expr x == 0 && is_excl x = xs
   |otherwise = x: do_weakening expr xs
----------------------------------------------------------------
--dereliction 

check_dereliction:: LExp String -> [LExp String] -> Bool
check_dereliction expr [] = False
check_dereliction expr (x:xs) 
   |check_amount_var' expr x == 1 && is_excl x && in_expr expr x = True
   |otherwise = check_dereliction expr xs

in_expr:: LExp String -> LExp String -> Bool -- Wenn Dereliction bei t = !x angewendet terminiert nicht!
in_expr (App e1 e2) x = in_expr e1 x && in_expr e2 x
in_expr (Excl(Var var)) x
  | (Excl(Var var)) == x = False
  | otherwise = True
in_expr (Var var) x = True
in_expr (Lambda v e) x = in_expr e x
in_expr (Excl_Lambda v e) x = in_expr e x
in_expr (Excl(e)) x = in_expr e x
in_expr (Quantum(q)) x = True

dereliction:: [LExp String] -> [LExp String]
dereliction [] = [] 
dereliction (x:xs) 
  | check_vars x /= True  =(unlinear x):xs
  | otherwise = x: dereliction xs

get_dereliction_var :: LExp String -> [LExp String] -> LExp String 
get_dereliction_var expr (x:xs) 
   | check_amount_var' expr x == 1 && is_excl x = x
   | otherwise = get_dereliction_var expr xs
----------------------------------------------------------------
--contraction 

get_contraction_var :: LExp String -> [LExp String] -> LExp String  --check_contraction schon ob excl, hier nicht mehr nötig
get_contraction_var expr (x:xs) 
   | check_amount_var' expr x > 1 = x
   | otherwise = get_contraction_var expr xs

check_contraction :: LExp String -> [LExp String] -> Bool 
check_contraction expr [] = False
check_contraction expr (x:xs) 
   | check_amount_var' expr x > 1 && is_excl x = True
   |otherwise = check_contraction expr xs

contraction:: LExp String -> [LExp String] -> LExp String-> [String]->(LExp String, [LExp String],[String])
contraction expr context (Excl(Var v)) vars = contraction' expr context v vars 

--führt Umbennenung aus, analog zu rename in LExp ohne Maybe
contraction':: LExp String -> [LExp String] -> String -> [String]->(LExp String, [LExp String],[String])
contraction' (Var var) context v (f:vars) 
  | v == var = ((Var f), [(Excl(Var f))] ++ context, vars)
  | otherwise = ((Var var),context , (f:vars))

contraction' (Quantum(q)) context v2 vars = ((Quantum q),context,vars)
contraction' (Lambda v1 e) context v2 vars = 
  let(e',context',vars') = contraction' e context v2 vars in (Lambda v1 e',context',vars')

contraction' (Excl_Lambda v1 e) context v2 vars = 
  let(e',context',vars') = contraction' e context v2 vars in (Excl_Lambda v1 e',context',vars')

contraction' (Excl(e)) context v vars = 
  let(e',context',vars') = contraction' e context v vars in (Excl(e'),context',vars')

contraction' (App e1 e2) context v vars = 
  let(e1',context',vars') = contraction' e1 context v vars
     (e2',context'',vars'') = contraction' e2 context' v vars'
  in (App e1' e2', context'',vars'')

----------------------------------------------------------------
--Hilfsfunktionen für Context Operationen
take_nonlinear :: [LExp String] -> [LExp String]
take_nonlinear [] = []
take_nonlinear (x:xs)
  | check_vars x == False = take_nonlinear xs
  | otherwise =  x:take_nonlinear xs

--ob Context nichtlinear
allnonlinear:: [LExp String] -> Bool
allnonlinear [] = True
allnonlinear (x:xs) 
  | is_excl x = allnonlinear xs
  |otherwise = False

put_context :: [LExp String] -> LExp String -> [LExp String] 
put_context context (Var v) =  [(Var v)] ++ context
put_context context (Lambda v e) = [(Var v)] ++ context
put_context context (Excl_Lambda v e) =   [(Excl(Var v))] ++ context      --alle Variablen mit rename, ! nicht nötig?

in_context ::[LExp String] -> LExp String -> Bool
in_context [] v = False
in_context (x:xs) v
  | x == v = True
  | otherwise = in_context xs v

drop_context ::[LExp String] -> LExp String -> [LExp String]
drop_context [] v = []
drop_context (x:xs) v
  | x == v = xs
  | otherwise = x: drop_context xs v

var_in_exp:: LExp String -> LExp String -> Bool
var_in_exp expr (Excl(Var var)) = var_in_exp' expr (Var var)
var_in_exp expr (Var var) = var_in_exp' expr (Var var)

--schauen ob Variable in expr vorkommt
var_in_exp':: LExp String -> LExp String ->Bool
var_in_exp' (Var v) var  
  | (Var v) == var = True
  |otherwise = False

var_in_exp' (Lambda v e) var = var_in_exp e var
var_in_exp' (Excl_Lambda v e) var = var_in_exp e var
var_in_exp' (Excl(e)) var = var_in_exp e var
var_in_exp' (Quantum(q)) var = False
var_in_exp' (App e1 e2) var = var_in_exp e1 var || var_in_exp e2 var

----------------------------------------------------------------
--Hilfsfunktionen für Values/expr
unlinear:: LExp String -> LExp String --dereliction
unlinear (Excl(Var var)) = (Var var)

check_vars:: LExp String -> Bool
check_vars (Var var) = True
check_vars _ = False

is_excl:: LExp String -> Bool
is_excl (Excl(e)) = True
is_excl expr = False

app_form :: LExp String -> Bool
app_form (App e1 e2) = True
app_form expr = False

return_no_excl:: LExp String -> LExp String
return_no_excl (Excl(e)) = e

--wie oft var(aus context) in expr vorkommt
check_amount_var' :: LExp String -> LExp String -> Int
check_amount_var' expr (Var var) = check_excl expr var
check_amount_var' expr (Excl(Var var)) = check_excl expr var

check_excl ::LExp String -> String -> Int --Contraction -> mind 2 mal var in expr mit excl vars
check_excl expr v = check_excl' expr v counter 
  where counter = 0

check_excl':: LExp String -> String -> Int -> Int
check_excl' (Var var) v' counter
   | var == v' = counter +1
   | otherwise = counter
check_excl' (Quantum(q)) v' counter = counter 
check_excl' (Lambda v e) v' counter = check_excl' e v' counter
check_excl' (Excl_Lambda v e) v' counter = check_excl' e v' counter
check_excl' (Excl(e)) v' counter = check_excl' e v' counter
check_excl' (App e1 e2) v' counter = check_excl' e1 v' counter + check_excl' e2 v' counter