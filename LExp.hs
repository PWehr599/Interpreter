module LExp where

import Data.Monoid as Monoid
import QIO.QioSyn as QS
import QIO.Qdata
import QIO.QioClass
import QIO.Qio
import QIO.QArith as QQA
import Data.Angle as Angle --Rx, Ry, Rz (für später, wenn noch Zeit)

import Data
import Q_Op
import Wellformed

--jetzt mit Quantum + Excl
-- Hilfsfunktion zur alpha-Umbenennung von Ausdrücken:
rename :: (Eq b) => LExp b -> [b] -> (LExp b, [b])
rename expr freshvars = rename_it expr [] freshvars
 where 
  rename_it (Var v) renamings freshvars = 
   case lookup v renamings of 
     Nothing -> (Var v,freshvars)
     Just v'  -> (Var v',freshvars)

  rename_it (App e1 e2) renamings freshvars =            
   let (e1',vars') = rename_it e1 renamings freshvars
       (e2',vars'') = rename_it e2 renamings vars'
   in (App e1' e2', vars'')

  rename_it (Excl(App e1 e2)) renamings freshvars =  
    let (e1',vars') = rename_it e1 renamings freshvars
        (e2',vars'') = rename_it e2 renamings vars'
    in (Excl(App e1' e2'), vars'')

  rename_it (Lambda v e) renamings (f:freshvars) =  
   let (e',vars') = rename_it e ((v,f):renamings) freshvars
   in (Lambda f e',vars')

  rename_it (Excl_Lambda v e) renamings (f:freshvars) =  
   let (e',vars') = rename_it e ((v,f):renamings) freshvars
   in (Excl_Lambda f e',vars')

  rename_it (Excl(e)) renamings (freshvars) = 
   let (e',vars') = rename_it e renamings freshvars
   in (Excl(e'),vars')

  --nichts bei Quantum
  rename_it (Quantum(q)) renamings freshvars = (Quantum(q), freshvars)

-- Hilfsfunktion zur Substitution
-- substitute freshvars expr1 expr2 var 
-- f"uhrt die Ersetzung expr1[expr2/var] durch

substitute  :: (Eq b) => [b] -> LExp b -> LExp b -> b -> (LExp b, [b])

substitute freshvars (Quantum q1) (Var v) var = 
  ((Quantum q1), freshvars)

substitute freshvars (Quantum q1) (Excl(e)) var = 
  ((Quantum q1), freshvars)

substitute freshvars (Quantum q1) (Lambda v e) var = -- wenn lambda discarded
  ((Quantum q1), freshvars)

substitute freshvars (Quantum q1) (Quantum q2) var =  --well formed für verhindern Discard Qbits
  ((Quantum q1), freshvars)

substitute freshvars (Var v) (Quantum q) var
  | v == var = ((Quantum q),freshvars)
  | otherwise = (Var v,freshvars)

substitute freshvars (Var v) expr2 var --redundant warning
 | v == var =  rename (expr2) freshvars
 | otherwise = (Var v,freshvars)

substitute freshvars (Excl(Var v)) expr2 var --redundant warning
 | v == var =  rename (Excl(expr2)) freshvars
 | otherwise = ((Excl(Var v)),freshvars)
 
--substitute freshvars (Excl_Lambda v1 (Excl(e1))) (Var v) var = 
--  ((Excl_Lambda v1 (Excl(e1)), freshvars))

substitute freshvars (Lambda v e1) (Excl(e)) var = 
  let(e',vars') = substitute freshvars e1 (Excl(e)) var
  in (Lambda v e',vars')

substitute freshvars (App e1 e2) expr2 var =
 let (e1',vars')  = substitute freshvars e1 expr2 var
     (e2',vars'') = substitute vars' e2 expr2 var
 in (App e1' e2', vars'')

substitute freshvars (Excl(App e1 e2)) expr2 var =   --Syntax !!!!
 let (e1',vars')  = substitute freshvars e1 expr2 var
     (e2',vars'') = substitute vars' e2 expr2 var
 in (Excl(App e1' e2'), vars'')

substitute freshvars (Excl(e)) expr var =  --fixIt auf S.27 ?
   let(e',vars') = substitute freshvars e expr var 
   in(Excl(e'), vars')

substitute freshvars (Lambda v e) expr2 var =
 let (e',vars')   = substitute freshvars e expr2 var
 in (Lambda v e',vars')

substitute freshvars (Excl_Lambda v e) expr2 var =
 let (e',vars')   = substitute freshvars e expr2 var
 in (Excl_Lambda v e',vars')

substitute freshvars (Quantum q1) expr var =  --für Excl-substitute
  ((Quantum q1), freshvars)


new_History:: LExp String -> LExp String

--values -> nix passiert ID 
new_History (Var var) = (P_h)
new_History (Excl(e)) = (P_h) --passiert doch rename 
new_History (Lambda v e) = (P_h)
new_History (Quantum(q)) = (P_h)
new_History (Excl_Lambda v e) = (P_h)

--alle Lambda Substitutionen
--checkfree unnötig bei wellformed Lambdas, aber ändert nichts 
 
new_History (App (Lambda v1 e1) (Var var)) 
  |checkfree e1 v1 = (App(Lambda v1 (lambda_History e1 v1))(P_h))
  |otherwise = (App(Lambda v1 (P_h))(Var var))

new_History (App (Lambda v1 e1) (Lambda v2 e2)) 
  |checkfree e1 v1 = (App(Lambda v1 (lambda_History e1 v1))(P_h))
  |otherwise = (App(placeholder (Lambda v1 e1))(Lambda v2 e2))

new_History (App (Lambda v1 e1) (Excl_Lambda v2 e2)) 
  |checkfree e1 v1 = (App(Lambda v1 (lambda_History e1 v1))(P_h)) 
  |otherwise = (App(placeholder (Lambda v1 e1))(Excl_Lambda v2 e2))

new_History (App(Lambda v1 e1)(Quantum(Qb q))) = (App(Lambda v1 (lambda_History e1 v1))(P_h))

new_History (App(Lambda v1 e1)(Quantum(Operation o))) = (App(Lambda v1 (lambda_History e1 v1))(P_h))

--Quanten Gates History (mit bis zu 3 Qubits), geht auch mehr wenn nötig
new_History (App(Quantum(Operation o))(Quantum(Qb q))) = (App (Quantum(Operation(o)))(P_h))
new_History (App (App(Quantum(Operation o))(Quantum(Qb q1 ))) (Quantum(Qb q2))) = (App(Quantum(Operation o))(P_h))
new_History (App (App (App(Quantum(Operation o))(Quantum(Qb q1 ))) (Quantum(Qb q2))) (Quantum(Qb q3))) = (App(Quantum(Operation o))(P_h))

new_History (App(Excl_Lambda v1 e1)(Excl(e2)))
  |checkfree e1 v1  = (App(Excl_Lambda v1 (lambda_History e1 v1))(P_h))
  |otherwise = (App (Excl_Lambda v1 (P_h))(Excl(e2)))

--Fälle für (v1 t2) -> (v1 t2'), alle Values durch 
new_History (App (Lambda v1 e1) e2) = 
  let e2' = new_History e2
  in (App (P_h) (new_History(e2)))

new_History (App (Excl_Lambda v1 e1) e2) = 
  let e2' = new_History e2
  in (App (P_h) (new_History(e2)))

new_History(App(Var var) e2) = 
  let e2' = new_History e2
  in(App(P_h) e2')

new_History(App(Quantum (Qb q)) e2) = 
  let e2' = new_History e2
  in(App(P_h) e2')

new_History(App(Quantum (Operation o)) e2) = 
  let e2' = new_History e2
  in(App(P_h) e2')

new_History(App(Excl(e)) e2) = 
  let e2' = new_History e2
  in(App(P_h) e2')
  
--(Fall (t1 t2) -> (t1' t2))
new_History (App e1 e2) = (App (new_History e1) (P_h)) --(t t), für ID in reduceQ_history selber 


lambda_History:: LExp String -> String -> LExp String
lambda_History e v 
  | checkfree e v == True = lambda_History' e v
  | otherwise = e

lambda_History':: LExp String -> String -> LExp String
lambda_History' (App e1 e2) v = 
  let(e1') = lambda_History' e1 v
     (e2') = lambda_History' e2 v
  in (App e1' e2')

lambda_History' (Lambda v1 e1 ) v = (App (P_h)(lambda_History' e1 v))
lambda_History' (Excl_Lambda v1 e1) v = (App (P_h)(lambda_History' e1 v))
lambda_History' (Quantum(Qb q)) v = (P_h)
lambda_History' (Quantum(QbValue b)) v = (P_h)
lambda_History' (Quantum(Operation o)) v = (P_h)
lambda_History' (Excl(e)) v = (Excl(lambda_History' e v)) --Excl wird dran gelassen
lambda_History' (Var var) v  
  | v == var = (Var var)
  | otherwise = (P_h)

--Term voll mit Placeholder setzten, aber unnötig bei Apps, vielleicht später benutzen
placeholder:: LExp String -> LExp String
placeholder (App e1 e2) = 
  let e1' = placeholder e1
      e2' = placeholder e2
  in (App e1' e2')

placeholder (Excl_Lambda v e) = (P_h)
placeholder (Lambda v e) = (P_h)
placeholder (Var var) = (P_h)
placeholder (Quantum(q)) = (P_h)
placeholder (Excl(e)) = (P_h)

checkfree :: LExp String -> String -> Bool --nur für Excl_Lambdas aufrufen, ob \!x.term -> ob x frei in term

checkfree (App e1 e2) v = 
  let(e1') = checkfree e1 v
     (e2') = checkfree e2 v
  in (e1' || e2')

checkfree (Var var ) v
  | v == var = True
  | otherwise = False

checkfree (Quantum(Qb q)) v = False
checkfree (Quantum(QbValue b)) v = False
checkfree (Quantum(Operation o)) v = False
checkfree (Excl(e)) v = checkfree e v
checkfree(Lambda v1 e1 ) v = checkfree e1 v
checkfree (Excl_Lambda v1 e1) v = checkfree e1 v

--vor Reduktion alle Qbits erstellen 
--komische Historien vermeiden
createQbits:: LExp String -> QIO (LExp String)
createQbits(App e1 e2) = do
  (e1') <- createQbits e1
  (e2') <- createQbits e2
  return(App e1' e2')

createQbits (Quantum(QbValue v)) = do 
  q <- mkQbit v 
  return (Quantum(Qb q))

createQbits (Excl_Lambda v e) = do 
  e' <- createQbits e
  return (Excl_Lambda v e')

createQbits (Excl(e)) = do 
  e' <- createQbits e
  return (Excl(e'))

createQbits (Lambda v e) = do 
  e' <- createQbits e
  return (Lambda v e') 

createQbits (Var var) = do
  return(Var var)

createQbits(Quantum(Operation o)) = do
  return(Quantum(Operation o))

newReduction:: LExp String -> [String] -> QIO (LExp String,[String]) -- + History: [LExp String], 
--Substitutionen klassisch alle Values aus S.21 machen
newReduction (App (Lambda v1 e1) (Lambda v2 e2)) freshvars = do
  let (e',vars) = substitute freshvars e1 (Lambda v2 e2) v1
  return (e',vars)

newReduction (App (Lambda v1 e1) (Var var)) freshvars = do
  let (e',vars) = substitute freshvars e1 (Var var) v1
  return (e',vars)

newReduction (App (Lambda v1 e1) (Excl(e))) freshvars = do
  let (e',vars) = substitute freshvars e1 (Excl(e)) v1
  return (e',vars)

newReduction (App (Lambda v1 e1) (Excl_Lambda v2 e2)) freshvars = do  
  let (e',vars) = substitute freshvars e1 (Excl_Lambda v2 e2) v1
  return (e',vars)

--Quantum Substitutionen values

newReduction (App (Lambda v1 e1) (Quantum(Qb q))) freshvars = do --nur Konstanten
  let(e',vars) = substitute freshvars e1 (Quantum(Qb q)) v1
  return (e',vars)

newReduction (App (Lambda v1 e1) (Quantum(Operation o))) freshvars = do --nur Konstanten
  let(e',vars) = substitute freshvars e1 (Quantum(Operation o)) v1
  return (e',vars)

--Substitution Excl
newReduction (App (Excl_Lambda v1 e1) (Excl(e2))) freshvars = do --pattern fehlt 
  let (e',vars) = substitute freshvars e1 e2 v1
  return (e',vars)
--Quantum Gates H, X, Y, Z, S, R3

newReduction (App (Quantum(Operation H ))(Quantum(Qb q ))) freshvars  = do 
   applyOneHadamard q 
   return(Quantum(Qb q), freshvars)

newReduction (App (Quantum(Operation X )) (Quantum(Qb q ))) freshvars = do
  applyOneX q
  return(Quantum(Qb q), freshvars)

newReduction (App(Quantum(Operation Y ))(Quantum(Qb q ))) freshvars = do
  applyOneY q
  return(Quantum(Qb q), freshvars)

newReduction (App(Quantum(Operation Z ))(Quantum(Qb q ))) freshvars = do
  applyOneZ q
  return(Quantum(Qb q), freshvars)

newReduction (App(Quantum(Operation S ))(Quantum(Qb q ))) freshvars = do
  applyOneS q
  return(Quantum(Qb q), freshvars)

newReduction (App(Quantum(Operation R3 ))(Quantum(Qb q ))) freshvars = do
  applyOneR3 q
  return(Quantum(Qb q), freshvars)

--Gates Kontrolle CNOT, Toffoli

newReduction (App (App(Quantum(Operation CNOT))(Quantum(Qb q1 ))) (Quantum(Qb q2))) freshvars = do -- q1 Kontrolle q2 target 
  applyCNOT q1 q2
  return(App (Quantum(Qb q1))((Quantum(Qb q2))), freshvars)

newReduction (App (App (App(Quantum(Operation Toffoli))(Quantum(Qb q1 ))) (Quantum(Qb q2))) (Quantum(Qb q3))) freshvars = do -- q1, q2 Kontrolle q3 target 
  applyToffoli q1 q2 q3
  return(App (App (Quantum(Qb q1))((Quantum(Qb q2))))(Quantum(Qb q3)), freshvars)
-----------------------------------------------------------------------------------------
newReduction (App (Quantum(Operation operation))(e2)) freshvars = do 
  (e2',vars) <- newReduction (e2) freshvars
  return ((App(Quantum(Operation operation)))e2', vars)

newReduction (App (Quantum(Qb q)) e2) freshvars = do --richtig?
  (e2',vars) <-  newReduction e2 freshvars
  return ((App(Quantum(Qb q)) e2'), vars)

newReduction (App e1 (Quantum(Qb q))) freshvars = do --richtig?
  (e1',vars) <-  newReduction e1 freshvars
  return ((App e1'(Quantum(Qb q))), vars)

newReduction(Quantum (Qb q)) freshvars = do 
  return (Quantum(Qb q), freshvars)

--Klassisch vorgehen ohne Quantum
newReduction (App (Lambda v1 e1) (e2)) freshvars = do --aufpassen EXCL --2
  (e2',vars) <-  newReduction e2 freshvars
  return ((App (Lambda v1 e1) e2'), vars)

newReduction (App (Var var) e2) freshvars = do
  (e2',vars) <-  newReduction e2 freshvars
  return ((App (Var var) e2'), vars)

newReduction (App(App(Var var) (Lambda v e)) e2) freshvars = do  --richtig?
  (e2',vars) <- newReduction e2 freshvars
  return((App(App(Var var) (Lambda v e)) e2'),vars)

newReduction (Lambda v e) freshvars = do 
  return((Lambda v e),freshvars)

newReduction (Excl_Lambda v e) freshvars = do 
  return((Excl_Lambda v e),freshvars)

newReduction (Var var) freshvars = do
  return((Var var), freshvars)

newReduction (App (Excl_Lambda v e) (Quantum(q))) freshvars = do --exit
  return((App (Excl_Lambda v e) (Quantum(q))), freshvars)

newReduction (Excl e) freshvars = do 
  return ((Excl e),freshvars)
  
newReduction(App (Excl_Lambda v1 e1)e2) freshvars = do
  (e2',vars) <- newReduction e2 freshvars
  return((App (Excl_Lambda v1 e1)e2'), vars)

newReduction (App e1 e2) freshvars = do  --1
  (e1',vars) <-  newReduction e1 freshvars
  return ((App e1' e2), vars)

-----------------------------------------------------------------------------------------

measureResult :: LExp String ->  QIO (LExp String)
measureResult (Quantum(Qb q)) = do 
  b <-measQbit q
  return (Quantum(Qb_M b))

measureResult (App e1 e2) = do 
  (e1') <- measureResult e1
  (e2') <- measureResult e2
  return(App e1' e2')

measureResult (Lambda v e ) = do 
  return (Lambda v e)

measureResult (Excl_Lambda v e ) = do 
  return (Excl_Lambda v e)

measureResult (Var var ) = do 
  return (Var var)

measureResult(Excl(e)) = do 
  return (Excl e)

measureResult(Quantum(QbValue b)) = do --sollte nicht passieren, für fehler
  return (Quantum (QbValue b))

measureResult(Quantum(Operation o)) = do --sollte nicht passieren, aber bei Berechnungen ohne Qubit möglich
  return (Quantum (Operation o))

measureResult (Quantum(Qb_M b)) = do 
  return (Quantum(Qb_M b))
-----------------------------------------------------------------------------------------
measureAll:: LExp String -> QIO (LExp String)
measureAll e = do 
  (e') <- measureResult e 
  if e' == e then return e else measureAll e'

make_history:: LExp String -> QIO (LExp String)
make_history e = do
  let e' = new_History(e)
  return e'

reduceQ_history :: LExp String -> [String] -> [LExp String] -> QIO(LExp String,[String],[LExp String])
reduceQ_history e freshvars history = do 
  newhistory <- make_history e
  let history' = history ++ [newhistory]
  (e',vars) <- newReduction e freshvars
  if e == e' then return (e,vars,(history ++ [(P_h)])) else reduceQ_history e' vars history' --ID in return: (P_h), immer (P_h) als letzter Historien Wert, klassisch wär so lange Placeholder bis abgebrochen
                                                                                             -- hier nach ersten (P_h) Abbruch 
--Hauptfunktion für Reduktion
reduce:: LExp String -> [String]-> QIO(LExp String,[LExp String])
reduce e fresh = do 
  e' <- createQbits e
  (e'',vars',history) <- reduceQ_history e' fresh empty_history
  e''' <- measureAll e''
  return (e''', history)

  where  empty_history = []

--ausführen mit QIO sim für Wahrscheinlichkeiten (wie Modell)
q_lambda_reductionsim:: LExp String -> Prob(LExp String,[LExp String])
q_lambda_reductionsim expr = do 
  let (expr',vars) = rename expr fresh
  case wellformed expr' vars of 
    True -> do
      a <- sim $ reduce expr' vars
      return a
    False -> return(expr,[])

  where  fresh = ["x_" ++ show i | i <- [1..]]

--ausführen mit QIO run für Messung
q_lambda_reductionrun:: LExp String -> IO(LExp String,[LExp String]) --schwierig mit geschachtelter Maybe Monade
q_lambda_reductionrun expr = do 
  let (expr',vars) = rename expr fresh
  case wellformed expr' vars of
    True -> do
      (res,his) <- run $ do
        (a,b)<-reduce expr' vars
        return(a,b)
      return (res,his) 
    False -> return (expr,[]) 

  where  fresh = ["x_" ++ show i | i <- [1..]]



