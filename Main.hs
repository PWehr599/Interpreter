import Data.Monoid as Monoid
import QIO.QioSyn as QS
import QIO.Qdata
import QIO.QioClass
import QIO.Qio
import QIO.QArith as QQA
import Data.Angle as Angle

import LExp 
import Wellformed 
import Data
import Q_Op

--Ab hier Testfälle:
-- infix Expr :@ Exp statt leer (Var "x") :@ (Var "x") entspricht xx
-- (Var "x") `App` (Var "x")
exVar = Var "x"
exExclLam = App(Lambda "x" (App(App(Var "y") (Var "y"))(Var "x"))) (Var "z")
--exExclLam1 = App((Lambda "x" (App(App(Var "y") (Var "y"))(Var "x"))) (Var "z"))

lam = Excl_Lambda "x" (App(Var "x")(Var "x"))
appX = App(Var "x")(Var "x")
lam3red = App(App(Lambda "x"(Var "x"))(Lambda "y" (Var "y")))(App(Lambda "x"(App(Quantum(Operation(H)))(Var "x")))((Quantum(QbValue False))))
exExclLam' = Excl_Lambda "x" (App(App(Var "x") (Quantum (QbValue False)))(Var "x"))

exLam = App (Lambda "x" (Var "x")) (Excl_Lambda "y" (App(Var "y")(Var "y")))
exprLam =  App (App (Lambda "x" (Var "x"))((Lambda "v" (Var "v")))) (Var "x")
exprLam2 = App (Lambda "w" (Var "w"))(Lambda "z"(App (Var "z")(Var "z")))
exprLam3 = App (Lambda "f" (App (Var "f") (Var "f"))) (Var "e")

expr1 = App (Lambda "x" (Lambda"x" (App (Var "x") (Var "x")))) (Var "y")

--(\x.xx)(((\y.y)(\y.y))(\y.y)) (\y.y)
expr2 = App (Lambda "x" (App (Var "x") (Var "x"))) (App (App (App (Lambda "y1" (Var "y1"))(Lambda "y2"(Var "y2")))(Lambda "y3" (Var "y3"))) (Lambda "y4" (Var "y4")) )
expr3 = App (Lambda "x" (App (Var "x") (Var "x"))) (Lambda "z" (App(Var "z")(Var "z"))) --kein fehler unendlich Auswertung Omega
expr5 = App (App (Lambda "w" (Var "w"))(Lambda "z" (App(Var "z")(Var "z")))) (App (Lambda "w" ( Var"w"))(Lambda "z" (App (Var "z")(Var "z"))))
expr6 = App(App (Lambda "x" (Lambda"y" (App (Var "x") (Var "x")))) (Var "y"))(Var "s")
expr6E = App(App (Excl_Lambda "x" (Excl_Lambda "y" (App (Var "x") (Var "x")))) (Excl(Var "y")))(Excl(Var "s"))

expr6ELam = App(Excl_Lambda "x" (Excl_Lambda "y" (App (Var "x") (Var "x"))))(Excl(Var"z"))
expr6ELam' = Excl_Lambda "x" (Lambda "y" (App (Var "x") (Var "x")))

 ---------------------------------------------------------------------------------

excllam = Excl_Lambda "d"(App(Excl_Lambda "d"(Var "d"))(Excl(Excl_Lambda "s"(Excl(App(Var"s")(Var"s"))))))
expr6EE = App(Excl_Lambda "y" (App (Var "x") (Var "x"))) (Excl(Var "y"))

ee = App (Lambda "x" (App (Var "x") (Var "x"))) (App (Var "x") (Var "x")) 

ee2 =Lambda "w" (Var "y")

ee3 = Excl_Lambda "y" (Excl(App (Var "y") (Var "y")))

exprE = App (Lambda "f" (App (Var "f") (Var "f"))) (App (Lambda "w" (Var "w")) (Lambda "z" (App (Var "z") (Var "z"))))
exprE1 = App (Lambda "f" (App (Var "f") (Var "f"))) (Lambda "x_1" (App (Var "x_1") (Var "x_1"))) --(Var "w") --(Lambda "w" (Var "w")) --(Lambda "x_1" (App (Var "x_1") (Var "x_1")))
exprE2 = App (Lambda "w" (Var "w")) (Lambda "z" (App (Var "z") (Var "z")))

testRename = App(Excl_Lambda "u"(Excl_Lambda "f" (App(Var "f")(Excl(App(Var "u")(Excl(Lambda"u"(Var"u"))))))))(Lambda "u" (Var "u"))
 ---------------------------------------------------------------------------------
 
exprExcl2 = App( Excl_Lambda "f" (App (Var "f") (Var "f")))((Quantum ((QbValue False))))
exprExcl3 = App( Excl_Lambda "f" (App (Var "f")  (Var "f")))(Excl(App (Lambda "x" (App (Var "x") (Var "x"))) (App (App (App (Lambda "y" (Var "y"))(Lambda "y"(Var "y")))(Lambda "y" (Var "y"))) (Lambda "y" (Var "y")) )))
exprExcl4 = App( Excl_Lambda "f" (Excl(App (Var "f")(Var "f"))))(Excl(Var"s"))--geht
exprExcl5 = App(Excl_Lambda "f" (App (Var "f")(Var "f")))(Excl(Var"s")) --geht
exprExcl6 = App (Excl_Lambda "x" (Var "x")) (Excl(Excl_Lambda "f" (Var "f"))) --geht
exprExcl7 = App (Excl_Lambda "x" (Var "x")) (Excl_Lambda "f" (Var "f")) 
expr3' = App( Lambda "f" (App (Var "f")  (Var "f")))(App (Lambda "x" (App (Var "x") (Var "x"))) (App (App (App (Lambda "y" (Var "y"))(Lambda "y"(Var "y")))(Lambda "y" (Var "y"))) (Lambda "y" (Var "y")) ))

--te = App (Var "f") (Quantum ((QbValue False)))

 ---------------------------------------------------------------------------------
tt = App (Var "t") (Var "t")
ren =App (Lambda "x" (App (Var "x") (Var "x"))) (App (App (App (Lambda "y" (Var "y"))(Lambda "y"(Var "y")))(Lambda "y" (Var "y"))) (Lambda "y" (Var "y")) )

exprQEX = App(Excl_Lambda "s" (App(Quantum(Operation S))(App(Quantum(Operation X))(Var "s")))) (Excl(App (Quantum (Operation H))(Quantum(QbValue False))))--geht

exprQEX' = App(Lambda "s" (App(Quantum(Operation X))(Var "s")))((Quantum ((QbValue False)))) --geht

test  = App(App(Var "x") (Lambda "y" (Var "y")))(App(Lambda "z" (Var "z"))(Lambda "y" (Var "y")))
 ---------------------------------------------------------------------------------


exprQ = App(App(Quantum(Operation(H)))(Quantum(QbValue False)))(App(Quantum(Operation(Z)))(Quantum(QbValue True)))
exprQ2 = App(App(App( Quantum(Operation H)) (App((Quantum(Operation Z))) (App(Quantum (Operation Y)) (Quantum(QbValue False)))))(Quantum((QbValue False))))(Quantum(QbValue False)) --geht

exprQ3 = App (Excl_Lambda "f" (Quantum(QbValue True))) (Excl(App(Quantum(Operation H ))(Quantum(QbValue False)) )) --geht

exprCNOT = App (App(Quantum(Operation CNOT))(App(Quantum(Operation H))(Quantum(QbValue True )))) (Quantum(QbValue True))
exprTof = App (App (App(Quantum(Operation Toffoli))(Quantum(QbValue True ))) (Quantum(QbValue True))) (Quantum(QbValue False))
exprX = App ( Quantum (Operation X)) (Quantum(QbValue False))
exprY = App(Quantum(Operation Y ))(Quantum(QbValue False)) 
exprH = App(Quantum(Operation H ))(Quantum(QbValue False))
exprR3 = App(Quantum(Operation R3 ))(Quantum(QbValue False))

exprLQ = App (Lambda "s" (App(Quantum(Operation H))(App(Var "s")(Var"s"))))(Quantum(QbValue False))-- (App(Quantum(Operation X ))(Quantum(QbValue False)) )
--exprH2 = App(Quantum (Operation "H" (Operation "H" (QbValue True)))) --1

 ---------------------------------------------------------------------------------

test222 = App(App(App(Var "x") (Lambda "y" (Var "y")))(Var"x"))(App(Lambda "z" (Var "z"))(Lambda "y" (Var "y"))) --fehler newReduction geht zu früh raus
test222' = App(App(Var "x") (Var "x"))(App(Lambda "z" (Var "z"))(Lambda "y" (Var "y"))) --fehler newReduction geht zu früh raus,wenn App mit 2 unreduzierbaren Werten 
excl_var = Excl(Var "x")
only_var = Var "x"
qbit = App(Quantum(QbValue True))(Quantum(QbValue False))

--fehler weg
testQ = App(App(App(Quantum(QbValue False))(Quantum(QbValue False)))(Quantum(QbValue False))) (App(Quantum(Operation H)) (Quantum(QbValue False))) --gleicher Fehler mit Quantum
testQ' = App(App(App(Quantum(QbValue False))(Quantum(QbValue False)))(Quantum(QbValue False))) (App(Lambda "w" (Var("w"))) (Quantum(QbValue False))) --gleicher Fehler mit Quantum
testQ'' = App(App(App(Quantum(QbValue False))(Quantum(QbValue False)))(Quantum(QbValue False))) (App(Quantum(QbValue True)) (Quantum(QbValue False))) --gleicher Fehler mit Quantum
testQ''' = App(App(Quantum(QbValue True))(Quantum(QbValue True)))(App(Quantum(QbValue False))(Quantum(QbValue False)))
testQ'''' = App(App(Quantum(QbValue True))(Quantum(QbValue True)))(Quantum(QbValue False))

exprExcl = App( Excl_Lambda "f" (App (Var "f")  (Var "f"))) (Excl(App ((Lambda "f") (Var "f"))(App(Var "f")(Quantum ((QbValue False))))))  --fehler
exprExcl' = App( Excl_Lambda "f" (App (Quantum ((QbValue False)))  (Var "f"))) (Excl(App ((Lambda "f") (Var "f"))(App(Lambda "y" (Quantum(QbValue True)))((Var "f")))))  --geht aber illegal
exprExcl'' = App( Excl_Lambda "f" (App (Excl(App(Var "f")(Excl(Var "h"))))  (Var "f"))) (Excl(App ((Lambda "f") (Var "f"))(App(Var "f")(Quantum ((QbValue False)))))) 
testQuantum = App(Quantum(QbValue False))(App(Quantum(Operation H))(Quantum(QbValue False))) --geht

freshTest = ["x_" ++ show i | i <- [1..20]]
varList = [(Var "x"),(Var "x"), (Excl(Var "x")),(Var "a"),(Excl(Var "x_1")),(Var "c"),(Excl(Var "x_2"))]
varListExcl = [ (Excl(Var "x")),(Excl(Var "x_1")),(Excl(Var "x_2"))]
testList = []

lll = App(Excl_Lambda "y" (Lambda "x"(App(Var "x")(Var "x"))))(Quantum(QbValue False))

dere = Excl_Lambda "x"(Excl_Lambda "y"(App (Var "y") (Var "y")))
ttt= Excl_Lambda "x"(Excl_Lambda "y"(Var "y"))
noRed = App(Excl_Lambda "f"(App(Var "f")(Excl(Excl_Lambda "f"(Quantum(QbValue True))))))(Excl((Quantum(QbValue False))))
fix  = App(Excl_Lambda "f"(App(Var "f")(Excl(App(Excl(Var "f"))(Var "f")))))(Excl((Excl(Excl_Lambda "f"(App(Var"f")(Lambda "y" (Var "y")))))))
dereTest = Excl_Lambda "x"(App (Lambda "y"(Var "y"))(Var "x"))
ex = App(Excl_Lambda "x"(Excl((Var"x"))))(Excl((Var "c")))

lamlam = App(Lambda "y"(Lambda "x"(App (Var "x") (Var "y"))))(Lambda "y"(Var "y"))
--in Arbeit
ex2 = Excl_Lambda "x"(Excl(Var "x"))
verschraenkt = App(App(Lambda "x" (Lambda "y" (App (App(Quantum(Operation CNOT))(App(Quantum(Operation H))(Var "x"))) (Var "y")))) (Quantum(QbValue False)))(Quantum(QbValue False))
klassisch = App ((Lambda "y" (App(Lambda "x"(Var "x"))(Var "y"))))(Var "z")
doppelh = App (Quantum(Operation H))(App(Quantum(Operation H))(Quantum(QbValue False))) --h00
h = App (App(Quantum(Operation CNOT))(Quantum(QbValue True ))) (Quantum(QbValue True))
lastte = App(Excl_Lambda "x"(Quantum(QbValue False)))(Excl(App(Quantum(Operation(H)))(Quantum(QbValue False))))
---------------------------------------------------------------------------------

main :: IO()
main = do     
    let result = q_lambda_reductionsim verschraenkt
    print result
    --print $ sim doCNOT
    {--
    print fix
    (res, his) <- q_lambda_reductionrun fix 
    if null his then 
        (print ("Not Wellformed"))
    else (print (res,his))
 --}
    --print $ show r3 --Matrix 