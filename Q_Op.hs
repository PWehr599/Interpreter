module Q_Op where

import Data.Monoid as Monoid
import Data.Complex
import QIO.Qdata
import QIO.QioClass
import QIO.Qio
import QIO.QIORandom
import QIO.QArith as QQA
import QIO.QioSyn as QS

--Datentyp für Funktionen, um Sequenzen aus Funktionen zu erstellen 
--data U = UReturn --leere Funktion am Ende der Sequenz
-- | Rot Qbit Rotation U
-- | Swap Qbit Qbit U
-- | Cond Qbit (Bool -> U) U
-- | Ulet Bool (Qbit -> U) U
-- mkQ: False=0, True=1

--type Rotation = ((Bool,Bool) -> CC)  2*2 komplexe matrix
--Aufbau Matrix:
--(FF TF)
--(FT TT)

unitaryN :: (Qbit -> U) -> [Qbit] -> U
unitaryN _ [] = mempty
unitaryN uf (q:qs) = uf q <> unitaryN uf qs

makeOneQubit :: Bool -> QIO Qbit
makeOneQubit val = do
    q <- mkQbit val
    return q

--Liste N Qubits erstellen
mkQbits :: Int -> Bool -> QIO [Qbit]
mkQbits n b = mkQbits' n b []
    where
        mkQbits' 0 _ qs = return qs
        mkQbits' n b qs = do
            q <- mkQbit b
            mkQbits' (n-1) b (qs ++ [q])

-- hinten Qubit in Liste einfügen  
mkQbit_add:: Bool -> [Qbit] -> QIO [Qbit]
mkQbit_add b qL  = do
    q <- mkQbit b
    return (qL ++ [q])
        
applyOneHadamard :: Qbit -> QIO () --uhad rein
applyOneHadamard q1 =  applyU(uhad q1)

apply_All_Hadamard:: [Qbit] -> QIO ([Qbit]) 
apply_All_Hadamard qList = do
    applyU((unitaryN uhad qList))
    return (qList)

--Einfache Gatter
--Pauli Gates: X, Y, Z, S, (Rx, Ry, Rz) -> R3 wichtig
-- Ri Gatter: (Betragsquadrat komplex)
-- X Gatter = Rx mit Wert pi für 0.(-i Unterschied, globale Phase), pi rotation um X Achse 
applyOneX :: Qbit -> QIO () --unot: not rot
applyOneX q1 = applyU(unot q1)

rY :: Rotation
rY (True, False) = 0 :+ (-1)
rY (False, True) = 0 :+ 1
rY (_, _) = 0

uY :: Qbit -> U
uY q = rot q Q_Op.rY

applyOneY :: Qbit -> QIO () --uY
applyOneY q1 = applyU(uY q1)

rZ :: Rotation 
rZ (False, False) = 1
rZ (True, True) = -1
rZ (_, _) = 0

uZ :: Qbit -> U
uZ q = rot q rZ

applyOneZ :: Qbit -> QIO () --uZ
applyOneZ q1 = applyU(uZ q1)

--S Gate 
rS :: Rotation
rS (False,False) = 1
rS (True,False) = 0
rS (False,True) = 0
rS (True,True) = 0 :+ 1

uS :: Qbit -> U
uS q = rot q rS

applyOneS :: Qbit -> QIO ()
applyOneS q1 = applyU(uS q1) 

--S Transposed
rSt :: Rotation
rSt (False,False) = 1
rSt (True,False) = 0
rSt (False,True) = 0
rSt (True,True) = 0 :+(- 1)

uSt :: Qbit -> U
uSt q = rot q rS

applyOneSt :: Qbit -> QIO ()
applyOneSt q1 = applyU(uSt q1) 

--R3 Gate (e^pi*i/4) in TT(oder a2b2 in Matrix)
r3 :: Rotation
r3 (False,False) = 1
r3 (True,False) = 0
r3 (False,True) = 0
r3 (True,True) = 0 :+ exp(pi/4)

u3 :: Qbit -> U
u3 q = rot q r3

applyOneR3 :: Qbit -> QIO ()
applyOneR3 q = applyU(u3 q)


--Gates mit Kontrolle
applyCNOT:: Qbit -> Qbit -> QIO () 
applyCNOT q1 q2 = applyU(cnot q1 q2) -- q1 Kontrolle, q2 Target 

toffoli :: Qbit -> Qbit -> Qbit -> U -- Toffoli OP
toffoli q1 q2 qo = cond q1 (\x -> if x then (cnot q2 qo)
    else mempty)

applyToffoli:: Qbit -> Qbit -> Qbit ->QIO () --Toffoli, q1, q2 Kontrolle, q3 target 
applyToffoli q1 q2 q3 = applyU(toffoli q1 q2 q3)

measQbits :: [Qbit] -> QIO [Bool]
measQbits qs = measQbits' qs []
    where
        measQbits' [] bs = return bs
        measQbits' (q:qs) bs = do
            b <- measQbit q
            measQbits' qs (bs ++ [b])

entangle :: QIO [Bool] 
entangle = do
    qa <- mkQbit False
    qb <- mkQbit False
    applyU (uhad qa <> QQA.cnot qa qb)
    ba <- measQbit qa
    bb <- measQbit qb
    return [ba, bb]
 
cccNot :: Qbit -> Qbit -> Qbit -> Qbit -> Qbit -> U -- Dreier-control mit toffoli, nötig?
cccNot q1 q2 q3 q4 qa =
    toffoli q1 q2 qa <> toffoli q3 qa q4 <> toffoli q1 q2 qa   

doCccNOT :: QIO Bool -- 4er Toffoli  q4 apply
doCccNOT = do
    q1 <- mkQbit True
    q2 <- mkQbit True
    q3 <- mkQbit True
    q4 <- mkQbit False
    applyU (ulet False (cccNot q1 q2 q3 q4))
    applyOneS(q1)
    measQbit q4

q0 :: QIO Qbit
q0 = mkQ True
--Anwenden Hadamard auf Qubit
qPlus :: QIO Bool
qPlus  =  do  qa <- q0
              applyOneY (qa)
              measQbit qa