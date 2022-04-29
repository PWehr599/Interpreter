module Data where

import Data.Monoid as Monoid
import QIO.QioSyn as QS
import QIO.Qdata
import QIO.QioClass
import QIO.Qio
import QIO.QArith as QQA

import Q_Op

data LExp v =  
   Var v                  -- x
 | Lambda v (LExp v)      -- \x.s
 | Excl_Lambda v (LExp v) -- \!x.s
 | App (LExp v) (LExp v) -- (s t)
 | Excl (LExp v) -- !t 
 | P_h    --  _ Placeholder
 | Quantum QuantumOp  --  Qubits, Quantum Operationen(Gates, Messung)
 deriving(Eq,Show)

data QuantumOp = 
  QbValue Bool   
  | Qb Qbit 
  | Qb_M Bool --für nach Messung
  | Operation Q_OpName  --Gates : X, Y, Z, H, S, R3(Rx), Toffoli, CNOT
  deriving(Eq,Show)

data Q_OpName  = 
    H
  | X
  | Y
  | Z
  | S
  | St
  | R3  -- pi/8 drehung in TT
  | CNOT
  | Toffoli
 deriving(Eq,Show)