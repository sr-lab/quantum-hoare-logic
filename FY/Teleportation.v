From Coq Require Import Strings.String.
From Coq Require Import Lists.List.
Import ListNotations.
From FY Require Export Utils.
From FY Require Export Syntax.
From FY Require Export Semantics.
From FY Require Export Assertion.
From FY Require Export Logic.

Definition X0 : string := "X0".
Definition X1 : string := "X1".

Definition TELEPORT : com :=
  <{ 
     q 0 := 0;
     q 1 := 0;
     q 2 := 0;
     q 1 *=1 GH;
     q 1 2 *=2 GCNOT;
     q 0 1 *=2 GCNOT;
     q 0 *=1 GH;
     X0 :=measQ 0;
     X1 :=measQ 1;
     if X0 == (0 % nat)
     then 
       if X1 == (1 % nat) then q 2 *=1 GX else skip end 
     else
       if X1 == (1 % nat) then q 2 *=1 GX; q 2 *=1 GZ else q 2 *=1 GZ end 
     end
  }>.

Print TELEPORT.

Theorem final_state: ceval TELEPORT 
[(( _ !-> 0%nat), I 1)] [(( _ !-> 0%nat), I 1)] .
Proof.
    eapply E_Seq.
    apply E_Init.
    simpl.
    eapply E_Seq.
    apply E_Init.
    simpl.
    eapply E_Seq.
    apply E_Init.
    simpl.
    eapply E_Seq.
    apply E_AppOne.
    simpl.
    eapply E_Seq.
    apply E_AppTwo.
    simpl.
    eapply E_Seq.
    apply E_AppTwo.
    simpl.
    eapply E_Seq.
    apply E_AppOne.
    simpl.
    eapply E_Seq.
    apply E_Meas.
    simpl.
    eapply E_Seq.
    apply E_Meas.
    simpl.
    eapply E_IfTrue.
    simpl.
    eapply E_IfTrue.
    simpl.
    (* there is a problem *)
Admitted.


(*
import numpy as np
H = 1/np.sqrt(2)*np.array([[1, 1],
                           [1,-1]])
CNOT = np.array([[1,0,0,0],
                 [0,1,0,0],
                 [0,0,0,1],
                 [0,0,1,0]])

I = np.eye(2)

ket0 = np.array([1,0])
ket1 = np.array([0,1])

init = np.kron(ket0, np.kron(ket0, ket0)).reshape(-1,1)

fst = init.dot(init.T)
#print(fst)

u1 = np.kron(H, np.kron(I, I))
snd = u1.dot(fst).dot(u1.T)
#print(snd)

u2 = np.kron(CNOT , I)
thrd = u2.dot(snd).dot(u2.T)
#print(thrd)

u3 = np.kron(I , CNOT)
frth = u3.dot(thrd).dot(u3.T)
print(frth)

m0 = np.kron(ket0, np.kron(I, I))
fth0 = m0.dot(frth).dot(m0.T) / np.trace(m0.dot(frth).dot(m0.T))
print(fth0)

m1 = np.kron(ket1, np.kron(I, I))
fth1 = m1.dot(frth).dot(m1.T) / np.trace(m1.dot(frth).dot(m1.T))
print(fth1)

m0 = np.kron(ket0, I)
sxth00 = m0.dot(fth0).dot(m0.T) / np.trace(m0.dot(fth0).dot(m0.T))
print(sxth00)
sxth01 = m0.dot(fth1).dot(m0.T) / np.trace(m0.dot(fth1).dot(m0.T))
print(sxth01)

m1 = np.kron(ket1, I)
sxth10 = m1.dot(fth0).dot(m1.T) / np.trace(m1.dot(fth0).dot(m1.T))
print(sxth10)
m1 = np.kron(ket1, I)
sxth11 = m1.dot(fth1).dot(m1.T) / np.trace(m1.dot(fth1).dot(m1.T))
print(sxth11)


prop000 = np.kron(ket0, np.kron(ket0, ket0)).T.dot(frth).dot(np.kron(ket0, np.kron(ket0, ket0)))
print(prop000)
prop001 = np.kron(ket0, np.kron(ket0, ket1)).T.dot(frth).dot(np.kron(ket0, np.kron(ket0, ket1)))
print(prop001)
prop010 = np.kron(ket0, np.kron(ket1, ket0)).T.dot(frth).dot(np.kron(ket0, np.kron(ket1, ket0)))
print(prop010)
prop011 = np.kron(ket0, np.kron(ket1, ket1)).T.dot(frth).dot(np.kron(ket0, np.kron(ket1, ket1)))
print(prop011)
prop100 = np.kron(ket1, np.kron(ket0, ket0)).T.dot(frth).dot(np.kron(ket1, np.kron(ket0, ket0)))
print(prop100)
prop101 = np.kron(ket1, np.kron(ket0, ket1)).T.dot(frth).dot(np.kron(ket1, np.kron(ket0, ket1)))
print(prop101)
prop110 = np.kron(ket1, np.kron(ket1, ket0)).T.dot(frth).dot(np.kron(ket1, np.kron(ket1, ket0)))
print(prop110)
prop111 = np.kron(ket1, np.kron(ket1, ket1)).T.dot(frth).dot(np.kron(ket1, np.kron(ket1, ket1)))
print(prop111)

*)

