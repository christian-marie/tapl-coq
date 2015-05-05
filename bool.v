Require Export Bool.
Require Export List.
Export ListNotations.

Require Export common.

Module BLang.


(* The terms of our boolean logic, all at one level *)
Inductive bterm : Type :=
  | BTrue   : bterm
  | BFalse  : bterm
  | BIf     : bterm -> bterm -> bterm -> bterm
  | BZero   : bterm
  | BSucc   : bterm -> bterm
  | BPred   : bterm -> bterm
  | BIsZero : bterm -> bterm.

(* Notation for if statements *)
Notation "'BIF' t1 'THEN' t2 'ELSE' t3 'FI'" :=
  (BIf t1 t2 t3) (at level 80, right associativity).


Reserved Notation "t '||' t'" (at level 50, left associativity).

(* Evaluation relations, defined inductively *)
Inductive bevalR : bterm -> bterm -> Prop :=
  | E_IfTrue: forall (t2 t3: bterm),
      (BIF BTrue THEN t2 ELSE t3 FI || t2)
  | E_IfFalse: forall (t2 t3: bterm),
      (BIF BFalse THEN t2 ELSE t3 FI || t3)
  | E_If: forall (t1 t1' t2 t3: bterm),
      (t1 || t1') ->
      (BIF t1 THEN t2 ELSE t3 FI || BIF t1' THEN t2 ELSE t3 FI)
  where "t '||' t'" := (bevalR t t') : type_scope.

(**
s = if true then false else false
def
t = if s then true else true
def
u = if false then true else true

if t then false else false -> if u then false else false

witnessed by the following derivation tree:

------------- E-IfTrue
s -> false

------------- E-If
t ->  u

------------- E-If
if t then false else false -> if u then false else false

**)

Definition s : bterm := 
  BIF BTrue THEN BFalse ELSE BFalse FI.

Definition t : bterm := 
  BIF s THEN BTrue ELSE BTrue FI.

Definition u : bterm := 
  BIF BFalse THEN BTrue ELSE BTrue FI.

Example Ex353:
  (BIF t THEN BFalse ELSE BFalse FI || BIF u THEN BFalse ELSE BFalse FI).
Proof.
  apply E_If.
  apply E_If.
  apply E_IfTrue.
Qed.

(**
Theorem [Determinacy of one-step evaluation]:
  If t -> t' and t -> t'' then t' == t''
**)

Theorem one_step_deterministic : forall t t' t'' : bterm,
  (t || t') ->
  (t || t'') -> 
  t' = t''.
Proof.
  intros t t' t'' erel1  erel2.
  generalize dependent t''.
  bevalR_cases (induction erel1; intros) Case.
  Case "E_IfTrue".
    inversion erel2. reflexivity.
    inversion H3.
  Case "E_IfFalse".
    inversion erel2. reflexivity.
    inversion H3.
  Case "E_If".
    bevalR_cases (inversion erel2) SCase.
    SCase "E_IfTrue".
      subst.
      inversion erel1.
    SCase "E_IfFalse".
      subst.
      inversion erel1.
    SCase "E_If".
      rewrite IHerel1 with t1'0.
      reflexivity.
      assumption.
Qed.

End BLang.
