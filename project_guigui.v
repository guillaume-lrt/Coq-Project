(* -------------------------------------------------------------------- *)
Require Import Bool Arith List ssreflect.

Local Notation "~~ b" := (negb b) (at level 2).
Local Notation "b1 == b2" := (eqb b1 b2) (at level 70).

(* -------------------------------------------------------------------- *)
(* We are here interested in proving facts about propositional logic.   *
 *                                                                      *
 * The purpose of this exercice is the proof of the 2 following facts:  *
 * - 1. natural deduction is correct w.r.t. the interpretation of       *
 *      assertions;                                                     *
 * - 2. it is decidable to check that an assertion is universally       *
 *      valid. We are going to check that by implementing a sound       *
 *      normalization algorithm for assertions, and then to write, in   *
 *      Coq, a simple decision for the universal validity of the        *
 *      normalized assertions.                                          *)

(* ==================================================================== *)
(* The following datatype describe the syntax of assertions. The        *
 * constructors for True, the negation and the double implication       *
 * are not primitive. They are expressed using the other constructions  *
 * of the logic.                                                        *)

Inductive prop : Type :=
| PVar (_ : nat)                (* Propositional variable *)
| PFalse                        (* False *)
| PAnd (_ : prop) (_ : prop)    (* Conjunction *)
| POr  (_ : prop) (_ : prop)    (* Disjunction *)
| PImp (_ : prop) (_ : prop).   (* Implication *)

Notation PTrue    := (PImp PFalse PFalse).
Notation PNot p   := (PImp p PFalse).
Notation PIff p q := (PAnd (PImp p q) (PImp q p)).

(* -------------------------------------------------------------------- *)
(* A valuation is simply a function from propositional variables to     *
 * truth values.                                                        *)

Notation valuation := (nat -> bool) (only parsing).

(* -------------------------------------------------------------------- *)
(* Complete the definition of the following function that computes the  *
 * semantic of an assertion from the given valuation.                   *)

Fixpoint sem (v : valuation) (p : prop) : bool :=
  match p with
  |PVar n => v n
  |PFalse => false
  |POr p1 p2 => 
  if orb (sem v p1) (sem v p2) then true
  else false
  |PAnd p1 p2 => 
  if andb (sem v p1) (sem v p2) then true
  else false
  |PImp p1 p2 => 
  if orb ~~(sem v p1) (sem v p2) then true
  else false
  end.

(* -------------------------------------------------------------------- *)
(* We now define the notions of begin satisfiable under a valuation     *
 * and of being universally valid.                                      *)

Definition sat (v : valuation) (p : prop) :=
  sem v p = true.

Definition valid (p : prop) :=
  forall v, sat v p.

(* -------------------------------------------------------------------- *)
(* The following inductive predicate defines the notion of judgement    *
 * in natural deduction. This predicate accepts two arguments:          *
 *                                                                      *
 * - a list of assertions that stands for the proof context;            *
 * - the assertion that is proven under this context.                   *)

Inductive nd : list prop -> prop -> Prop :=
  (* Non-structural rules *)
| Ax env p :
    In p env -> nd env p

| Absurd env p :
    nd (PNot p :: env) PFalse -> nd env p

  (* Introduction rules *)

| AndI   env p q : nd env p -> nd env q -> nd env (PAnd p q)
| OrIL   env p q : nd env p -> nd env (POr p q)
| OrIR   env p q : nd env q -> nd env (POr p q)
| ImpI   env p q : nd (p :: env) q -> nd env (PImp p q)

  (* Elimination rules *)

| FalseE env p     : nd env PFalse -> nd env p
| AndEL  env p q   : nd env (PAnd p q) -> nd env p
| AndER  env p q   : nd env (PAnd p q) -> nd env q
| OrE    env p q r : nd env (POr p q) -> nd (p :: env) r -> nd (q :: env) r -> nd env r
| ImpE   env p q   : nd env p -> nd env (PImp p q) -> nd env q
.

(* -------------------------------------------------------------------- *)
(* We first start to prove that the predicate [dn] is stable by         *
 * weakening or permuting the proof context. The following definition   *
 * defines an ordering over proof contexts.                             *)

Definition subenv (e1 e2 : list prop) :=
  forall q, In q e1 -> In q e2.

(* -------------------------------------------------------------------- *)
(* Show that [dn] is monotone from [subenv]                             *)
Lemma app_subenv (e1 e2 : list prop)(p: prop) :
 forall p, (subenv e1 e2) -> subenv (p :: e1)(p :: e2).
Proof.
move => p0. move => h.
move => q. simpl. move => h1.
case h1; auto.
Qed.

Lemma subenv_nd (e1 e2 : list prop) (p : prop) :
  subenv e1 e2 -> nd e1 p -> nd e2 p.
Proof.
move => i12 d.
move: e2 i12.
induction d; move => e2 i12. 
apply Ax; apply i12; apply H.
apply Absurd. apply IHd. apply app_subenv; assumption.
apply AndI. apply IHd1. apply i12. apply IHd2. apply i12.
apply OrIL. apply IHd. apply i12.
apply OrIR. apply IHd. apply i12.
apply ImpI. apply IHd. apply app_subenv; assumption.
apply FalseE. apply IHd. apply i12.
apply (AndEL e2 p q). apply IHd; apply i12.
apply (AndER e2 p q). apply IHd; apply i12.
apply (OrE e2 p q r). apply IHd1. apply i12. apply IHd2. apply app_subenv; assumption. apply IHd3. apply app_subenv; assumption.
apply (ImpE e2 p q). apply IHd1. apply i12. apply IHd2. apply i12.
Qed.

(* -------------------------------------------------------------------- *)
(* We now prove the correctness of [dn]. Prove the following lemma,     *
 * by induction on [nd env p].                                          *)

Lemma correctness (env : list prop) (p : prop) :
  nd env p -> forall v, (forall q, In q env -> sat v q) -> sat v p.
Proof.
move => d.
induction d; move => v; move => h; rewrite /sat.

apply h. assumption.

case vp: (sem v p). reflexivity. 
apply (IHd v).
move => q [<-|e].
  by rewrite /sat /= vp /=.
apply h. assumption.

rewrite /= IHd1 //= IHd2 //=.

rewrite /= IHd //=.

rewrite /= IHd //=. destruct (sem v p); auto.

simpl.
case vp: (sem v p) => //=. rewrite IHd //= => r [<-|e]; auto.

case vp: (sem v p) => //=. apply (IHd v). assumption.

rewrite /sat /= in IHd.
case vp: (sem v p) => //=.
move: (IHd v).
rewrite vp.
move => h1. apply h1. exact h.

rewrite /sat /= in IHd.
case vq: (sem v q) => //=.
move: (IHd v).
rewrite vq.
destruct (sem v p); move => h1; apply h1; exact h.

rewrite /sat /= in IHd1 IHd2 IHd3 h.
case vp: (sem v p); case vq: (sem v q); case vr: (sem v r) => //=.
rewrite -vr; apply IHd2. move => q0 [<-|h2]; auto.
rewrite -vr; apply IHd2. move => q0 [<-|h2]; auto.
rewrite -vr; apply IHd3. move => q0 [<-|h2]; auto.
move: (IHd1 v). rewrite vq vp /=. move => h1. apply h1. exact h.

rewrite /sat /= in IHd1 IHd2 h.
case vp: (sem v p); case vq: (sem v q) => //=.
move: (IHd2 v). rewrite vq vp /=; auto.
rewrite -vp; apply IHd1; auto.
Qed.

(* ==================================================================== *)
(* We are now interested in deciding if a given assertion is            *
 * universally valid or not. For that, we first normalize the           * 
 * assertions, obtaining an expression built from boolean constants,    *
 * propositionnal variables and if-then-else statements whose           *
 * condition is a propositional variables.                              *)

(* -------------------------------------------------------------------- *)
(* We start by defining an intermediate datatype that describe the      *
 * syntax of normalized assertions, except for the side conditions      *
 * of the if-then-else expressions that are still unconstrained.        *)

Inductive ifForm : Type :=
| PIVar   (_ : nat)                               (* variable propositionnelle *)
| PIConst (_ : bool)                              (* constante true / false *)
| PIIf    (_ : ifForm) (_ : ifForm) (_ : ifForm). (* if-then-else *)

(* -------------------------------------------------------------------- *)
(* Define the semantic of the assertions of type [ifForm].              *)

Fixpoint ifsem (v : valuation) (p : ifForm) : bool :=
  match p with
  |PIVar n => v n
  |PIConst true => true
  |PIConst false => false
  |PIIf p1 p2 p3 => if ifsem v p1 then ifsem v p2 else ifsem v p3
end.


(* -------------------------------------------------------------------- *)
(* Write the normalization functions from assertions of type [prop] to  *
 * assertions of type [ifForm].                                         *)

Fixpoint ifForm_of_prop (p : prop) :=
  match p with
  |PVar n => PIVar n
  |PFalse => PIConst false
  |PAnd p1 p2 => PIIf (ifForm_of_prop p1) (ifForm_of_prop p2) (PIConst false)
  |POr p1 p2 => PIIf (ifForm_of_prop p1) (PIConst true) (ifForm_of_prop p2)
  |PImp p1 p2 => PIIf (ifForm_of_prop p1) (ifForm_of_prop p2) (PIConst true)
end.

(* -------------------------------------------------------------------- *)
(* Show that your normalization function is correct w.r.t. [ifsem].     *)

Lemma ifForm_correct (v : valuation) (p : prop) :
  sem v p = ifsem v (ifForm_of_prop p).
Proof.
induction p. 
  simpl. trivial.
  simpl. trivial.
  simpl. rewrite -IHp1. rewrite -IHp2. case vp1: (sem v p1); case vp2: (sem v p2); simpl; trivial.
  simpl. rewrite -IHp1. rewrite -IHp2. case vp1: (sem v p1); case vp2: (sem v p2); simpl; trivial.
  simpl. rewrite -IHp1. rewrite -IHp2. case vp1: (sem v p1); case vp2: (sem v p2); simpl; trivial.
Qed.

(* -------------------------------------------------------------------- *)
(* We now define the syntax of normalized assertions. We see that the   *
 * conditions of the if-then-else expressions are now enforced to be    *
 * propositional variables.                                             *)

Inductive nifForm : Type :=
| PNIVar   (_ : nat)
| PNIConst (_ : bool)
| PNIIf    (_ : nat) (_ : nifForm) (_ : nifForm).

(* -------------------------------------------------------------------- *)
(* Define the semantic of the assertions of type [nifForm].             *)

Fixpoint nifsem (v : valuation) (p : nifForm) : bool :=
  match p with
  |PNIVar n => v n
  |PNIConst true => true
  |PNIConst false => false
  |PNIIf n p1 p2 => if v n then nifsem v p1 else nifsem v p2  
end.

(* -------------------------------------------------------------------- *)
(* Write below the normalization function for assertions of type        *
 * [ifForm], obtaining assertions of type [nifForm].                    *)

Fixpoint normif (c t f : nifForm) {struct c} :=
  ...

Fixpoint norm (p : ifForm) : nifForm :=
  ...

(* -------------------------------------------------------------------- *)
(* Show that the normalization functions are correct w.r.t. [nifsem].   *)

Lemma normif_correct (v : valuation) (c t f : nifForm) :
  nifsem v (normif c t f) = if nifsem v c then nifsem v t else nifsem v f.
Proof. elim c; simpl; auto.
...
Qed.

(* -------------------------------------------------------------------- *)
Lemma norm_correct (v : valuation) (p : ifForm) : nifsem v (norm p) = ifsem v p.
Proof.
...
Qed.

(* -------------------------------------------------------------------- *)
(* Finally, we provide a procedure that decides if a normalized         *
 * assertion is universally valid w.r.t. [nifasm].                      *)

Definition xt (v : nat -> option bool) (x : nat) (b : bool) :=
  fun y => if beq_nat x y then Some b else v y.

Fixpoint nifForm_tauto_r (v : nat -> option bool) (p : nifForm) :=
  match p with
  | PNIVar   x => match v x with Some true => true | _ => false end
  | PNIConst b => b

  | PNIIf x t f =>
    match v x with
    | Some true  => nifForm_tauto_r v t
    | Some false => nifForm_tauto_r v f
    | None       =>
           nifForm_tauto_r (xt v x true ) t
        && nifForm_tauto_r (xt v x false) f
    end
  end.

Definition nifForm_tauto p := nifForm_tauto_r (fun _ => None) p.

(* -------------------------------------------------------------------- *)
(* Show the correctness of the procedure...                             *)

Lemma nifForm_tauto_r_correct (xv : nat -> option bool) (p : nifForm) :
     nifForm_tauto_r xv p = true
  -> forall v, (forall x b, xv x = Some b -> v x = b)
       -> nifsem v p = true.
Proof.
...
Qed.

(* -------------------------------------------------------------------- *)
Lemma nifForm_tauto_correct (p : nifForm) :
  nifForm_tauto p = true -> forall v, nifsem v p = true.
Proof.
...
Qed.

(* -------------------------------------------------------------------- *)
(* ...and its completness.                                              *)

Lemma nifForm_tauto_r_complete (xv : nat -> option bool) (p : nifForm) :
     nifForm_tauto_r xv p = false
  -> exists v, (forall x b, xv x = Some b -> v x = b) /\ nifsem v p = false.
Proof.
...
Qed.

(* -------------------------------------------------------------------- *)
Lemma nifForm_tauto_complete (p : nifForm) :
  nifForm_tauto p = false -> exists v, nifsem v p = false.
Proof.
...
Qed.

(* -------------------------------------------------------------------- *)
(* From this, define a decision procedure for the univdesal validity    *
 * and non-normalized assertions.                                       *)

Definition is_tautology (p : prop) : bool :=
  ...

(* -------------------------------------------------------------------- *)
(* Show the correctness of the procedure...                             *)

Lemma is_tautology_correct (p : prop) : is_tautology p = true -> valid p.
Proof.
...
Qed.

(* -------------------------------------------------------------------- *)
(* ...and its completness.                                              *)

Lemma is_tautology_complete (p : prop) :
  is_tautology p = false -> exists v, sem v p = false.
Proof.
...
Qed.
