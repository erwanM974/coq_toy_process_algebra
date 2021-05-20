(* =========================================================== *)
(**
* Example Coq Proof on a toy process algebra example

We define a very simple process algebra with (strict) sequential and alternative composition.
We then prove the equivalence of two formulations of a trace semantics for this
process algebraic language.
Those are:
- a denotational formulation defined inductively by composition of sets of traces
- a structural operational formulation as is classically done in process calculus
**)

Require Import List.
Require Import Coq.Program.Equality.

Parameter E : Set.

Definition Sequence : Type := list E.

Inductive PATerm : Set := 
  empty_pa : PATerm 
  |event_pa : E -> PATerm
  |seq_pa:PATerm->PATerm->PATerm
  |alt_pa:PATerm->PATerm->PATerm.

Fixpoint terminates (p : PATerm) : Prop :=
  match p with
    | empty_pa       => True
    | (event_pa e)   => False
    | (seq_pa p1 p2) => (terminates p1) /\ (terminates p2)
    | (alt_pa p1 p2) => (terminates p1) \/ (terminates p2)
  end.

Inductive is_next_of : PATerm -> E -> PATerm -> Prop :=
|next_event : forall (e:E), 
                 (is_next_of (event_pa e) e empty_pa)
|next_seq_left   : forall (e:E) (p1 p2 p1' : PATerm),
                 (is_next_of p1 e p1')
                   -> (is_next_of (seq_pa p1 p2) e (seq_pa p1' p2))
|next_seq_right  : forall (e:E) (p1 p2 p2' : PATerm),
                 ( (is_next_of p2 e p2') /\ (terminates p1) )
                   -> (is_next_of (seq_pa p1 p2) e p2')
|next_alt_left   : forall (e:E) (p1 p2 p1' : PATerm),
                 (is_next_of p1 e p1')
                   -> (is_next_of (alt_pa p1 p2) e p1')
|next_alt_right  : forall (e:E) (p1 p2 p2' : PATerm),
                 (is_next_of p2 e p2')
                   -> (is_next_of (alt_pa p1 p2) e p2').

Inductive sem_op : PATerm -> Sequence -> Prop :=
 | sem_op_empty  : forall (p :PATerm),
                      (terminates p)  
                      -> (sem_op p nil)
 | sem_op_event : forall (p p':PATerm) (e:E) (s:Sequence),
                      (is_next_of p e p')/\(sem_op p' s)
                      -> (sem_op p (cons e s) ).

Fixpoint sem_de (p : PATerm) : (Sequence -> Prop) :=
 match p with
    | empty_pa       => fun s:Sequence => s = nil
    | (event_pa e)   => fun s:Sequence => s = e :: nil
    | (seq_pa p1 p2) => fun s:Sequence => exists (s1 s2 : Sequence), (sem_de p1 s1) /\ (sem_de p2 s2) /\ (s = s1 ++ s2)
    | (alt_pa p1 p2) => fun s:Sequence => (sem_de p1 s) \/ (sem_de p2 s)
  end.

Lemma terminates_implies_de_accept_empty (p : PATerm) :
  (terminates p) -> (sem_de p nil).
Proof.
intros H.
induction p.
- simpl. reflexivity.
- simpl in H. contradiction.
- simpl. exists nil. exists nil.
  simpl in H. destruct H as (H1,H2).
  apply IHp1 in H1. apply IHp2 in H2.
  split.
  + assumption.
  + split.
    * assumption.
    * simpl. reflexivity.
- simpl. simpl in H. destruct H.
  + left. apply IHp1. assumption.
  + right. apply IHp2. assumption.
Qed.

Lemma execute_keep_de (p p': PATerm) (e:E) (s:Sequence) :
  (is_next_of p e p') /\ (sem_de p' s)
    -> (sem_de p (cons e s) ).
Proof.
intros H.
destruct H as (H1,H2).
dependent induction p.
- inversion H1.
- inversion H1.
  destruct H0. destruct H3. destruct H4.
  inversion H2. simpl. reflexivity.
- inversion H1;
  symmetry in H; destruct H;
  symmetry in H3; destruct H3;
  symmetry in H0; destruct H0;
  destruct H4.
  + simpl. inversion H2 as (s1,H).
    destruct H as (s2,H). exists (e :: s1).
    exists s2.
    destruct H. destruct H0.
    split.
    { apply (IHp1 p1') ; assumption. }
    { split.
      - assumption.
      - simpl. destruct H3. reflexivity.
    }
  + destruct H5.
    simpl. exists nil. exists (e :: s).
    split.
    { apply terminates_implies_de_accept_empty.
      assumption. }
    { split.
      - apply (IHp2 p2') ; assumption.
      - simpl. reflexivity.
    }
- simpl. 
  inversion H1 ;
  symmetry in H; destruct H;
  symmetry in H3; destruct H3;
  symmetry in H0; destruct H0;
  destruct H4.
  + left. apply (IHp1 p1') ; assumption.
  + right. apply (IHp2 p2') ; assumption.
Qed.

Theorem op_implies_de (p : PATerm) (s : Sequence) :
  (sem_op p s) -> (sem_de p s).
Proof.
intros H.
dependent induction s generalizing p.
- apply terminates_implies_de_accept_empty.
  inversion H. assumption.
- inversion H. 
  symmetry in H1. destruct H1.
  destruct H0.
  symmetry in H3. destruct H3.
  destruct H2.
  apply (execute_keep_de p p' e s).
  split.
  + assumption.
  + apply (IHs p').
    assumption.
Qed.

Lemma de_accept_empty_implies_terminates (p : PATerm) :
  (sem_de p nil) -> (terminates p).
Proof.
intros H.
induction p.
- simpl. reflexivity.
- simpl in H. inversion H.
- simpl. simpl in H.
  destruct H as (s1,H).
  destruct H as (s2,H).
  destruct H. destruct H0.
  symmetry in H1.
  apply app_eq_nil in H1.
  destruct H1.
  symmetry in H1. destruct H1.
  symmetry in H2. destruct H2.
  split.
  + apply IHp1. assumption.
  + apply IHp2. assumption.
- simpl. simpl in H.
  destruct H.
  + left. apply IHp1. assumption.
  + right. apply IHp2. assumption.
Qed.

Lemma de_accept_cons_implies_execution_possible (p : PATerm) (e:E) (s:Sequence) :
  (sem_de p (cons e s) )
    -> (exists (p':PATerm), (is_next_of p e p') /\ (sem_de p' s) ).
Proof.
intros H.
dependent induction p.
- simpl in H. inversion H.
- simpl in H. inversion H.
  symmetry in H1. destruct H1.
  symmetry in H2. destruct H2.
  exists empty_pa. simpl.
  split.
  + apply next_event.
  + reflexivity.
- simpl in H.
  destruct H as (s1,H).
  destruct H as (s2,H).
  destruct H.
  destruct H0. dependent induction s1.
  + simpl in H1. destruct H1.
    apply IHp2 in H0.
    destruct H0 as (p2',H0).
    destruct H0.
    exists p2'.
    split.
    * apply next_seq_right.
      split.
      { assumption. }
      { apply de_accept_empty_implies_terminates.
        assumption. }
    * assumption.
  + inversion H1. 
    destruct H3. apply IHp1 in H. 
    destruct H as (p1',H). 
    exists (seq_pa p1' p2).
    destruct H.
    split.
    * apply next_seq_left. assumption.
    * simpl. exists s1. exists s2.
      split.
      { assumption. }
      { split. 
        - assumption. 
        - reflexivity.
      }
- simpl in H. destruct H.
  + apply IHp1 in H.
    destruct H as (p1',H).
    destruct H.
    exists p1'.
    split.
    * apply next_alt_left. assumption.
    * assumption.
  + apply IHp2 in H.
    destruct H as (p2',H).
    destruct H.
    exists p2'.
    split.
    * apply next_alt_right. assumption.
    * assumption.
Qed.

Theorem de_implies_op (p : PATerm) (s : Sequence) :
  (sem_de p s) -> (sem_op p s).
Proof.
intros H.
dependent induction s generalizing p. 
- apply sem_op_empty.
  apply de_accept_empty_implies_terminates.
  assumption.
- apply de_accept_cons_implies_execution_possible in H.
  destruct H as (p',H).
  destruct H.
  apply (sem_op_event p p').
  split.
  + assumption.
  + apply IHs. assumption.
Qed.
  
Theorem sem_equivalence (p : PATerm) (s : Sequence) :
  (sem_op p s) <-> (sem_de p s).
Proof.
split.
- apply op_implies_de.
- apply de_implies_op.
Qed.





