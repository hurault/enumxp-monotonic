Require Import Arith Lia Init.Datatypes List.

Open Scope list_scope.

(* About list *)
Fixpoint mem {a:Type} (i:a) (p: list a) : Prop :=
  match p with
  | nil => False
  | x :: q => (i=x) \/ mem i q 
  end.



Fixpoint mem_nat (i:nat) (p: list nat) : bool :=
  match p with
  | nil => false
  | x :: q => if (eq_nat_dec i x) then true else (mem_nat i q) 
  end.
 

Lemma mem_coherent : forall (i:nat) (p: list nat), mem_nat i p = true <-> mem i p.
Proof.
   induction p.
   simpl.
   lia.
   split.
   simpl.
   destruct (Nat.eq_dec i a).
   auto.
   rewrite IHp.
   auto.
   simpl.
   destruct (Nat.eq_dec i a).
   auto.
   rewrite IHp.
   intro.
   destruct H.
   tauto.
   apply H.
Qed.

Lemma mem_not_mem : forall (i:nat) (p: list nat), mem i p \/ ~ mem i p.
Proof.
   intros.
   induction p.
   simpl.
   auto.
   cut (i=a \/ i<>a).
   intro di.
   destruct di.
   left.
   simpl.
   auto.
   destruct IHp.
   left.
   simpl.
   auto.
   right.
   auto.
   simpl.
   tauto.
   lia.
Qed.

Lemma mem_coherent_conv : forall (i : nat) (p : list nat), mem_nat i p = false <-> ~ mem i p.
Proof.
  intros. split; intros.
  - destruct (mem_not_mem i p) as [ Hmem | Hnotmem ].
    + apply mem_coherent in Hmem. congruence.
    + exact Hnotmem.
  - destruct (mem_nat i p) eqn:Heq.
    + apply mem_coherent in Heq. contradiction.
    + reflexivity.
Qed.


Lemma list_mem_not_nil {a:Type}: 
forall (x :a) (l:list a), mem x l -> l <> nil.
Proof.
intro.
destruct l.
simpl.
tauto.
intro.
discriminate.
Qed.

Lemma list_mem_middle  {a:Type}:  forall (x :a) (x0 x1:list a),
mem x (x0 ++ x :: x1).
Proof.
intros.
induction x0.
simpl.
auto.
simpl.
auto.
Qed.

(* x0++(Cons x x1) = (Cons i Nil) -> x0=Nil /\ x=i /\ x1=Nil *)
Lemma destruct_list_1elt  {a:Type} :
  forall (x i:a) (x0 x1:list a),
  ((app x0 (cons x x1)) = (cons i nil)) ->
  (x0 = nil) /\ (x = i) /\ (x1 = nil).
Proof.
intros.
destruct x0.
(* x0 = nil -> OK*)
simpl in H.
injection H.
auto.
(* x0 <> nil *)
(* x1 <> nil *)
cut False.
tauto.
simpl in H.
cut (x0 ++ x :: x1 = nil).
cut (x0 ++ x :: x1 <> nil).
tauto.
(* x0 ++ x :: x1 <> nil *)
cut (mem x (x0 ++ x :: x1)).
apply list_mem_not_nil.
apply list_mem_middle.
(* x0 ++ x :: x1 = nil *)
injection H.
auto.
Qed.

(* Nil++(Cons x x1) = (Cons i p) -> x=i /\ x1=p *)
Lemma destruct_list_debutvide {a:Type}:
  forall (x i :a) (p x1 : list a),
  ((app nil (cons x x1)) = (cons i p)) -> (x = i) /\ (x1 = p).
Proof.
intros.
generalize H.
simpl.
intro I.
injection I.
auto.
Qed.


Fixpoint diff (l1 l2 : list nat) : list nat :=
  match l1 with
  | nil => nil
  | x :: l1' =>
    if mem_nat x l2 then diff l1' l2
    else x :: diff l1' l2
  end.

Theorem diff_correct (l1 l2 : list nat) :
  forall j, mem j (diff l1 l2) <-> mem j l1 /\ ~ mem j l2.
Proof.
  intros j. split; intros H.
  - (* -> *)
    induction l1 as [| x l1' IH ].
    + inversion H.
    + destruct (mem_nat x l2) eqn:Hmem.
      * simpl in H; rewrite Hmem in H.
        split; [right|]; tauto.
      * simpl in H; rewrite Hmem in H.
        inversion H.
        split. left; tauto.
        intros absurd; apply mem_coherent in absurd. 
        rewrite H0 in absurd. rewrite absurd in Hmem. discriminate.
        split; [right|]; tauto.
  - (* <- *)
    destruct H as (H1 & H2).
    induction l1 as [| x l1' IH ].
    + inversion H1.
    + assert (H3 : mem_nat j l2 = false).
      { cut (mem_nat j l2 <> true). destruct (mem_nat j l2); tauto.
      intros absurd. apply mem_coherent in absurd; contradiction. }
      inversion H1.
      * subst. simpl. rewrite H3.
        now left.
      * simpl. destruct (mem_nat x l2).
        tauto. right; tauto.
Qed.


Fixpoint init (n : nat) :=
  match n with
  | 0 => nil
  | S n => n :: init n
  end.

Theorem init_correct (n : nat) :
  forall (p : nat), mem p (init n) <-> p < n.
Proof.
  intros p. split; intros H.
  - (* -> *)
    induction n.
    + inversion H.
    + inversion H.
      * rewrite H0. apply le_n.
      * apply le_S, IHn, H0.
  - (* <- *)
    induction H.
    + now left.
    + right. assumption.
Qed.