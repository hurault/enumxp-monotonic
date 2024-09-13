Require Import Arith Lia Init.Datatypes.

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
