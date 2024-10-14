Require Import Arith Lia Init.Datatypes List.
Require Import Coq.Logic.Classical.

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


Lemma mem_equiv_in : forall (l : list nat) (i : nat),
  mem i l <-> In i l.
Proof.
  intros; split.
  - induction l; intros; inversion H.
    + now left.
    + right. now apply IHl.
  - induction l; intros; inversion H.
    + now left.
    + right. now apply IHl.
Qed.
 

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


Lemma append_mem {t:Type} : forall (x:t) (x0 x1 : list t),  mem x (x0++(x::x1)).
Proof.
   intros x x0 x1.
   induction x0.
   simpl.
   left.
   auto.
   simpl.
   right.
   apply IHx0.
Qed.   

Lemma mem_append {t:Type}: forall (e :t) (x0 x1 : list t), mem e (x0++x1) -> mem e x0 \/ mem e x1.
Proof.
   intros e x0 x1 h1.
   induction x0.
   cut (mem e (nil ++ x1)).
   simpl.
   auto.
   apply h1.
   cut ( mem e ((a :: x0) ++ x1)).
   simpl.
   intro c.
   destruct c.
   auto.
   cut (e = a \/ (mem e x0 \/ mem e x1)).
   tauto.
   cut (mem e x0 \/ mem e x1).
   auto.
   apply IHx0.
   apply H.
   apply h1.
   Qed.

Lemma mem_append_2  {t:Type} : forall (e:t) (x0 x1 : list t), mem e x0 -> mem e (x0++x1).
Proof.
   intros.
   induction x0.
   cut False.
   tauto.
   generalize H.
   simpl.
   auto.
   simpl.
   generalize H.
   simpl.
   intro d.
   destruct d.
   auto.
   right.
   apply IHx0.
   auto.
Qed.

Lemma mem_append_3  {t:Type} : forall (e:t) (x0 x1 : list t), mem e x1 -> mem e (x0++x1).
Proof.
   intros.
   induction x0.
   (* cas de base *)
   simpl.
   auto.
  (* cas général *)
  simpl.
  right.
  auto.
Qed.

Lemma mem_exists_append {t:Type} : forall (e:t) (l:list t), mem e l -> exists (l1 l2 : list t), l=l1++(e::l2).
Proof.
   intros.
   induction l.
   cut False.
   tauto.
   generalize H.
   simpl.
   auto.
   generalize H.
   simpl.
   intro d.
   destruct d.
   exists nil.
   exists l.
   rewrite H0.
   simpl.
   reflexivity.
   generalize (IHl H0).
   intro.
   destruct H1.
   destruct H1.
   exists (a::x).
   exists x0.
   rewrite H1.
   auto.
Qed.


Fixpoint is_sorted (p:list nat) : Prop :=
match p with
| nil => True
| t :: q => (forall (e:nat), mem e q -> t>e) /\ is_sorted q
end.

Lemma sorted_sorted : forall (x0 x1 : list nat), is_sorted (x0++x1) -> is_sorted x0 /\   is_sorted x1.
Proof.
   intros.
   induction x0.
   simpl.
   generalize H.
   simpl.
   tauto.
   generalize H.
   simpl.
   intro.
   destruct H0.
   split.
   split.
   intros.
   apply H0.
   apply mem_append_2.
   exact H2.
   apply IHx0.
   exact H1.
   apply IHx0.
   exact H1.
Qed.

Lemma sorted_middle_x1 : forall (x:nat) (x0 x1 : list nat), 
is_sorted (x0++(x::x1)) -> (forall (e :nat), mem e x1 -> x > e).
Proof.
   intros.
   cut (is_sorted (x::x1)).
   simpl.
   intro.
   destruct H1.
   apply (H1 e).
   exact H0.
   apply (sorted_sorted x0 (x::x1)).
   exact H.
Qed.

Lemma sorted_middle_x0 :  forall (x:nat) (x0 x1 : list nat), 
is_sorted (x0++(x::x1)) -> (forall (e:nat), mem e x0 -> x < e).
Proof.
   intros.
   induction x0.
   cut False.
   tauto.
   generalize H0.
   simpl.
   tauto.
   generalize H0.
   simpl.
   intro.
   destruct H1.
   generalize H.
   rewrite <- H1.
   simpl.
   intro.
   destruct H2.
   apply (H2 x).
   apply append_mem.
   apply IHx0.
   generalize H.
   simpl.
   tauto.
   exact H1.
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


Fixpoint mapi_aux {A B : Type} (f : nat -> A -> B) (l : list A) (i : nat) : list B :=
  match l with
  | nil => nil
  | cons x t => cons (f i x) (mapi_aux f t (S i))
  end.

Definition mapi {A B : Type} (f : nat -> A -> B) (l : list A) : list B :=
  mapi_aux f l 0.

Lemma mapi_aux_length {A B : Type} (f : nat -> A -> B) l i :
  length (mapi_aux f l i) = length l.
Proof.
  generalize dependent i.
  induction l; intros.
  - reflexivity.
  - simpl. now rewrite IHl.
Qed.

Theorem mapi_length {A B : Type} (f : nat -> A -> B) l :
  length (mapi f l) = length l.
Proof.
  apply mapi_aux_length.
Qed.

Lemma mapi_aux_nth {A B : Type} (f : nat -> A -> B) l i j err :
  nth j (mapi_aux f l i) (f (i + j) err) = f (i + j) (nth j l err).
Proof.
  generalize dependent i.
  generalize dependent j.
  induction l; intros.
  - simpl. now destruct j.
  - simpl. destruct j.
    + f_equal. lia.
    + replace (i + S j) with ((S i) + j); [| lia ].
      apply IHl.
Qed.

Theorem mapi_nth {A B : Type} (f : nat -> A -> B) l j err :
  nth j (mapi f l) (f j err) = f j (nth j l err).
Proof.
  apply mapi_aux_nth.
Qed.


Fixpoint is_set {a:Type} (l:list a) : Prop :=
  match l with
  | nil => True
  | t::q => not (mem t q) /\ (is_set q)
  end.

Definition is_subset {a:Type} (l1 l2 : list a) : Prop :=
  (is_set l1) /\ (is_set l2) /\ (forall (e : a), mem e l1 -> mem e l2) .
  
Definition is_strict_subset  {a:Type} (l1 : list a) (l2 : list a) : Prop :=
  (is_subset l1 l2) /\ (exists (e : a), mem e l2 /\ not (mem e l1)).

Definition leq {a:Type} (l1 l2: list a) : Prop :=
   forall (e : a), mem e l1 <-> mem e l2.

Lemma is_subset_leq_or_is_strict_subset  {a:Type} : forall (l1 l2: list a),
   is_subset l1 l2 -> leq l1 l2 \/ is_strict_subset l1 l2.
Proof.
   intro l1.
   intro l2.
   intro.
   cut ((exists (e : a), mem e l2 /\ not (mem e l1)) \/ ~(exists (e : a), mem e l2 /\ not (mem e l1))).
   intro d.
   destruct d.
   (* exists (e : a), mem e l2 /\ not (mem e l1) *)
   right.
   unfold is_strict_subset.
   tauto.
   (* ~ exists (e : a), mem e l2 /\ not (mem e l1) *)
   left.
   unfold is_subset in H.
   destruct H.
   destruct H1.
   unfold leq.
   split.
   (* mem e l1 -> mem e l2 *)
   auto.
   (* mem e l2 -> mem e l1 *)
   intro.
   cut (mem e l1 \/ ~mem e l1).
   intro d.
   destruct d.
   auto.
   cut False.
   tauto.
   generalize H0.
   unfold not.
   intro.
   apply H5.
   exists e.
   tauto.
   tauto.
   tauto.
Qed.

Lemma init_is_set (n : nat) :
  is_set (init n).
Proof.
  induction n.
  - now simpl.
  - simpl. split.
    + intros absurd.
      apply init_correct in absurd.
      lia.
    + assumption.
Qed.

Lemma diff_is_set (s1 s2 : list nat) :
  is_set s1 -> is_set s2 -> is_set (diff s1 s2).
Proof.
  intros.
  induction s1.
  - trivial.
  - simpl.
    inversion H.
    destruct (mem_nat a s2) eqn:Heq.
    + auto.
    + split.
      intros absurd. now apply diff_correct in absurd.
      auto.
Qed.

Lemma sorted_is_set (s : list nat) :
  is_sorted s -> is_set s.
Proof.
  induction s; intros H.
  - trivial.
  - inversion H. simpl. split.
    + intros absurd.
      cut (a > a). lia.
      auto.
    + auto.
Qed.