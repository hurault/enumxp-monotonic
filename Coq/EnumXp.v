Require Import Extraction.
Require Import Program.
Require Import Arith Lia Init.Datatypes.
Require Import Coq.Program.Wf.
Require Import Coq.Logic.Classical.
Require Import Coq.Logic.Classical_Prop.
Require Import Coq.Logic.Classical_Pred_Type.

Require Import Recdef.

Require Import Orders.
Require Import Coq.Structures.OrderedType.

Require Import MSets.
Require Import MSetProperties.
Require Import MSetInterface.


Inductive literal : Type :=
  | top : nat -> literal
  | bot : nat -> literal.

Module OWL <: Orders.OrderedType.
Definition t := literal.
Global Transparent t.
Definition eq a b := match a with
  | top x => match b with 
    | bot _ => False
    | top y => eq x y
    end
  | bot x => match b with 
    | bot y => eq x y
    | top _ => False
    end
  end.

Instance eq_equiv : Equivalence eq.
Proof.
  unfold eq.
  split.
  unfold Reflexive.
  intro.
  destruct x.
  auto.
  auto.
  unfold Symmetric.
  intro;intro.
  destruct x.
  destruct y.
  auto.
  auto.
  destruct y.
  auto.
  auto.
  unfold Transitive.
  intro;intro;intro.
  destruct x.
  destruct y.
  intro.
  destruct z.
  rewrite H.
  auto.
  auto.
  tauto.
  destruct y.
  tauto.
  intro.
  destruct z.
  auto.
  rewrite H.
  auto.
Defined.

Definition lt a b := 
match a with
| top x => match b with 
  | bot y => lt x y
  | top y => lt x y
  end
| bot x => match b with 
  | bot y => lt x y
  | top y => lt x y \/ Nat.eq x y
  end
end.

Instance lt_strorder : StrictOrder lt.
Proof.
  unfold lt.
  split.
  unfold Irreflexive.
  unfold Reflexive.
  intro.
  unfold complement.
  destruct x.
  lia.
  lia.
  unfold Transitive.
  destruct x.
  intro.
  intro.
  destruct y.
  intro.
  destruct z.
  lia.
  auto.
  lia.
  intro.
  destruct z.
  lia.
  lia.
  intro.
  intro.
  destruct y.
  intro.
  destruct z.
  lia.
  lia.
  intro.
  destruct z.
  lia.
  lia.
Defined.

Instance lt_compat : Proper (eq ==> eq ==> iff) lt.
Proof.
  split.
  unfold lt.
  destruct x.
  destruct x0.
  intro.
  destruct y.
  destruct y0.
  elim H.
  elim H0.
  exact H1.
  elim H0.
  elim H.
  intro.
  destruct y.
  destruct y0.
  elim H0.
  elim H.
  elim H0.
  exact H1.
  elim H.
  destruct x0.
  intro.
  destruct y.
  elim H.
  destruct y0.
  elim H.
  elim H0.
  exact H1.
  elim H0.
  intro.
  destruct y.
  elim H.
  destruct y0.
  elim H0.
  elim H.
  elim H0.
  exact H1.
  unfold lt.
  destruct y.
  destruct y0.
  intro.
  destruct x.
  destruct x0.
  cut (n<n0).
  elim H.
  elim H0.
  auto.
  exact H1.
  elim H0.
  elim H.
  intro.
  destruct x.
  destruct x0.
  elim H0.
  cut (n<n0).
  elim H.
  elim H0.
  auto.
  exact H1.
  elim H.
  destruct y0.
  intro.
  destruct x.
  elim H.
  destruct x0.
  cut (n<n0 \/ Nat.eq n n0).
  elim H.
  elim H0.
  auto.
  exact H1.
  elim H0.
  destruct x0.
  elim H0.
  intro.
  destruct x.
  elim H.
  cut (n<n0).
  elim H.
  elim H0.
  auto.
  exact H1.
Defined.

Definition compare a b := 
(*
match a with
| top x | bot x => match b with 
  | bot y | top y => match Nat.compare x y with
    | Lt => Lt
    | Gt => Gt
    | Eq => match a,b with
      | top _, top _ => Eq
      | top _, bot _ => Gt
      | bot _, top _ => Lt
      | bot _, bot _ => Eq
      end
    end
  end
end.
*)
match a with
| top x => match b with 
  | bot y => match Nat.compare x y with
    | Lt => Lt
    | _ => Gt
    end
  | top y => Nat.compare x y
  end
| bot x => match b with 
  | bot y => Nat.compare x y
  | top y => match Nat.compare x y with
    | Gt => Gt
    | _ => Lt
    end
  end
end.

Lemma compare_spec : forall x y, CompSpec eq lt x y (compare x y).
Proof.
  intros; case_eq (compare x y); constructor.
  cut (compare x y = Eq).
  unfold compare.
  destruct x.
  destruct y.
  simpl.
  apply Compare_dec.nat_compare_eq.
  destruct (n ?= n0).
  discriminate.
  discriminate.
  discriminate.
  destruct y.
  destruct (n ?= n0).
  discriminate.
  discriminate.
  discriminate.
  simpl.
  apply Compare_dec.nat_compare_eq.
  exact H.

  cut (compare x y = Lt).
  unfold compare.
  destruct x.
  destruct y.
  simpl.
  apply Compare_dec.nat_compare_Lt_lt.
  simpl.
  cut ((n ?= n0) = Lt \/ (n ?= n0) = Eq \/ (n ?= n0)= Gt).
  intro.
  destruct H0.
  rewrite H0.
  intro.
  apply Compare_dec.nat_compare_Lt_lt in H0.
  exact H0.
  destruct H0.
  rewrite H0.
  discriminate.
  rewrite H0.
  discriminate.
  destruct (n ?= n0).
  auto.
  auto.
  auto.
  destruct y.
  simpl.
  cut ((n ?= n0) = Lt \/ (n ?= n0) = Eq \/ (n ?= n0)= Gt).
  intro.
  destruct H0.
  rewrite H0.
  intro.
  left.
  apply Compare_dec.nat_compare_Lt_lt in H0.
  exact H0.
  destruct H0.
  rewrite H0.
  intro.
  right.
  apply Compare_dec.nat_compare_eq in H0.
  exact H0.
  rewrite H0.
  discriminate.
  destruct (n ?= n0).
  auto.
  auto.
  auto.
  simpl.
  apply Compare_dec.nat_compare_Lt_lt.
  exact H.
  cut (compare x y = Gt).
  unfold compare.
  destruct x.
  destruct y.
  simpl.
  apply Compare_dec.nat_compare_Gt_gt.
  simpl.
  cut ((n ?= n0) = Lt \/ (n ?= n0) = Eq \/ (n ?= n0)= Gt).
  intro.
  destruct H0.
  rewrite H0.
  discriminate.
  destruct H0.
  rewrite H0.
  intro.
  right.
  symmetry.
  apply Compare_dec.nat_compare_eq in H0.
  exact H0.
  rewrite H0.
  intro.
  left.
  apply Compare_dec.nat_compare_Gt_gt in H0.
  exact H0.
  destruct (n ?= n0).
  auto.
  auto.
  auto.
  destruct y.
  simpl.
  cut ((n ?= n0) = Lt \/ (n ?= n0) = Eq \/ (n ?= n0)= Gt).
  intro.
  destruct H0.
  rewrite H0.
  discriminate.
  destruct H0.
  rewrite H0.
  discriminate.
  rewrite H0.
  intro.
  apply Compare_dec.nat_compare_Gt_gt in H0.
  exact H0.
  destruct (n ?= n0).
  auto.
  auto.
  auto.
  simpl.
  apply Compare_dec.nat_compare_Gt_gt.
  exact H.
Defined.

Lemma eq_dec : forall n m : literal, sumbool (eq n m) (~eq n m).
Proof.
  intro;intro.
  destruct n.
  destruct m.
  simpl.
  apply Peano_dec.eq_nat_dec.
  simpl.
  auto.
  destruct m.
  auto.
  simpl.
  apply Peano_dec.eq_nat_dec.
Defined.

Lemma eq_leibniz : forall n m : literal, (eq n m) -> (n = m).
Proof.
  intros.
  destruct n.
  destruct m.
  elim H.
  auto.
  elim H.
  destruct m.
  elim H.
  auto.
Defined.
End OWL.

Import OWL.

Module Clause := MakeWithLeibniz OWL.
Import Clause.

Module ClauseProp := MSetProperties.WPropertiesOn OWL Clause.
Import ClauseProp.

Module CNF := MakeWithLeibniz Clause.
Import CNF.

Module CNFProp := MSetProperties.WPropertiesOn Clause CNF.
Import CNFProp.

Module Nat_as_OT_Leibniz <: Orders.OrderedType.

Definition t := nat.

Definition eq := Nat_as_OT.eq.

Definition eq_equiv := Nat_as_OT.eq_equiv.

Definition lt := Peano.lt.

Definition lt_strorder := Nat_as_OT.lt_strorder.

Definition lt_compat := Nat_as_OT.lt_wd.

Definition compare x y : comparison := Nat_as_OT.compare x y.

Definition compare_spec := Nat_as_OT.compare_spec.

Definition eq_dec := Nat_as_OT.eq_dec.

Lemma eq_leibniz : forall n m : nat, (eq n m) -> (n = m).
  intros.
  auto.
Qed.

End Nat_as_OT_Leibniz.

Module NatSet := MakeWithLeibniz Nat_as_OT_Leibniz.
Import NatSet.

Module NatSetProp := MSetProperties.WPropertiesOn Nat_as_OT_Leibniz NatSet.

Import NatSetProp.
From EnumXP Require Export FeatureProperties.
From EnumXP Require Export CorrectFindXp.

Open Scope list_scope.

Lemma contrapose : forall p q:Prop, (p->q)->(~q->~p).
Proof. intros. intro. apply H0. apply H. exact H1. Qed.

Definition valid_set s := NatSet.For_all (gt nb_feature) s.

Definition valid_index (lit:literal) : Prop :=
match lit with
| bot x => gt nb_feature x
| top x => gt nb_feature x
end.

Definition valid_clause c := Clause.For_all (valid_index) c.

Definition valid_CNF c := CNF.For_all valid_clause c.

(* SAT axioms *)

Definition clause_satis (c:Clause.t) (s:NatSet.t) : Prop :=
exists (e:nat), (Clause.In (top e) c /\ NatSet.In e s) \/ (Clause.In (bot e) c /\ ~NatSet.In e s).

Definition sat_satis (sat:CNF.t -> option NatSet.t) : Prop :=
forall (p:CNF.t) (r:option NatSet.t), (sat p) = r ->
  (exists (s0:NatSet.t), r = Some s0 /\ (forall (c:Clause.t), CNF.In c p -> clause_satis c s0))
\/ (r = None /\ (forall (s:NatSet.t), exists (c0:Clause.t), CNF.In c0 p /\ ~clause_satis c0 s)).

Definition sat_index_bound (sat:CNF.t -> option NatSet.t) : Prop :=
forall (p:CNF.t) (r:NatSet.t), (Some r) = (sat p) ->
(valid_CNF p) -> (valid_set r).

Definition sat_correct (sat:CNF.t -> option NatSet.t) : Prop :=
sat_satis sat /\ sat_index_bound sat.


Parameter findAXp: (list T -> Tk) -> (list T) -> NatSet.t -> NatSet.t.
Parameter findCXp: (list T -> Tk) -> (list T) -> NatSet.t -> NatSet.t.


(* a few usefull lemmas on NatSet.diff *)

Lemma subset_diff: forall (s1 s2 s:NatSet.t), 
NatSet.Subset s1 s ->
NatSet.Subset s2 s ->
NatSet.Subset (NatSet.diff s s1) (NatSet.diff s s2)
-> NatSet.Subset s2 s1.
Proof.
  intros.
  unfold NatSet.Subset.
  intros.
  unfold NatSet.Subset in H.
  specialize H with (a:=a).
  unfold NatSet.Subset in H0.
  specialize H0 with (a:=a).
  unfold NatSet.Subset in H1.
  specialize H1 with (a:=a).
  apply contrapose in H1.
  pose proof NatSet.diff_spec.
  specialize H3 with (s:=s) (s':=s1) (x:=a).
  apply Logic.not_iff_compat in H3.
  apply H3 in H1.
  apply Logic.Classical_Prop.not_and_or in H1.
  destruct H1.
  apply H0 in H2.
  absurd (NatSet.In a s).
  exact H1.
  exact H2.
  apply Logic.Classical_Prop.NNPP in H1.
  exact H1.
  intro.
  apply NatSet.diff_spec in H3.
  destruct H3.
  absurd (NatSet.In a s2).
  exact H4.
  exact H2.
Qed.

Lemma diff_diff: forall (s1 s2:NatSet.t), 
NatSet.Subset s1 s2 ->
NatSet.Equal (NatSet.diff s2 (NatSet.diff s2 s1)) s1.
Proof.
  intros.
  unfold NatSet.Equal.
  intros.
  split.
  intro.
  apply NatSet.diff_spec in H0.
  destruct H0.
  pose proof NatSet.diff_spec.
  specialize H2 with (s:=s2) (s':=s1) (x:=a).
  destruct H2.
  apply contrapose in H3.
  apply Logic.Classical_Prop.not_and_or in H3.
  destruct H3.
  absurd (NatSet.In a s2).
  exact H3.
  exact H0.
  apply Logic.Classical_Prop.NNPP in H3.
  exact H3.
  exact H1.
  intros.
  apply NatSet.diff_spec.
  split.
  pose proof NatSetProp.in_subset.
  specialize H1 with (s1:=s1) (s2:=s2) (x:=a).
  apply H1.
  exact H0.
  exact H.
  intro.
  apply NatSet.diff_spec in H1.
  destruct H1.
  absurd (NatSet.In a s1).
  exact H2.
  exact H0.
Qed.

Lemma inter_diff_empty : forall (s1 s2 s3: NatSet.t),
NatSet.Subset s1 s3 ->
NatSet.Subset s2 s3 ->
NatSet.Empty (NatSet.inter s1 (NatSet.diff s3 s2)) ->
NatSet.Subset s1 s2.
Proof.
  intros.
  unfold NatSet.Subset.
  intros.
  unfold NatSet.Empty in H1.
  pose proof NatSet.inter_spec.
  specialize H3 with (s:=s1) (s':=(diff s3 s2)) (x:=a).
  destruct H3.
  apply contrapose in H4.
  apply Logic.Classical_Prop.not_and_or in H4.
  destruct H4.
  absurd (In a s1).
  exact H4.
  exact H2.
  pose proof NatSet.diff_spec.
  specialize H5 with (s:=s3) (s':=s2) (x:=a).
  destruct H5.
  apply contrapose in H6.
  apply Logic.Classical_Prop.not_and_or in H6.
  destruct H6.
  pose proof NatSetProp.in_subset.
  specialize H7 with (s1:=s1) (s2:=s3) (x:=a).
  apply H7 in H2.
  absurd (NatSet.In a s3).
  exact H6.
  exact H2.
  exact H.
  apply Logic.Classical_Prop.NNPP in H6.
  exact H6.
  exact H4.
  apply H1.
Qed.

Lemma in_diff : forall (s1 s2 : NatSet.t) (i : nat),
In i s1 /\ In i (diff s1 s2) -> ~ In i s2.
Proof.
  intros.
  destruct H.
  unfold not.
  intro.
  pose proof (diff_inter_empty s1 s2).
  unfold Equal in H2.
  specialize H2 with (a:= i).
  destruct H2.
  cut (In i empty).
  intro r.
  inversion r.
  apply H2.
  apply inter_spec.
  split.
  exact H0.
  apply inter_spec.
  split.
  exact H.
  exact H1.
Qed.

Lemma not_in_diff : forall (s1 s2 : NatSet.t) (i : nat),
In i s1 /\ ~ In i (diff s1 s2) -> In i s2.
Proof.
  intros.
  destruct H.
  rewrite diff_spec in H0.
  apply Logic.Classical_Prop.not_and_or in H0.
  destruct H0.
  tauto.
  tauto.
Qed.


Function build_vl_vu_aux (i:nat) (v: list T) (p : NatSet.t) (f:nat->T): list T :=
  match v with
  | nil => v
  | h::q => if NatSet.mem i p then ((f i)::(build_vl_vu_aux (S i) q p f)) else (h::(build_vl_vu_aux (S i) q p f)) 
  end.

Definition build_vl_vu (v: list T) (p : NatSet.t) : (list T)*(list T) :=
(build_vl_vu_aux 0 v p lambda, build_vl_vu_aux 0 v p nu).


Lemma length_build_vl_vu_aux : forall (v : list T) (i:nat) (p : NatSet.t) (f:nat->T) , 
 length (build_vl_vu_aux i v p f) = length v.
Proof.
  induction v.
  (* cas de base *)
  simpl.
  intros.
  reflexivity.
  (* cas général *)
  simpl.
  intros.
  destruct (NatSet.mem i p).
  simpl.
  f_equal.
  specialize IHv with  (i:=(S i)) (p:=p) (f:=f).
  apply IHv.
  simpl.
  f_equal.
  specialize IHv with (i:=(S i)) (p:=p) (f:=f).
  apply IHv.
Qed.

Lemma length_build_vl_vu : forall (v vl vu: list T) (p : NatSet.t), (vl,vu)=build_vl_vu v p 
-> (length vl = length v /\ length vu = length v).
Proof.
  intros.
  unfold build_vl_vu in H.
  inversion H.
  split.
  apply length_build_vl_vu_aux.
  apply length_build_vl_vu_aux.
Qed.

Definition is_bounded_aux (v : list T) (i:nat) : Prop :=
forall (j:nat), j>=0 /\ j< length v -> 
 led (lambda (j+i)) (get j v) /\ led (get j v) (nu (j+i)).


Lemma Induction_is_bounded_aux : forall (a:T) (v : list T) (i:nat),
is_bounded_aux (a::v) i <-> (led (lambda i) a /\ led a (nu i)) /\ is_bounded_aux v (S i).
Proof.
  intros.
  split.
    (* -> *)
    unfold is_bounded_aux.
    intros.
    split.
    (* Tête *)
    specialize H with (j:=0).
    apply H.
    split.
    lia.
    simpl.
    lia.
    (* Queue *)
    intros.
    specialize H with (j:= (S j)).
    cut (S j + i = j + S i).
    intro arth.
    rewrite <- arth.
    cut (get (S j) (a :: v) = get j v).
    intro rget.
    rewrite <- rget.
    apply H.
    split.
    lia.
    simpl.
    lia.
    (* get (S j) (a :: v) = get j v *)
    unfold get.
    simpl.
    reflexivity.
    (* S j + i = j + S i *)
    lia.

    (* <- *)
    intros.
    destruct H as (HTete, HQueue).
    unfold is_bounded_aux.
    intros.
    destruct j.
      (* j=0 *)
      unfold get.
      simpl.
      exact HTete.
      (* j<> 0 *)
      unfold is_bounded_aux in HQueue.
      specialize HQueue with (j:= j).
      cut (S j + i = j + S i).
      intro arth.
      rewrite arth.
      cut (get (S j) (a :: v) = get j v).
      intro rget.
      rewrite rget.
      apply HQueue.
      split.
      lia.
      simpl.
      destruct H.
      generalize H0.
      simpl.
      lia.
      (* get (S j) (a :: v) = get j v *)
      unfold get.
      simpl.
      reflexivity.
      (* S j + i = j + S i *)
      lia.
Qed.

Lemma is_bounded_aux_is_bounded :  forall (v : list T),
is_bounded_aux v 0 <-> is_bounded v.
Proof.
  intros.
  split.
  (* -> *)
  unfold is_bounded_aux.
  unfold is_bounded.
  intros.
  specialize H with (j:=j).
  cut (j+0 = j).
  intro r.
  rewrite r in H.
  apply H.
  exact H0.
  lia.
  (* <- *)
  unfold is_bounded_aux.
  unfold is_bounded.
  intros.
  specialize H with (j:=j).
  cut (j+0 = j).
  intro r.
  rewrite r.
  apply H.
  exact H0.
  lia.
Qed.


Lemma bounded_build_vl_vu_aux : forall  (v : list T) (i:nat) (p : NatSet.t) (f:nat->T) , 
is_bounded_aux v i
-> is_bounded_aux (build_vl_vu_aux i v p lambda) i /\ is_bounded_aux (build_vl_vu_aux i v p nu) i.
Proof.    
  induction v.
  (* cas de base *)
  simpl.
  intros.
  split.
  exact H.
  exact H.
  (* cas général *)
  intros.
  simpl.
  destruct (NatSet.mem i p).
  (* cas 1 *)
  specialize IHv with (i:=(S i)) (p:=p).
  split.
  apply Induction_is_bounded_aux.
  split.
  split.
  apply led_eq.
  reflexivity.
  apply (led_transitivity (lambda i) a (nu i)).
  rewrite Induction_is_bounded_aux in H.
  apply H.
  apply IHv.
  exact f.
  rewrite Induction_is_bounded_aux in H.
  apply H.
  apply Induction_is_bounded_aux.
  split.
  split.
  apply (led_transitivity (lambda i) a (nu i)).
  rewrite Induction_is_bounded_aux in H.
  apply H.
  apply led_eq.
  reflexivity.
  apply IHv.
  exact f.
  rewrite Induction_is_bounded_aux in H.
  apply H.
  (* cas 2 *)
  specialize IHv with (i:=(S i)) (p:=p).
  split.
  apply Induction_is_bounded_aux.
  split.
  rewrite Induction_is_bounded_aux in H.
  apply H.
  apply IHv.
  exact f.
  rewrite Induction_is_bounded_aux in H.
  apply H.
  apply Induction_is_bounded_aux.
  split.
  rewrite Induction_is_bounded_aux in H.
  apply H.
  apply IHv.
  exact f.
  rewrite Induction_is_bounded_aux in H.
  apply H.
Qed.


Lemma bounded_build_vl_vu : forall (v vl vu: list T) (p : NatSet.t), 
is_bounded v
/\ (vl,vu)=build_vl_vu v p 
-> is_bounded vu /\ is_bounded vl.
Proof.
  intros.
  unfold build_vl_vu in H.
  destruct H as (bv, def_vl_vu).
  inversion def_vl_vu.
  split.
  apply is_bounded_aux_is_bounded.
  apply bounded_build_vl_vu_aux.
  exact lambda.
  apply is_bounded_aux_is_bounded.
  exact bv.
  apply is_bounded_aux_is_bounded.
  apply bounded_build_vl_vu_aux.
  exact lambda.
  apply is_bounded_aux_is_bounded.
  exact bv.
Qed.


Lemma get_in_p_build_vl_vu_aux : forall  (v : list T) (i:nat) (p : NatSet.t) (f:nat->T) (j: nat), 
 j>=0 /\ j <length v ->
 (
  (NatSet.In (i+j) p -> get j (build_vl_vu_aux i v p f) = f (i+j) )
  /\
  (~NatSet.In (i+j) p -> get j (build_vl_vu_aux i v p f) = get j v )
 ).
 Proof.
  induction v.
  (* cas de base *)
  intros.
  generalize H.
  simpl.
  lia.
  (* cas general *)
  intros.
  simpl.
  split.
  (* In (i + j) p  *)
    intro.
    destruct j.
      (* j = 0*)
      cut (NatSet.mem i p = true).
      intro rmem.
      rewrite rmem.
      unfold get.
      simpl.
      cut (i+0=i).
      intro r.
      rewrite r.
      reflexivity.
      lia.
        (* mem i p = true *)
        generalize H0.
        cut (i+0=i).
        intro r.
        rewrite r.
        apply mem_spec.
        lia.
      (* j <> 0 *)
      specialize IHv with (i:= S i) (p:=p) (f:=f) (j:=j).
      destruct IHv.
      split.
      lia.
      destruct H.
      generalize H1.
      simpl.
      lia.
      destruct (NatSet.mem i p).
        (* mem i p *)
        cut (i + S j = S i + j).
        intro r.
        rewrite r.
        apply H1.
        rewrite <- r.
        exact H0.
        lia.
        (* ~ mem i p *)
        cut (i + S j = S i + j).
        intro r.
        rewrite r.
        apply H1.
        rewrite <- r.
        exact H0.
        lia.
  (* ~ In (i + j) p  *)
    intro.
    destruct j.
      (* j = 0*)
      cut (NatSet.mem i p = false).
      intro rmem.
      rewrite rmem.
      unfold get.
      simpl.
      reflexivity.
        (* mem i p = true *)
        generalize H0.
        cut (i+0=i).
        intro r.
        rewrite r.
        pose proof mem_spec.
        specialize H1 with (s:=p) (x:=i).
        intros.
        destruct (NatSet.mem i p).
        tauto.
        reflexivity.
        lia.
      (* j <> 0 *)
      specialize IHv with (i:= S i) (p:=p) (f:=f) (j:=j).
      destruct IHv.
      split.
      lia.
      destruct H.
      generalize H1.
      simpl.
      lia.
      destruct (NatSet.mem i p).
        (* mem i p *)
        simpl.
        apply H2.
        cut (i + S j = S i + j).
        intro r.
        rewrite <- r.
        exact H0.
        lia.
        (* ~ mem i p *)
        simpl.
        apply H2.
        cut (i + S j = S i + j).
        intro r.
        rewrite <- r.
        exact H0.
        lia.
Qed.

Lemma get_in_p_build_vl_vu : forall (v vl vu: list T) (p : NatSet.t) (j:nat), 
 j>=0 /\ j <length v /\ (vl,vu)=build_vl_vu v p ->
 (
  (NatSet.In j p -> get j vl = lambda j /\ get j vu = nu j)
  /\
  (~NatSet.In j p -> get j vl = get j v /\ get j vu = get j v)
 ).
 Proof.
  intros.
  unfold build_vl_vu in H.
  destruct H as (jpos, H).
  destruct H as (jinf, def_vl_vu).
  inversion def_vl_vu.
  split.
  intro.
  split.
  pose proof  (get_in_p_build_vl_vu_aux v 0 p lambda j).
  destruct H2.
  split. exact jpos. exact jinf.
  cut (0+j=j).
  intro r.
  rewrite r in H2.
  apply H2.
  exact H.
  lia.
  pose proof  (get_in_p_build_vl_vu_aux v 0 p nu j).
  destruct H2.
  split. exact jpos. exact jinf.
  cut (0+j=j).
  intro r.
  rewrite r in H2.
  apply H2.
  exact H.
  lia.
  intro.
  split.
  pose proof  (get_in_p_build_vl_vu_aux v 0 p lambda j).
  destruct H2.
  split. exact jpos. exact jinf.
  cut (0+j=j).
  intro r.
  rewrite r in H3.
  apply H3.
  exact H.
  lia.
  pose proof  (get_in_p_build_vl_vu_aux v 0 p nu j).
  destruct H2.
  split. exact jpos. exact jinf.
  cut (0+j=j).
  intro r.
  rewrite r in H3.
  apply H3.
  exact H.
  lia.
 Qed.


Inductive Xp : Type :=
  | AXp : NatSet.t -> Xp
  | CXp : NatSet.t -> Xp.

Function featureSet_aux (i:nat) (s : NatSet.t): NatSet.t := 
match i with
| O => NatSet.empty
| S i => NatSet.add i (featureSet_aux i s)
end.

Definition featureSet : NatSet.t := featureSet_aux nb_feature NatSet.empty.

Lemma featureSet_aux_prop1 : forall (n i:nat), i < n -> NatSet.In i (featureSet_aux n NatSet.empty).
Proof.
  intros.
  functional induction (featureSet_aux (n) NatSet.empty) using featureSet_aux_ind.
  lia.
  cut (i=i1 \/ i<i1).
  intro.
  destruct H0.
  apply NatSet.add_spec.
  left.
  exact H0.
  apply NatSet.add_spec.
  right.
  apply IHt1.
  exact H0.
  lia.
Qed.

Lemma featureSet_aux_prop2 : forall (n i:nat), NatSet.In i (featureSet_aux n NatSet.empty) -> i < n.
Proof.
  intros.
  functional induction (featureSet_aux (n) NatSet.empty) using featureSet_aux_ind.
  apply NatSet.empty_spec in H.
  elim H.
  apply NatSet.add_spec in H.
  destruct H.
  rewrite H.
  lia.
  apply IHt1 in H.
  lia.
Qed.

Lemma valid_set_in_featureSet : forall (s:NatSet.t),
valid_set s <-> NatSet.Subset s featureSet.
Proof.
  intros.
  split.
  unfold NatSet.Subset.
  intros.
  unfold valid_set in H.
  unfold NatSet.For_all in H.
  apply H in H0.
  unfold featureSet.
  apply featureSet_aux_prop1.
  lia.
  intro.
  unfold NatSet.Subset in H.
  unfold featureSet in H.
  unfold valid_set.
  unfold NatSet.For_all.
  intros.
  apply H in H0.
  apply featureSet_aux_prop2 in H0.
  lia.
Qed.

Lemma in_valid_set_in_featureSet : forall (i:nat),
0 <= i < nb_feature -> In i featureSet.
Proof.
  intros.
  unfold featureSet.
  apply featureSet_aux_prop1.
  lia.
Qed.

(* Problem specific definitions *)

Definition stable (k:list T -> Tk): Prop := forall (f1:list T) (f2:list T) (x:list T), 
   List.length f1 = nb_feature 
/\ List.length f2 = nb_feature
/\ List.length x = nb_feature
/\ is_bounded f1
/\ is_bounded f2
/\ is_bounded x
/\ le_n f1 x /\ le_n x f2 /\ (k f1)=(k f2)-> (k f1)=(k x).

(* Need for CXp but not for AXp *)
Definition not_trivial (k:list T -> Tk): Prop := exists (f1:list T) (f2:list T), 
List.length f1 = nb_feature 
/\ List.length f2 = nb_feature
/\ is_bounded f1
/\ is_bounded f2
/\ (k f1)<>(k f2).

(* missing that it s!hould be the smallest set *)  
Definition is_weak_AXp (k : list T -> Tk) (v: list T) (p:NatSet.t) : Prop :=
   valid_set p
/\ forall (x: list T),
   List.length v = nb_feature
/\ List.length x = nb_feature
/\ is_bounded x
/\ (forall (j:nat), j>=0 /\ j< nb_feature -> ((NatSet.In j p /\ get j x = get j v) \/ (not (NatSet.In j p))))
 -> k(x)=k(v).

Definition is_AXp (k : list T -> Tk) (v: list T) (p:NatSet.t) : Prop :=
   is_weak_AXp k v p (* satisfy the constraint *)
/\ forall (q:NatSet.t), (NatSet.Subset q p) -> NatSet.Equal q p \/ not (is_weak_AXp k v q) (* all subset do not satisfy the constraint *).

(*
Definition eq_free_s (k : list T -> Tk) (v:list T) (s :NatSet.t) : Prop :=
    forall (vl:list T) (vu: list T),
    (
    length vu = nb_feature
    /\
    length vl = nb_feature
    /\
    (forall  (j:nat), j>=0 /\ j< nb_feature -> 
      (NatSet.In j s -> get j vu = nu j /\ get j vl = lambda j)
      /\
      (not (NatSet.In j s) -> get j vu = get j v /\ get j vl = get j v)
    )
    )
    -> (k vl) = (k vu).
  *)

Definition is_seeded_AXp (k : list T -> Tk) (v: list T) (s p:NatSet.t) : Prop :=
   valid_set s (* s in P(F) *)
/\ NatSet.Subset p (NatSet.diff featureSet s) (* AXp in F\s *)
/\ is_AXp k v p (* satisfy the constraint *).

Axiom correct_findAXp : forall (k : list T -> Tk) (v:list T) (s:NatSet.t),
   stable k
/\ is_weak_AXp k v (NatSet.diff featureSet s)
/\ length v = nb_feature
/\ is_bounded v
-> is_seeded_AXp k v s (findAXp k v s).

Lemma is_AXp_findAXp : forall (k : list T -> Tk) (v:list T) (s:NatSet.t),
   stable k
/\ is_weak_AXp k v (NatSet.diff featureSet s)
/\ length v = nb_feature
/\ is_bounded v
-> is_AXp k v (findAXp k v s).
Proof.
  intros.
  pose proof correct_findAXp. 
  specialize H0 with (k:=k) (v:=v) (s:=s).
  apply H0 in H.
  destruct H.
  destruct H1.
  exact H2.
Qed.

Lemma valid_set_findAXp : forall (k : list T -> Tk) (v:list T) (s:NatSet.t),
   stable k
/\ is_weak_AXp k v (NatSet.diff featureSet s)
/\ length v = nb_feature
/\ is_bounded v
-> valid_set (findAXp k v s).
Proof.
  intros.
  pose proof correct_findAXp.
  specialize H0 with (k:=k) (v:=v) (s:=s).
  apply H0 in H.
  destruct H.
  destruct H1.
  pose proof NatSetProp.subset_trans.
  specialize H3 with (s1:=(findAXp k v s)) (s2:=(diff featureSet s)) (s3:=featureSet).
  rewrite valid_set_in_featureSet.
  apply H3.
  exact H1.
  apply NatSetProp.subset_diff.
  apply NatSetProp.subset_refl.
Qed.

(* missing that it should be the smallest set *)  
Definition is_weak_CXp  (k : list T -> Tk) (v: list T) (p:NatSet.t) : Prop :=
   valid_set p (* p in P(F) *)
/\ exists (x: list T),
   List.length v = nb_feature
/\ List.length x = nb_feature
/\ is_bounded x 
/\ (forall (j:nat), j>=0 /\ j< nb_feature -> (((not (NatSet.In j p)) /\ get j x = get j v) \/  (NatSet.In j p)))
/\ not (k(x)=k(v)).

Definition is_CXp (k : list T -> Tk) (v: list T) (p:NatSet.t) : Prop :=
   is_weak_CXp k v p (* satisfy the constraint *)
/\ forall (q:NatSet.t), (NatSet.Subset q p) -> NatSet.Equal q p \/ not (is_weak_CXp k v q) (* all subset do not satisfy the constraint *).

Definition is_seeded_CXp (k : list T -> Tk) (v: list T) (s p:NatSet.t) : Prop :=
   valid_set s (* s in P(F) *)
/\ NatSet.Subset p (NatSet.diff featureSet s) (* CXp in F\s *)
/\ is_CXp k v p (* satisfy the constraint *).


Axiom correct_findCXp : forall (k : list T -> Tk) (v:list T) (s:NatSet.t),
   stable k
/\ not_trivial k
/\ is_weak_CXp k v (NatSet.diff featureSet s)
/\ length v = nb_feature
/\ is_bounded v
-> is_seeded_CXp k v s (findCXp k v s).

Lemma is_CXp_findCXp : forall (k : list T -> Tk) (v:list T) (s:NatSet.t),
   stable k
/\ not_trivial k
/\ is_weak_CXp k v (NatSet.diff featureSet s)
/\ length v = nb_feature
/\ is_bounded v
-> is_CXp k v (findCXp k v s).
Proof.
  intros.
  pose proof correct_findCXp. 
  specialize H0 with (k:=k) (v:=v) (s:=s).
  apply H0 in H.
  destruct H.
  destruct H1.
  exact H2.
Qed.

Lemma valid_set_findCXp : forall (k: list T -> Tk) (v:list T) (s:NatSet.t),
   stable k
/\ not_trivial k
/\ is_weak_CXp k v (NatSet.diff featureSet s)
/\ length v = nb_feature
/\ is_bounded v
-> valid_set (findCXp k v s).
Proof.
  intros.
  pose proof correct_findCXp.
  specialize H0 with (k:=k) (v:=v) (s:=s).
  apply H0 in H.
  destruct H.
  destruct H1.
  pose proof NatSetProp.subset_trans.
  specialize H3 with (s1:=(findCXp k v s)) (s2:=(diff featureSet s)) (s3:=featureSet).
  apply H3 in H1.
  apply valid_set_in_featureSet.
  exact H1.
  apply NatSetProp.subset_diff.
  apply NatSetProp.subset_refl.
Qed.

Lemma AXp_stability : forall (k: list T -> Tk) (v:list T) (s1 s2:NatSet.t),
is_AXp k v s1 ->
NatSet.Subset s1 s2 ->
valid_set s2 ->
is_weak_AXp k v s2.
Proof.
  intros.
  destruct H.
  destruct H.
  split.
  exact H1.
  intros.
  destruct H4.
  destruct H5.
  destruct H6.
  apply H3.
  split.
  exact H4.
  split.
  exact H5.
  split.
  exact H6.
  intros.
  apply H7 in H8.
  destruct H8.
  cut (In j s1 \/ ~ In j s1).
  intro.
  destruct H9.
  left.
  split.
  exact H9.
  destruct H8.
  exact H10.
  right.
  exact H9.
  tauto.
  cut (In j s1 \/ ~ In j s1).
  intro.
  destruct H9.
  pose proof NatSetProp.in_subset.
  specialize H10 with (s1:=s1) (s2:=s2) (x:=j).
  apply H10 in H9.
  absurd (In j s2).
  exact H8.
  exact H9.
  exact H0.
  right.
  exact H9.
  auto.
Qed.

Lemma weak_CXp_complement : forall (k : list T -> Tk) (v: list T) (p:NatSet.t),
is_weak_CXp k v p ->
   valid_set p
/\ exists (x: list T),
   List.length v = nb_feature
/\ List.length x = nb_feature
/\ is_bounded x
/\ (forall (j:nat), j>=0 /\ j< nb_feature -> 
((NatSet.In j (NatSet.diff featureSet p) /\ get j x = get j v) \/  ~(NatSet.In j (NatSet.diff featureSet p))))
/\ not (k(x)=k(v)).
Proof.
  intros.
  destruct H.
  split.
  exact H.
  destruct H0.
  exists x.
  destruct H0.
  split.
  exact H0.
  destruct H1.
  split.
  exact H1.
  destruct H2.
  split.
  exact H2.
  destruct H3.
  split.
  intros.
  specialize H3 with (j:=j).
  cut (j >= 0 /\ j < nb_feature).
  intro.
  apply H3 in H5.
  destruct H5.
  left.
  destruct H5.
  split.
  apply NatSet.diff_spec.
  split.
  destruct H6.
  apply featureSet_aux_prop1 in H8.
  unfold featureSet.
  exact H8.
  exact H5.
  exact H7.
  right.
  intro.
  apply NatSet.diff_spec in H7.
  destruct H7.
  absurd (NatSet.In j p).
  exact H8.
  exact H5.
  exact H5.
  exact H4.
Qed.

Lemma AXp_CXp_non_empty_inter: forall (k : list T -> Tk) (v: list T)(s1 s2: NatSet.t),
is_AXp k v s1 ->
is_CXp k v s2 ->
exists (x:nat), NatSet.In x (NatSet.inter s1 s2).
Proof.
  intros.
  destruct H0.
  apply weak_CXp_complement in H0.
  cut (~NatSet.Empty (NatSet.inter s1 s2) \/ NatSet.Empty (NatSet.inter s1 s2)).
  intro.
  destruct H2.
  unfold NatSet.Empty in H2.
  apply Logic.Classical_Pred_Type.not_all_ex_not in H2.
  destruct H2.
  apply Logic.Classical_Prop.NNPP in H2.
  exists x.
  exact H2.
  pose proof inter_diff_empty.
  specialize H3 with (s1:=s1) (s2:=(NatSet.diff featureSet s2)) (s3:=featureSet).
  cut (is_AXp k v s1).
  destruct H.
  destruct H.
  apply valid_set_in_featureSet in H.
  apply H3 in H.
  intro.
  pose proof AXp_stability.
  specialize H7 with (k:=k) (v:=v) (s1:=s1) (s2:=(NatSet.diff featureSet s2)).
  apply H7 in H6.
  destruct H6.
  destruct H0.
  destruct H9.
  destruct H9.
  destruct H10.
  destruct H11.
  destruct H12.
  specialize H8 with (x:=x).
  cut (length v = nb_feature /\
      length x = nb_feature /\
      is_bounded x /\
      (forall j : nat,
        j >= 0 /\ j < nb_feature ->
        In j (diff featureSet s2) /\ get j x = get j v \/ ~ In j (diff featureSet s2))).
  intro.
  apply H8 in H14.
  absurd (k x = k v).
  exact H13.
  exact H14.
  split.
  exact H9.
  split.
  exact H10.
  split.
  exact H11.
  exact H12.
  exact H.
  apply valid_set_in_featureSet.
  apply NatSetProp.diff_subset.
  apply NatSetProp.diff_subset.
  pose proof diff_diff.
  specialize H6 with (s1:=s2) (s2:=featureSet).
  destruct H0.
  apply valid_set_in_featureSet in H0.
  apply H6 in H0.
  apply NatSet.eq_leibniz in H0.
  rewrite H0.
  exact H2.
  exact H.
  tauto.
Qed.

Definition AXp2Clause (p:NatSet.t): Clause.t :=
  NatSet.fold (fun i acc => Clause.add (top i) acc) p Clause.empty.

Definition CXp2Clause (p:NatSet.t): Clause.t :=
  NatSet.fold (fun i acc => Clause.add (bot i) acc) p Clause.empty.

(* Terminaison *)

Lemma valid_CNF_incr : forall (h:CNF.t)(c:Clause.t), valid_CNF h -> valid_clause c -> valid_CNF (CNF.add c h).
Proof.
  intros.
  unfold valid_CNF.
  unfold CNF.For_all.
  intros.
  apply CNF.add_spec in H1.
  destruct H1.
  unfold Clause.Equal in H1.
  unfold valid_clause.
  unfold Clause.For_all.
  intro.
  specialize H1 with (a:=x0).
  rewrite H1.
  apply H0.
  apply H.
  exact H1.
Qed.

Lemma valid_clause_incr : forall (i:nat)(c:Clause.t),
(gt nb_feature i /\ valid_clause c) -> (valid_clause (Clause.add (top i) c) /\ valid_clause (Clause.add (bot i) c)).
Proof.
  intros.
  destruct H.
  unfold valid_clause.
  unfold Clause.For_all.
  split.
  intros.
  apply Clause.add_spec in H1.
  destruct H1.
  destruct x.
  unfold valid_index.
  rewrite H1.
  exact H.
  elim H1.
  unfold valid_clause in H0.
  unfold Clause.For_all in H0.
  specialize H0 with (x:=x).
  apply H0.
  exact H1.
  intros.
  apply Clause.add_spec in H1.
  destruct H1.
  destruct x.
  elim H1.
  unfold valid_index.
  rewrite H1.
  exact H.
  unfold valid_clause in H0.
  unfold Clause.For_all in H0.
  specialize H0 with (x:=x).
  apply H0.
  exact H1.
Qed.

Lemma valid_AXp2Clause : forall (p:NatSet.t), (valid_set p) -> (valid_clause (AXp2Clause p)).
Proof.
  intros.
  unfold AXp2Clause.
  apply NatSetProp.fold_rec_bis.
  intros.
  exact H1.
  unfold valid_clause.
  unfold Clause.For_all.
  intros.
  absurd (Clause.In x Clause.empty).
  apply Clause.empty_spec.
  exact H0.
  intros.
  unfold valid_set in H.
  unfold NatSet.For_all in H.
  specialize H with (x:=x).
  apply H in H0.
  apply valid_clause_incr.
  split.
  exact H0.
  exact H2.
Qed.

Lemma valid_CXp2Clause : forall (p:NatSet.t), (valid_set p) -> (valid_clause (CXp2Clause p)).
Proof.
  intros.
  unfold CXp2Clause.
  apply NatSetProp.fold_rec_bis.
  intros.
  exact H1.
  unfold valid_clause.
  unfold Clause.For_all.
  intros.
  absurd (Clause.In x Clause.empty).
  apply Clause.empty_spec.
  exact H0.
  intros.
  unfold valid_set in H.
  unfold NatSet.For_all in H.
  specialize H with (x:=x).
  apply H in H0.
  apply valid_clause_incr.
  split.
  exact H0.
  exact H2.
Qed.

Definition litSet : Clause.t := Clause.union (AXp2Clause featureSet) (CXp2Clause featureSet).

Lemma valid_top_aux : forall (n i:nat), i < n -> Clause.In (top i) (AXp2Clause (featureSet_aux n NatSet.empty)).
Proof.
  intros.
  induction n.
  easy.
  simpl.
  unfold AXp2Clause.
  pose proof NatSetProp.fold_add.
  specialize H0 with (eqA:= Clause.eq)
  (f:= fun (i0 : NatSet.elt) (acc : Clause.t) => Clause.add (top i0) acc)
  (s:= (featureSet_aux n NatSet.empty)) (i:=Clause.empty) (x:= n).
  apply H0.
  apply Clause.eq_equiv.
  split.
  rewrite H1.
  rewrite H2.
  auto.
  rewrite H1.
  rewrite H2.
  auto.
  split.
  apply ClauseProp.add_add.
  apply ClauseProp.add_add.
  pose proof featureSet_aux_prop2.
  specialize H1 with (n:=n) (i:=n).
  apply contrapose in H1.
  exact H1.
  lia.
  apply Clause.add_spec.
  cut ((i<n)\/(i=n)).
  intro.
  destruct H1.
  right.
  unfold AXp2Clause in IHn.
  apply IHn.
  exact H1.
  left.
  exact H1.
  lia.
Qed.

Lemma valid_bot_aux : forall (n i:nat), i < n -> Clause.In (bot i) (CXp2Clause (featureSet_aux n NatSet.empty)).
Proof.
  intros.
  induction n.
  easy.
  simpl.
  unfold CXp2Clause.
  pose proof NatSetProp.fold_add.
  specialize H0 with (eqA:= Clause.eq)
  (f:= fun (i0 : NatSet.elt) (acc : Clause.t) => Clause.add (bot i0) acc)
  (s:= (featureSet_aux n NatSet.empty)) (i:=Clause.empty) (x:= n).
  apply H0.
  apply Clause.eq_equiv.
  split.
  rewrite H1.
  rewrite H2.
  auto.
  rewrite H1.
  rewrite H2.
  auto.
  split.
  apply ClauseProp.add_add.
  apply ClauseProp.add_add.
  pose proof featureSet_aux_prop2.
  specialize H1 with (n:=n) (i:=n).
  apply contrapose in H1.
  exact H1.
  lia.
  apply Clause.add_spec.
  cut ((i<n)\/(i=n)).
  intro.
  destruct H1.
  right.
  unfold CXp2Clause in IHn.
  apply IHn.
  exact H1.
  left.
  exact H1.
  lia.
Qed.

Lemma valid_lit_set : forall (lit:literal), valid_index lit -> Clause.In lit litSet.
Proof.
  intros.
  unfold valid_index in H.
  destruct lit.
  unfold litSet.
  apply Clause.union_spec.
  left.
  apply valid_top_aux.
  lia.
  unfold litSet.
  apply Clause.union_spec.
  right.
  apply valid_bot_aux.
  lia.
Qed.

Definition clauseSet_aux (lit:literal) (h:CNF.t) : CNF.t := 
  CNF.fold (fun c acc => CNF.add (Clause.add lit c) acc) h CNF.empty.

Definition clauseSet_aux2 (litset: Clause.t) : CNF.t := 
  Clause.fold (fun l acc => CNF.union (clauseSet_aux l acc) acc) litset (CNF.singleton (Clause.empty)).

Definition clauseSet : CNF.t := 
  Clause.fold (fun l acc => CNF.union (clauseSet_aux l acc) acc) litSet (CNF.singleton (Clause.empty)).

Lemma clauseSet_aux_lemma : forall (c:Clause.t) (lit:literal) (h:CNF.t),
CNF.In c (clauseSet_aux lit h) -> Clause.In lit c.
Proof.
  intros.
  unfold clauseSet_aux in H.
  pose proof CNFProp.fold_rec_nodep.
  specialize X with (A:=CNF.t) (i:=CNF.empty) (P:=(CNF.For_all (Clause.In lit)))
  (f:=(fun (c : CNF.elt) (acc : CNF.t) => CNF.add (Clause.add lit c) acc)).
  apply X in H.
  exact H.
  unfold CNF.For_all.
  intros.
  apply CNF.empty_spec in H0.
  easy.
  intros.
  unfold CNF.For_all.
  intros.
  apply CNF.add_spec in H2.
  destruct H2.
  rewrite H2.
  apply Clause.add_spec.
  left.
  fold (OWL.eq lit lit).
  reflexivity.
  unfold CNF.For_all in H1.
  apply H1.
  exact H2.
Qed.

Lemma In_clause : forall (lit: literal) (a b: Clause.t),
~ Clause.In lit a /\ ~ Clause.In lit b /\ Clause.Equal (Clause.add lit a) (Clause.add lit b) 
-> Clause.Equal a b.
Proof.
  intros.
  destruct H.
  destruct H0.
  unfold Clause.Equal in H1.
  unfold Clause.Equal.
  intros.
  cut (a0=lit \/ a0 <> lit).
  intro.
  destruct H2.
  rewrite H2.
  split.
  intro.
  absurd (Clause.In lit a).
  exact H.
  exact H3.
  intro.
  absurd (Clause.In lit b).
  exact H0.
  exact H3.
  split.
  intro.
  cut (OWL.eq a0 lit \/ Clause.In a0 a).
  intro.
  apply Clause.add_spec in H4.
  apply H1 in H4.
  apply Clause.add_spec in H4.
  destruct H4.
  absurd (a0 = lit).
  exact H2.
  apply OWL.eq_leibniz in H4.
  exact H4.
  exact H4.
  right.
  exact H3.
  intro.

  cut (OWL.eq a0 lit \/ Clause.In a0 b).
  intro.
  apply Clause.add_spec in H4.
  apply H1 in H4.
  apply Clause.add_spec in H4.
  destruct H4.
  absurd (a0 = lit).
  exact H2.
  apply OWL.eq_leibniz in H4.
  exact H4.
  exact H4.
  right.
  exact H3.
  apply Logic.Classical_Prop.classic.
Qed.

Lemma clauseSet_aux_lemma2 : forall (c:Clause.t) (lit:literal) (h:CNF.t),
~(Clause.In lit c) -> CNF.In (Clause.add lit c) (clauseSet_aux lit h) -> ~CNF.In (Clause.add lit c) h -> CNF.In c h.
Proof.
  intros.
  pose proof CNFProp.set_induction.
  specialize X with (s:=h).
  specialize X with (P:= fun a => CNF.In (Clause.add lit c) (clauseSet_aux lit a) -> ~CNF.In (Clause.add lit c) a -> CNF.In c a).
  apply X.
  clear X.
  intros.
  unfold clauseSet_aux in H3.
  pose proof CNFProp.fold_1b.
  specialize H5 with (A:=CNF.t) (s:=s) (i:=CNF.empty) 
  (f:=fun (c : CNF.elt) (acc : CNF.t) => CNF.add (Clause.add lit c) acc).
  apply H5 in H2.
  rewrite H2 in H3.
  apply CNF.empty_spec in H3.
  easy.
  clear X.
  intros.
  apply CNFProp.Add_Equal in H4.
  apply CNF.eq_leibniz in H4.
  rewrite H4 in H5. 
  unfold clauseSet_aux in H5.
  pose proof CNFProp.fold_add.
  specialize H7 with (A:=CNF.t) (eqA:=CNF.eq)
  (f:= fun (c : CNF.elt) (acc : CNF.t) => CNF.add (Clause.add lit c) acc).
  apply H7 in H5.
  fold (clauseSet_aux lit s) in H5.
  clear H7.
  apply CNF.add_spec in H5.
  pose proof CNF.add_spec.
  specialize H7 with (x:=x) (y:=(Clause.add lit c)) (s:=s).
  apply Logic.not_iff_compat in H7.
  rewrite H4 in H6.
  apply H7 in H6.
  apply Logic.Classical_Prop.not_or_and in H6.
  destruct H6.
  clear H7.
  destruct H5.
  rewrite H4.
  apply CNF.add_spec.
  left.
  pose proof In_clause.
  specialize H7 with (lit:=lit).
  apply H7.
  split.
  exact H.
  split.
  apply Clause.eq_leibniz in H5.
  rewrite H5 in H6.
  cut (Clause.In lit x -> Clause.Equal (Clause.add lit x) x).
  intro.
  apply contrapose in H9.
  exact H9.
  exact H6.
  apply ClauseProp.add_equal.
  exact H5.
  rewrite H4.
  apply CNF.add_spec.
  right.
  apply H2.
  exact H5.
  exact H8.
  apply CNF.eq_equiv.
  split.
  apply Clause.eq_leibniz in H9.
  apply CNF.eq_leibniz in H10.
  rewrite H9.
  rewrite H10.
  tauto.
  apply Clause.eq_leibniz in H9.
  apply CNF.eq_leibniz in H10.
  rewrite H9.
  rewrite H10.
  tauto.
  split.
  apply CNFProp.add_add.
  apply CNFProp.add_add.
  exact H3.
  exact H0.
  exact H1.
Qed.


Lemma clauseSet_aux_lemma3 : forall (c:Clause.t) (lit:literal) (h:CNF.t),
CNF.In c (CNF.union (clauseSet_aux lit h) h)-> CNF.In (Clause.remove lit c) h \/ CNF.In c h.
Proof.
  intros.
  cut (~ Clause.In lit c \/ Clause.In lit c).
  intro.
  destruct H0.
  cut (~ Clause.In lit c).
  intro.
  left.
  apply ClauseProp.remove_equal in H0.
  rewrite H0.
  apply ClauseProp.equal_sym in H0.
  pose proof clauseSet_aux_lemma.
  specialize H2 with (c:=c) (lit:=lit) (h:=h).
  apply contrapose in H2.
  apply CNF.union_spec in H.
  destruct H.
  absurd (CNF.In c (clauseSet_aux lit h)).
  exact H2.
  exact H.
  exact H.
  exact H1.
  exact H0.
  cut (CNF.In (Clause.remove lit c) h \/ ~CNF.In (Clause.remove lit c) h).
  intro.
  destruct H1.
  left.
  exact H1.
  right.

  apply CNF.union_spec in H.
  destruct H.
  pose proof ClauseProp.add_remove.
  specialize H2 with (x:=lit) (s:=c).
  apply H2 in H0.

  pose proof clauseSet_aux_lemma2.
  specialize H3 with (c:=(Clause.remove lit c)) (lit:=lit) (h:=h).
  rewrite H0 in H3.
  pose proof Clause.remove_spec.
  specialize H4 with (s:=c) (y:=lit) (x:=lit).
  destruct H4.
  clear H5.
  fold (OWL.eq lit lit) in H4.
  cut ((~ CNF.In c h -> CNF.In (Clause.remove lit c) h) -> (CNF.In c h \/ CNF.In (Clause.remove lit c) h)).
  intro.
  apply H5 in H3.
  destruct H3.
  exact H3.
  absurd (CNF.In (Clause.remove lit c) h).
  exact H1.
  exact H3.
  intro.
  apply Clause.remove_spec in H6.
  destruct H6.
  fold (OWL.eq lit lit) in H7.
  elim H7.
  reflexivity.
  exact H.
  tauto.
  exact H.
  tauto.
  tauto.
Qed.

Lemma clauseSet_aux_lemma4 : forall (a:CNF.t) (c:Clause.t) (lit:literal),
CNF.In c a -> CNF.In (Clause.add lit c) (clauseSet_aux lit a).
Proof.
  intros.
  unfold clauseSet_aux.
  pose proof CNFProp.fold_rec_bis.
  specialize X with (A:=CNF.t) (i:=CNF.empty) (s:=a)
  (P:=(fun a b => forall (c:Clause.t), CNF.In c a -> CNF.In (Clause.add lit c) b))
  (f:=(fun (c : CNF.elt) (acc : CNF.t) => CNF.add (Clause.add lit c) acc)).
  apply X.
  clear X.
  intros.
  apply CNFProp.equal_sym in H0.
  rewrite H0 in H2.
  apply H1.
  exact H2.
  clear X.
  intros.
  apply CNF.empty_spec in H0.
  easy.
  clear X.
  intros.
  apply CNF.add_spec.
  apply CNF.add_spec in H3.
  destruct H3.
  left.
  rewrite H3.
  reflexivity.
  apply H2 in H3.
  right.
  exact H3.
  exact H.
Qed.

Lemma remove_remove: forall (x y: literal) (c: Clause.t),
Clause.Equal (Clause.remove x (Clause.remove y c)) (Clause.remove y (Clause.remove x c)).
Proof.
  intros.
  unfold Clause.Equal.
  intros.
  split.
  intro.
  apply Clause.remove_spec in H.
  destruct H.
  apply Clause.remove_spec in H.
  destruct H.
  fold (OWL.eq a y) in H1.
  fold (OWL.eq a x) in H0.
  apply Clause.remove_spec.
  split.
  apply Clause.remove_spec.
  split.
  exact H.
  exact H0.
  exact H1.
  intro.
  apply Clause.remove_spec in H.
  destruct H.
  apply Clause.remove_spec in H.
  destruct H.
  fold (OWL.eq a x) in H1.
  fold (OWL.eq a y) in H0.
  apply Clause.remove_spec.
  split.
  apply Clause.remove_spec.
  split.
  exact H.
  exact H0.
  exact H1.
Qed.

Lemma clauseSet_aux_lemma5 : forall (h:CNF.t) (c:Clause.t) (lit:literal),
CNF.In (Clause.remove lit c) h ->  CNF.In c (CNF.union (clauseSet_aux lit h) h).
Proof.
  intros.
  cut (Clause.In lit c \/ ~Clause.In lit c).
  intro.
  apply CNF.union_spec.
  destruct H0.
  pose proof clauseSet_aux_lemma4.
  specialize H1 with (a:=h) (c:=(Clause.remove lit c)) (lit:=lit).
  apply H1 in H.
  apply ClauseProp.add_remove in H0.
  rewrite H0 in H.
  left.
  exact H.
  apply ClauseProp.remove_equal in H0.
  rewrite H0 in H.
  right.
  exact H.
  tauto.
Qed.

Lemma valid_clause_set_aux : forall (c s:Clause.t),
Clause.Subset c s -> CNF.In c (clauseSet_aux2 s).
Proof.
  intros.
  pose proof ClauseProp.set_induction_bis.
  specialize X with (s:=s).
  specialize X with (P:= fun a => forall (c':Clause.t), Clause.Subset c' a -> CNF.In c' (clauseSet_aux2 a)).
  apply X.
  intros.
  apply Clause.eq_leibniz in H0.
  rewrite H0 in H1.
  apply H1 in H2.
  exact H2.
  intro.
  unfold clauseSet_aux2.
  rewrite ClauseProp.fold_empty.
  intro.
  apply CNF.singleton_spec.
  pose proof ClauseProp.subset_empty.
  specialize H1 with (s:=c').
  apply ClauseProp.double_inclusion.
  split.
  exact H0.
  exact H1.
  intros.
  cut (~Clause.In x c' \/ Clause.In x c').
  intro.
  unfold clauseSet_aux2.
  pose proof ClauseProp.fold_add.
  specialize H4 with (A:=CNF.t) (eqA:=CNF.Equal) (i:=(CNF.singleton Clause.empty)) (x:=x) (s:=s0)
  (f:=(fun (l : Clause.elt) (acc : CNF.t) => CNF.union (clauseSet_aux l acc) acc)).
  apply CNF.eq_leibniz in H4.
  rewrite H4.
  destruct H3.
  apply CNF.union_spec.
  right.
  apply H1.
  unfold Clause.Subset.
  intros.
  unfold Clause.Subset in H2.
  cut (Clause.In a c').
  intro.
  apply H2 in H5.
  apply Clause.add_spec in H5.
  fold (OWL.eq a x) in H5.
  destruct H5.
  rewrite H5 in H6.
  absurd (Clause.In x c').
  exact H3.
  exact H6.
  exact H5.
  exact H5.
  apply CNF.union_spec.
  left.
  fold (clauseSet_aux2 s0).
  apply ClauseProp.add_remove in H3.
  apply ClauseProp.equal_sym in H3.
  rewrite H3.
  apply clauseSet_aux_lemma4.
  apply H1.
  unfold Clause.Subset.
  intros.
  apply Clause.remove_spec in H5.
  destruct H5.
  fold (OWL.eq a x) in H6.
  unfold Clause.Subset in H2.
  apply H2 in H5.
  apply Clause.add_spec in H5.
  fold (OWL.eq a x) in H5.
  destruct H5.
  absurd (OWL.eq a x).
  exact H6.
  exact H5.
  exact H5.

  apply CNF.eq_equiv.
  split.
  fold (OWL.eq x0 y) in H5.
  apply OWL.eq_leibniz in H5.
  apply CNF.eq_leibniz in H6.
  rewrite H5.
  rewrite H6.
  tauto.
  fold (OWL.eq x0 y) in H5.
  apply OWL.eq_leibniz in H5.
  apply CNF.eq_leibniz in H6.
  rewrite H5.
  rewrite H6.
  tauto.
  split.
  intro.
  apply clauseSet_aux_lemma3 in H5.
  destruct H5.
  apply clauseSet_aux_lemma3 in H5.
  destruct H5.
  pose proof remove_remove.
  specialize H6 with (x:=y) (y:=x0) (c:=a).
  rewrite H6 in H5.
  apply clauseSet_aux_lemma5 in H5.
  apply clauseSet_aux_lemma5 in H5.
  exact H5.
  apply clauseSet_aux_lemma5 in H5.
  apply CNF.union_spec.
  right.
  exact H5.
  apply clauseSet_aux_lemma3 in H5.
  destruct H5.
  apply clauseSet_aux_lemma5.
  apply CNF.union_spec.
  right.
  exact H5.
  apply CNF.union_spec.
  right.
  apply CNF.union_spec.
  right.
  exact H5.
  intro.
  apply clauseSet_aux_lemma3 in H5.
  destruct H5.
  apply clauseSet_aux_lemma3 in H5.
  destruct H5.
  pose proof remove_remove.
  specialize H6 with (x:=x0) (y:=y) (c:=a).
  rewrite H6 in H5.
  apply clauseSet_aux_lemma5 in H5.
  apply clauseSet_aux_lemma5 in H5.
  exact H5.
  apply clauseSet_aux_lemma5 in H5.
  apply CNF.union_spec.
  right.
  exact H5.
  apply clauseSet_aux_lemma3 in H5.
  destruct H5.
  apply clauseSet_aux_lemma5.
  apply CNF.union_spec.
  right.
  exact H5.
  apply CNF.union_spec.
  right.
  apply CNF.union_spec.
  right.
  exact H5.
  exact H0.
  tauto.
  exact H.
Qed.

Lemma valid_clause_set : forall (c:Clause.t), (valid_clause c) -> CNF.In c clauseSet.
Proof.
  unfold valid_clause.
  unfold Clause.For_all.
  intros.
  apply valid_clause_set_aux.
  unfold Clause.Subset.
  intros.
  apply H in H0.
  apply valid_lit_set.
  exact H0.
Qed.

Lemma valid_CNF_set : forall (h:CNF.t), valid_CNF h -> CNF.Subset h clauseSet.
Proof.
  intros.
  unfold CNF.Subset.
  intros.
  unfold valid_CNF in H.
  unfold CNF.For_all in H.
  apply H in H0.
  apply valid_clause_set.
  exact H0.
Qed.

Definition maxi : nat := CNF.cardinal (clauseSet).

Lemma bound_valid_CNF : forall (h:CNF.t), valid_CNF h -> CNF.cardinal h <= maxi.
  intros.
  pose proof valid_CNF_set.
  specialize H0 with (h:=h).
  apply CNFProp.subset_cardinal.
  apply H0.
  apply H.
Qed.

Lemma AXp2Clause_inv : forall (x:nat) (s:NatSet.t), Clause.In (top x) (AXp2Clause s) -> NatSet.In x s.
Proof.
  intros.
  unfold AXp2Clause in H.
  pose proof NatSetProp.fold_rec_bis.
  specialize X with (A:=Clause.t) (s:=s) (i:=Clause.empty)
  (f:=(fun (i : NatSet.elt) (acc : Clause.t) => Clause.add (top i) acc))
  (P:= fun s a => Clause.In (top x) a -> NatSet.In x s).
  apply X in H.
  exact H.
  clear X.
  intros.
  apply NatSetProp.equal_sym in H0.
  rewrite H0.
  apply H1.
  auto.
  clear X.
  intros.
  apply Clause.empty_spec in H0.
  easy.
  clear X.
  intros.
  apply Clause.add_spec in H3.
  destruct H3.
  apply NatSet.add_spec.
  left.
  exact H3.
  apply H2 in H3.
  apply NatSet.add_spec.
  right.
  exact H3.
Qed.

Lemma AXp2Clause_lemma : forall (x:nat) (s:NatSet.t), NatSet.In x s -> Clause.In (top x) (AXp2Clause s).
Proof.
  intros.
  unfold AXp2Clause.
  pose proof NatSetProp.fold_rec_bis.
  specialize X with (A:=Clause.t) (s:=s) (i:=Clause.empty)
  (f:=(fun (i : NatSet.elt) (acc : Clause.t) => Clause.add (top i) acc))
  (P:= fun s a => NatSet.In x s -> Clause.In (top x) a).
  apply X.
  intros.
  rewrite H0 in H1.
  apply H1 in H2.
  exact H2.
  intro.
  apply NatSet.empty_spec in H0.
  easy.
  intros.
  apply NatSet.add_spec in H3.
  destruct H3.
  apply Clause.add_spec.
  left.
  exact H3.
  apply Clause.add_spec.
  right.
  apply H2 in H3.
  exact H3.
  exact H.
Qed.

Lemma AXp2Clause_range : forall (lit: literal) (s:NatSet.t), Clause.In lit (AXp2Clause s) -> exists (n:nat), lit = top n.
Proof.
  intros.
  unfold AXp2Clause in H.
  pose proof NatSetProp.fold_rec_bis.
  specialize X with (A:=Clause.t) (s:=s) (i:=Clause.empty)
  (f:=(fun (i : NatSet.elt) (acc : Clause.t) => Clause.add (top i) acc))
  (P:= fun s a => Clause.In lit a -> exists (x:nat), lit = top x).
  apply X in H.
  exact H.
  clear X.
  intros.
  apply H1 in H2.
  exact H2.
  intro.
  apply Clause.empty_spec in H0.
  easy.
  clear X.
  intros.
  apply Clause.add_spec in H3.
  destruct H3.
  fold (OWL.eq lit (top x)) in H3.
  exists x.
  apply OWL.eq_leibniz.
  exact H3.
  apply H2 in H3.
  exact H3.
Qed.

Lemma seeded_is_WAXP : forall (k : list T -> Tk) (v : list T) (s : NatSet.t) (vl vu : list T),
    stable k
/\ is_bounded v
/\ build_vl_vu v s = (vl, vu) 
/\ Tk_eq_dec (k vl) (k vu) = true
-> is_weak_AXp k v (NatSet.diff featureSet s).
Proof.
  intros.
  unfold is_weak_AXp.
  split.
  (* valid_set *)
  apply valid_set_in_featureSet.
  apply diff_subset.
  (* k equalities *)
  intros.
  destruct H0 as (lv,H0).
  destruct H0 as (lx,H0).
  destruct H0 as (xbounded,H0).
  destruct H as (k_stable,H).
  destruct H as (bounded_v,H).
  destruct H as (def_vl_vu, eq_k).
  unfold stable in k_stable.
  generalize (k_stable vl vu x).
  intro kstable.
  destruct kstable.
  split.
  (* length vu = nb_feature *)
  rewrite <- lv.
  apply (length_build_vl_vu v vl vu s).
  symmetry.
  exact def_vl_vu.
  split.
  (* length vu = nb_feature *)
  rewrite <- lv.
  apply (length_build_vl_vu v vl vu s).
  symmetry.
  exact def_vl_vu.
  split.
  (* length x = nb_feature *)
  exact lx.
  split.
  (* is_bounded vl *)
  apply (bounded_build_vl_vu v vl vu s).
  split.
  apply bounded_v.
  symmetry.
  exact def_vl_vu.
  split.
  (* is_bounded vu *)
  apply (bounded_build_vl_vu v vl vu s).
  split.
  apply bounded_v.
  symmetry.
  exact def_vl_vu.
  split.
  (* is_bounded x *)
  exact xbounded.
  split.
  (* le_n vl x *)
  unfold le_n.
  split.
    (* length vl = nb_feature *)
    rewrite <- lv.
    apply (length_build_vl_vu v vl vu s).
    symmetry.
    exact def_vl_vu.
    split.
    (* length x = nb_feature *)
    exact lx.
    (* forall i : nat, 0 <= i < nb_feature -> led (get i vl) (get i x) *)
    intros.
    cut (In i (diff featureSet s) \/ ~In i (diff featureSet s)).
    intro cases.
    destruct cases.
      (* In i (diff featureSet s) *)
      cut (get i vl = get i v).
      intro r1.
      rewrite r1.
      cut (get i x = get i v).
      intro r2.
      rewrite r2.
      apply led_eq.
      reflexivity.
        (* get i x = get i v *)
        specialize H0 with (j:=i).
        destruct H0.
        lia.
        apply H0.
        tauto.
        (* get i vl = get i v *)
        pose proof (get_in_p_build_vl_vu v vl vu s i).
        destruct H2.
        split. lia. split. lia. symmetry. exact def_vl_vu.
        apply H3.
        apply (in_diff featureSet s).
        split.
        apply in_valid_set_in_featureSet.
        exact H.
        exact H1.
      (* In i (diff featureSet s) *)
      cut (get i vl = lambda i).
      intro r1.
      rewrite r1.
      unfold is_bounded in xbounded.
      apply xbounded.
      rewrite lx.
      lia.
        (* get i vl = lambda i *)
        pose proof (get_in_p_build_vl_vu v vl vu s i).
        destruct H2.
        split. lia. split. lia. symmetry. exact def_vl_vu.
        apply H2.
        apply (not_in_diff featureSet s).
        split.
        apply in_valid_set_in_featureSet.
        exact H.
        exact H1.
    tauto.
    split.
  (* le_n x vu *)
  unfold le_n.
  split.
    (* length x = nb_feature *)
    exact lx.
    split.
    (* length vu = nb_feature *)
    rewrite <- lv.
    apply (length_build_vl_vu v vl vu s).
    symmetry.
    exact def_vl_vu.
    (* forall i : nat, 0 <= i < nb_feature -> led (get i x) (get i vu) *)
    intros.
    cut (In i (diff featureSet s) \/ ~In i (diff featureSet s)).
    intro cases.
    destruct cases.
      (* In i (diff featureSet s) *)
      cut (get i vu = get i v).
      intro r1.
      rewrite r1.
      cut (get i x = get i v).
      intro r2.
      rewrite r2.
      apply led_eq.
      reflexivity.
        (* get i x = get i v *)
        specialize H0 with (j:=i).
        destruct H0.
        lia.
        apply H0.
        tauto.
        (* get i vu = get i v *)
        pose proof (get_in_p_build_vl_vu v vl vu s i).
        destruct H2.
        split. lia. split. lia. symmetry. exact def_vl_vu.
        apply H3.
        apply (in_diff featureSet s).
        split.
        apply in_valid_set_in_featureSet.
        exact H.
        exact H1.
      (* In i (diff featureSet s) *)
      cut (get i vu = nu i).
      intro r1.
      rewrite r1.
      unfold is_bounded in xbounded.
      apply xbounded.
      rewrite lx.
      lia.
        (* get i vu = nu i *)
        pose proof (get_in_p_build_vl_vu v vl vu s i).
        destruct H2.
        split. lia. split. lia. symmetry. exact def_vl_vu.
        apply H2.
        apply (not_in_diff featureSet s).
        split.
        apply in_valid_set_in_featureSet.
        exact H.
        exact H1.
    tauto.
    (* k vl = k vu*)
    cut (~ (k vl <> k vu)).
    tauto.
    cut (~(Tk_eq_dec (k vl) (k vu) = false)).
    generalize (Tk_eq_coherent_neq (k vl) (k vu)).
    apply contrapose.
    destruct (Tk_eq_dec (k vl) (k vu)).
    lia.
    lia.
  (* k vl = k v*)
  generalize (k_stable vl vu v).
  intro kstable.
  destruct kstable.
  split.
  (* length vl = nb_feature *)
  rewrite <- lv.
  apply (length_build_vl_vu v vl vu s).
  symmetry.
  exact def_vl_vu.
  split.
  (* length vu = nb_feature *)
  rewrite <- lv.
  apply (length_build_vl_vu v vl vu s).
  symmetry.
  exact def_vl_vu.
  split.
  (* length v = nb_feature *)
  exact lv.
  split.
  (* is_bounded vl *)
  apply (bounded_build_vl_vu v vl vu s).
  split.
  apply bounded_v.
  symmetry.
  exact def_vl_vu.
  split.
  (* is_bounded vu *)
  apply (bounded_build_vl_vu v vl vu s).
  split.
  apply bounded_v.
  symmetry.
  exact def_vl_vu.
  split.
  (* is_bounded v *)
  exact bounded_v.
  split.
  (* le_n vl v *)
  unfold le_n.
  split.
    (* length vl = nb_feature *)
    rewrite <- lv.
    apply (length_build_vl_vu v vl vu s).
    symmetry.
    exact def_vl_vu.
    split.
    (* length v = nb_feature *)
    exact lv.
    (* forall i : nat, 0 <= i < nb_feature -> led (get i vl) (get i v) *)
    intros.
    pose proof (get_in_p_build_vl_vu v vl vu s i).
    destruct H1.
    split. lia. split. lia. symmetry. exact def_vl_vu.
    cut (In i s \/ ~In i s).
    intro cases.
    destruct cases.
      (* In i s *)
      cut (get i vl = lambda i).
      intro r1.
      rewrite r1.
      unfold is_bounded in bounded_v.
      apply bounded_v.
      lia.
      apply H1.
      exact H3.
      (* ~ In i s *)
      cut (get i vl = get i v).
      intro r1.
      rewrite r1.
      apply led_eq.
      reflexivity.
      apply H2.
      apply H3.
    tauto.
  split.
  (* le_n v vu *)
  unfold le_n.
  split.
    (* length v = nb_feature *)
    exact lv.
    split.
    (* length vu = nb_feature *)
    rewrite <- lv.
    apply (length_build_vl_vu v vl vu s).
    symmetry.
    exact def_vl_vu.
    (* forall i : nat, 0 <= i < nb_feature -> led (get i v) (get i vu) *)
    intros.
    intros.
    pose proof (get_in_p_build_vl_vu v vl vu s i).
    destruct H1.
    split. lia. split. lia. symmetry. exact def_vl_vu.
    cut (In i s \/ ~In i s).
    intro cases.
    destruct cases.
      (* In i s *)
      cut (get i vu = nu i).
      intro r1.
      rewrite r1.
      unfold is_bounded in bounded_v.
      apply bounded_v.
      lia.
      apply H1.
      exact H3.
      (* ~ In i s *)
      cut (get i vu = get i v).
      intro r1.
      rewrite r1.
      apply led_eq.
      reflexivity.
      apply H2.
      apply H3.
    tauto.
    (* k vl = k vu*)
    cut (~ (k vl <> k vu)).
    tauto.
    cut (~(Tk_eq_dec (k vl) (k vu) = false)).
    generalize (Tk_eq_coherent_neq (k vl) (k vu)).
    apply contrapose.
    destruct (Tk_eq_dec (k vl) (k vu)).
    lia.
    lia.
  (* k vl = k vl *)
  reflexivity.
Qed.


Lemma seeded_is_WCXP : forall (k : list T -> Tk) (v : list T) (s : NatSet.t) (vl vu : list T),
    stable k
/\ not_trivial k
/\ length v = nb_feature
/\ is_bounded v
/\ build_vl_vu v s = (vl, vu) 
/\ Tk_eq_dec (k vl) (k vu) = false
/\ valid_set s
-> is_weak_CXp k v s.
Proof.
  intros.
  unfold is_weak_CXp.
  split.
  (* valid_set *)
  apply H.
  (* k diff *)
  cut (k v = k vl \/ k v <> k vl).
  intro cases.
  destruct cases.
  (* kv = k vl *)
  exists vu.
  destruct H as (kstable,H).
  destruct H as (ntri,H).
  destruct H as (lv,H).
  destruct H as (bv,H).
  destruct H as (def_vl_vu,H).
  destruct H as (diff_k, validset).
  split.
    (* length v = nb_feature *)
    exact lv.
  split.
    (* length vu = nb_feature*)
    rewrite <- lv.
    apply (length_build_vl_vu v vl vu s).
    symmetry.
    exact def_vl_vu.
  split.
    (* is_bounded vu *)
    apply (bounded_build_vl_vu v vl vu s).
    split.
    apply bv.
    symmetry.
    exact def_vl_vu.
  split.
    (* forall j : nat, j >= 0 /\ j < nb_feature -> ~ In j s /\ get j vu = get j v \/ In j s *)
    intros.
    cut (~ In j s  \/ In j s).
    intro cases.
    destruct cases.
      (* ~ In j s *)
      left.
      split.
      exact H1.
      pose proof (get_in_p_build_vl_vu v vl vu s j).
      destruct H2.
      split.
      lia.
      split.
      lia.
      symmetry.
      exact def_vl_vu.
      apply H3.
      exact H1.
      (* In j s *)
      right.
      exact H1.
    tauto.
  rewrite H0.
  unfold not.
  intro.
  pose proof Tk_eq_coherent_eq (k vl) (k vu).
  apply symmetry in H.
  apply H1 in H.
  rewrite diff_k in H.
  discriminate H.
  (* k v <> k vl '*)
  exists vl.
  destruct H as (kstable,H).
  destruct H as (ntri,H).
  destruct H as (lv,H).
  destruct H as (bv,H).
  destruct H as (def_vl_vu,H).
  destruct H as (diff_k, validset).
  split.
    (* length v = nb_feature *)
    exact lv.
  split.
    (* length vl = nb_feature *)
    rewrite <- lv.
    apply (length_build_vl_vu v vl vu s).
    symmetry.
    exact def_vl_vu.
  split.
    (* is_bounded vl *)
    apply (bounded_build_vl_vu v vl vu s).
    split.
    apply bv.
    symmetry.
    exact def_vl_vu.
  split.
    (* forall j : nat, j >= 0 /\ j < nb_feature -> ~ In j s /\ get j vl = get j v \/ In j s *)
    intros.
    cut (~ In j s  \/ In j s).
    intro cases.
    destruct cases.
      (* ~ In j s *)
      left.
      split.
      exact H1.
      pose proof (get_in_p_build_vl_vu v vl vu s j).
      destruct H2.
      split.
      lia.
      split.
      lia.
      symmetry.
      exact def_vl_vu.
      apply H3.
      exact H1.
      (* In j s *)
      right.
      exact H1.
    tauto.
  (* k vl <> k v *)
  symmetry.
  exact H0.
  tauto.
Qed.


Lemma growth_AXp: forall (k : list T -> Tk) (sat : CNF.t -> option NatSet.t) (v : list T) (h : CNF.t) (s : NatSet.t),
stable k ->
valid_CNF h -> 
length v = nb_feature /\
is_bounded v ->
sat_correct  sat ->
sat h = Some s ->
forall vl vu : list T,
build_vl_vu v s = (vl, vu) ->
Tk_eq_dec (k vl) (k vu) = true -> ~CNF.In (AXp2Clause (findAXp k v s)) h.
Proof.
  intros k sat v h s H vcnf H0 H1 H2 vl vu H3 H4.
  cut (is_weak_AXp k v (NatSet.diff featureSet s)).
  intro s_waxp.
  destruct H1.
  unfold sat_satis in H1.
  specialize H1 with (p:=h) (r:= Some s).
  apply Logic.eq_sym in H2.
  cut (sat h = Some s).
  intro.
  apply H1 in H6.
  destruct H6.
  destruct H6.
  destruct H6.
  inversion H6.
  apply Logic.eq_sym in H9.
  rewrite H9.
  rewrite H9 in H7.
  unfold clause_satis in H7.
  pose proof correct_findAXp.
  specialize H8 with (k:=k) (v:=v) (s:=s).
  assert (NH := conj H (conj s_waxp H0)).
  clear H.
  apply H8 in NH.
  destruct NH.
  destruct H10.
  destruct H11.
  clear H0 H1 H8.
  intro.
  apply H7 in H0.
  destruct H0.
  destruct H0.
  destruct H0.
  apply AXp2Clause_inv in H0.
  unfold NatSet.Subset in H10.
  specialize H10 with (a:=x0).
  apply H10 in H0.
  apply NatSet.diff_spec in H0.
  destruct H0.
  absurd (NatSet.In x0 s).
  exact H8.
  exact H1.
  destruct H0.
  apply AXp2Clause_range in H0.
  elim H0.
  intro.
  discriminate.
  destruct H6.
  discriminate.
  apply Logic.eq_sym.
  exact H2.
  pose proof seeded_is_WAXP as p_s_waxp.
  apply (p_s_waxp k v s vl vu).
  split. exact H. split.
  (* is_bounded v *)
  apply H0.
  split.
  exact H3.
  exact H4.
Qed.

Definition meas (h : CNF.t) : nat := (maxi - (CNF.cardinal h)).

Theorem AXp_term : forall (k : list T -> Tk) (sat : CNF.t -> option NatSet.t) (v : list T) (h : CNF.t) (s : NatSet.t),
stable k ->
length v = nb_feature /\
is_bounded v ->
sat_correct  sat ->
valid_CNF h ->
sat h = Some s ->
forall vl vu : list T,
build_vl_vu v s = (vl, vu) ->
Tk_eq_dec (k vl) (k vu) = true -> meas (CNF.add (AXp2Clause (findAXp k v s)) h) < meas h.
Proof.
  intros.
  cut (is_weak_AXp k v (NatSet.diff featureSet s)).
  intro s_waxp.
  unfold meas.
  pose proof growth_AXp.
  specialize H6 with (k:=k) (sat:=sat) (v:=v) (h:=h) (s:=s) (vl:=vl) (vu:=vu).
  cut (stable k).
  intro.
  apply H6 in H.
  apply CNFProp.add_cardinal_2 in H.
  rewrite H.
  pose proof valid_CNF_incr.
  specialize H8 with (h:=h) (c:= AXp2Clause (findAXp k v s)).
  pose proof valid_set_findAXp.
  specialize H9 with (k:=k) (v:=v) (s:=s).
  assert (NH0 := conj H7 (conj s_waxp H0)).
  clear H0.
  apply H9 in NH0.
  apply valid_AXp2Clause in NH0.
  apply H8 in NH0.
  apply bound_valid_CNF in NH0.
  apply bound_valid_CNF in H2.
  lia.
  exact H2.
  exact H2.
  exact H0.
  exact H1.
  exact H3.
  exact H4.
  exact H5.
  exact H.
  pose proof seeded_is_WAXP as p_s_waxp.
  apply (p_s_waxp k v s vl vu).
  split. exact H. split.
  apply H0.
  split.
  exact H4. 
  exact H5.
Qed.


Lemma CXp2Clause_inv : forall (x:nat) (s:NatSet.t), Clause.In (bot x) (CXp2Clause s) -> NatSet.In x s.
Proof.
  intros.
  unfold CXp2Clause in H.
  pose proof NatSetProp.fold_rec_bis.
  specialize X with (A:=Clause.t) (s:=s) (i:=Clause.empty)
  (f:=(fun (i : NatSet.elt) (acc : Clause.t) => Clause.add (bot i) acc))
  (P:= fun s a => Clause.In (bot x) a -> NatSet.In x s).
  apply X in H.
  exact H.
  clear X.
  intros.
  apply NatSetProp.equal_sym in H0.
  rewrite H0.
  apply H1.
  auto.
  clear X.
  intros.
  apply Clause.empty_spec in H0.
  easy.
  clear X.
  intros.
  apply Clause.add_spec in H3.
  destruct H3.
  apply NatSet.add_spec.
  left.
  exact H3.
  apply H2 in H3.
  apply NatSet.add_spec.
  right.
  exact H3.
Qed.

Lemma CXp2Clause_lemma : forall (x:nat) (s:NatSet.t), NatSet.In x s -> Clause.In (bot x) (CXp2Clause s).
Proof.
  intros.
  unfold CXp2Clause.
  pose proof NatSetProp.fold_rec_bis.
  specialize X with (A:=Clause.t) (s:=s) (i:=Clause.empty)
  (f:=(fun (i : NatSet.elt) (acc : Clause.t) => Clause.add (bot i) acc))
  (P:= fun s a => NatSet.In x s -> Clause.In (bot x) a).
  apply X.
  intros.
  rewrite H0 in H1.
  apply H1 in H2.
  exact H2.
  intro.
  apply NatSet.empty_spec in H0.
  easy.
  intros.
  apply NatSet.add_spec in H3.
  destruct H3.
  apply Clause.add_spec.
  left.
  exact H3.
  apply Clause.add_spec.
  right.
  apply H2 in H3.
  exact H3.
  exact H.
Qed.

Lemma CXp2Clause_range : forall (lit: literal) (s:NatSet.t), Clause.In lit (CXp2Clause s) -> exists (n:nat), lit = bot n.
Proof.
  intros.
  unfold CXp2Clause in H.
  pose proof NatSetProp.fold_rec_bis.
  specialize X with (A:=Clause.t) (s:=s) (i:=Clause.empty)
  (f:=(fun (i : NatSet.elt) (acc : Clause.t) => Clause.add (bot i) acc))
  (P:= fun s a => Clause.In lit a -> exists (x:nat), lit = bot x).
  apply X in H.
  exact H.
  clear X.
  intros.
  apply H1 in H2.
  exact H2.
  intro.
  apply Clause.empty_spec in H0.
  easy.
  clear X.
  intros.
  apply Clause.add_spec in H3.
  destruct H3.
  fold (OWL.eq lit (bot x)) in H3.
  exists x.
  apply OWL.eq_leibniz.
  exact H3.
  apply H2 in H3.
  exact H3.
Qed.

Lemma growth_CXp: forall (k : list T -> Tk) (sat : CNF.t -> option NatSet.t) (v : list T) (h : CNF.t) (s : NatSet.t),
stable k  /\ not_trivial k ->
valid_CNF h ->
length v = nb_feature /\
is_bounded v ->
sat_correct  sat ->
sat h = Some s ->
forall vl vu : list T,
build_vl_vu v s = (vl, vu) ->
Tk_eq_dec (k vl) (k vu) = false -> ~CNF.In (CXp2Clause (findCXp k v (NatSet.diff featureSet s))) h.
Proof.
  intros k sat v h s H vcnf H0 H1 H2 vl vu H3 H4.
  cut (is_weak_CXp k v s).
  intro s_wcxp.
  destruct H1.
  unfold sat_satis in H1. 
  specialize H1 with (p:=h) (r:= Some s).
  apply Logic.eq_sym in H2.
  cut (sat h = Some s).
  intro.
  apply H1 in H6.
  destruct H6.
  destruct H6.
  destruct H6.
  inversion H6.
  apply Logic.eq_sym in H9.
  rewrite H9.
  rewrite H9 in H7.
  unfold clause_satis in H7. 
  pose proof correct_findCXp.
  specialize H8 with (k:=k) (v:=v) (s:=(NatSet.diff featureSet s)).
  destruct H.
  assert (NH := conj H (conj H10 (conj s_wcxp H0))).
  clear H H10.
  cut (NatSet.Equal (diff featureSet (diff featureSet s)) s).
  intro r.
  apply NatSet.eq_leibniz in r.
  rewrite r in H8.
  apply H8 in NH.
  destruct NH.
  destruct H10.
  destruct H11.
  clear H0 H1 H8.
  intro.
  apply H7 in H0.
  destruct H0.
  destruct H0.
  destruct H0.
  apply CXp2Clause_range in H0.
  destruct H0.
  discriminate.
  destruct H0.
  apply CXp2Clause_inv in H0.
  unfold NatSet.Subset in H10.
  specialize H10 with (a:=x0).
  apply H10 in H0.
  apply NatSet.diff_spec in H0.
  destruct H0.
  pose proof NatSet.diff_spec.
  specialize H13 with (s:=featureSet) (s':=s) (x:=x0).
  apply Logic.not_iff_compat in H13.
  apply H13 in H8.
  apply Logic.Classical_Prop.not_and_or in H8.
  destruct H8.
  absurd (NatSet.In x0 featureSet).
  exact H8.
  exact H0.
  absurd (~NatSet.In x0 s).
  exact H8.
  exact H1.
    (* diff featureSet (diff featureSet s) = s *)
    apply diff_diff.
    unfold sat_index_bound in H5.
    specialize H5 with (p:=h) (r:=s).
    apply valid_set_in_featureSet.
    apply H5.
    exact H2.
    exact vcnf.
    (* fin *)
  destruct H6.
  discriminate.
  apply Logic.eq_sym.
  exact H2.

  pose proof seeded_is_WCXP as p_s_wcxp.
  apply (p_s_wcxp k v s vl vu).
  split. apply H. split. apply H. split.
  (* is_bounded v *)
  apply H0.
  split.
  apply H0.
  split.
  exact H3.
  split.
  exact H4.
  unfold sat_correct in H1.
  unfold sat_index_bound in H1.
  destruct H1.
  specialize H5 with (p:=h) (r:=s).
  apply H5.
  symmetry.
  exact H2.
  exact vcnf.
Qed.

Theorem CXp_term : forall (k : list T -> Tk) (sat : CNF.t -> option NatSet.t) (v : list T) (h : CNF.t) (s : NatSet.t),
stable k /\ not_trivial k ->
length v = nb_feature /\
is_bounded v ->
sat_correct  sat ->
valid_CNF h ->
sat h = Some s ->
forall vl vu : list T,
build_vl_vu v s = (vl, vu) ->
Tk_eq_dec (k vl) (k vu) = false ->
meas (CNF.add (CXp2Clause (findCXp k v (NatSet.diff featureSet s))) h) < meas h.
Proof.
  intros.
  cut (is_weak_CXp k v (NatSet.diff featureSet (NatSet.diff featureSet s))).
  intro s_wcxp.
  unfold meas.
  pose proof growth_CXp.
  specialize H6 with (k:=k) (sat:=sat) (v:=v) (h:=h) (s:=s) (vl:=vl) (vu:=vu).
  cut (not_trivial k /\ stable k).
  intro.
  apply H6 in H.
  apply CNFProp.add_cardinal_2 in H.
  rewrite H.
  pose proof valid_CNF_incr.
  specialize H8 with (h:=h) (c:= CXp2Clause (findCXp k v (NatSet.diff featureSet s))).
  pose proof valid_set_findCXp.
  specialize H9 with (k:=k) (v:=v) (s:=(NatSet.diff featureSet s)).
  destruct H7.
  assert (NH0 := conj H10 (conj H7 (conj s_wcxp H0))).
  clear H0.
  apply H9 in NH0.
  apply valid_CXp2Clause in NH0.
  apply H8 in NH0.
  apply bound_valid_CNF in NH0.
  apply bound_valid_CNF in H2.
  lia.
  exact H2.
  exact H2.
  exact H0.
  exact H1.
  exact H3.
  exact H4.
  exact H5.
  destruct H.
  split.
  exact H7.
  exact H.
  pose proof seeded_is_WCXP as p_s_wcxp.
  cut (NatSet.Equal (diff featureSet (diff featureSet s)) s).
  intro r.
  apply NatSet.eq_leibniz in r.
  rewrite r.
  apply (p_s_wcxp k v s vl vu).
  split. apply H. split. apply H. split.
  apply H0.
  split.
  apply H0.
  split.
  exact H4.
  split. 
  exact H5.
  unfold sat_correct in H1.
  unfold sat_index_bound in H1.
  destruct H1.
  specialize H6 with (p:=h) (r:=s).
  apply H6.
  symmetry.
  exact H3.
  exact H2.

    (* diff featureSet (diff featureSet s) = s *)
    apply diff_diff.
    unfold sat_correct in H1.
    unfold sat_index_bound in H1.
    destruct H1.
    specialize H6 with (p:=h) (r:=s).
    apply valid_set_in_featureSet.
    apply H6.
    symmetry.
    exact H3.
    exact H2.
Qed.


Program Fixpoint enumXp_aux 
  (k : list T -> Tk) (kstable : stable k) (knt : not_trivial k)
  (sat : CNF.t -> option NatSet.t) (scorrect : sat_correct sat)
  (v: list T) (bv : length v = nb_feature /\ is_bounded v) 
  (h : CNF.t) (vcnf : valid_CNF h) 
{measure (meas h)} : list Xp :=
  match (sat h) with
  | None => nil
  | Some s => 
    let '(vl,vu):=(build_vl_vu v s) in
    if dec (Tk_eq_dec (k vl) (k vu)) then
      let p := (findAXp k v s) in
      (AXp p)::(enumXp_aux k kstable knt sat scorrect v bv (CNF.add (AXp2Clause p) h) _)
    else
      let s' := NatSet.diff featureSet s in
      let p2 := (findCXp k v s') in
      (CXp p2)::(enumXp_aux k kstable knt sat scorrect v bv ( CNF.add (CXp2Clause p2) h) _ )
  end.
(* Rec OK for AXP *)
Obligation 1.
  apply valid_CNF_incr.
  exact vcnf.
  apply valid_AXp2Clause.
  apply valid_set_findAXp.
  split.
  exact kstable.
  split.
  apply (seeded_is_WAXP k v s (build_vl_vu_aux 0 v s lambda) (build_vl_vu_aux 0 v s nu)).
  auto.
  auto.
  Qed.
(* meas decrease for AXP *)
Obligation 2.
apply (AXp_term k sat v h s kstable (conj H H0) scorrect vcnf (symmetry Heq_anonymous0) (build_vl_vu_aux 0 v s lambda) (build_vl_vu_aux 0 v s nu)).
auto.
exact e.
Qed.
(* Rec OK for CXP *)
Obligation 3.
  apply valid_CNF_incr.
  exact vcnf.
  apply valid_CXp2Clause.
  apply valid_set_findCXp.
  split.
  exact kstable.
  split.
  exact knt.
  split.
  cut (NatSet.Equal (diff featureSet (diff featureSet s)) s).
  intro dd.
  apply NatSet.eq_leibniz in dd.
  rewrite dd.
  apply (seeded_is_WCXP k v s (build_vl_vu_aux 0 v s lambda) (build_vl_vu_aux 0 v s nu)).
  split;auto;split;auto;split;auto;split; auto;split;auto;split;auto.
  unfold sat_correct in scorrect.
  unfold sat_index_bound in scorrect.
  destruct scorrect.
  specialize H2 with (p:=h) (r:=s).
  apply H2.
  symmetry.
  auto.
  auto.
    (* diff featureSet (diff featureSet s) = s *)
    apply diff_diff.
    unfold sat_correct in scorrect.
    unfold sat_index_bound in scorrect.
    destruct scorrect.
    specialize H2 with (p:=h) (r:=s).
    apply valid_set_in_featureSet.
    apply H2.
    symmetry.
    auto.
    auto.
  auto.
  Qed.
(* meas decrease for CXP *)
Obligation 4.
apply (CXp_term k sat v h s (conj kstable knt) (conj H H0) scorrect vcnf (symmetry Heq_anonymous0) (build_vl_vu_aux 0 v s lambda) (build_vl_vu_aux 0 v s nu)).
auto.
exact e.
Qed.


Functional Scheme enumXp_aux_ind := Induction for enumXp_aux Sort Prop.

Theorem valid_CNF_empty : valid_CNF CNF.empty.
Proof.
unfold valid_CNF.
unfold CNF.For_all.
intros.
apply CNF.empty_spec in H.
easy.
Qed.

Definition enumXp 
(k : list T -> Tk) (kstable : stable k)  (knt : not_trivial k)
(sat : CNF.t -> option NatSet.t) (scorrect : sat_correct sat) 
(v: list T) (bv : length v = nb_feature /\ is_bounded v): list Xp := 
enumXp_aux k kstable knt sat scorrect v bv CNF.empty valid_CNF_empty.

(* Correction *)

Theorem AXp_all : forall 
(k : list T -> Tk) (kstable : stable k) (knt : not_trivial k)
(sat : CNF.t -> option NatSet.t) (sc : sat_correct sat) 
(v : list T) (bv : length v = nb_feature /\ is_bounded v),
   sat_correct sat
/\ length v = nb_feature ->
(forall (s:NatSet.t), (List.In (AXp s) (enumXp k kstable knt sat sc v bv)) -> (is_AXp k v s)).
Proof.
  intro;intro;intro;intro;intro;intro;intro;intro.
  unfold enumXp.
  intros.
  functional induction (enumXp_aux k kstable knt sat sc v bv CNF.empty valid_CNF_empty).
  elim H0.
  elim H0.
  intro.
  inversion H1.
  cut (is_weak_AXp k v (NatSet.diff featureSet s0)).
  intro s0_waxp.
  apply correct_findAXp.
  destruct H.
  tauto.
  pose proof seeded_is_WAXP as p_s_waxp.
  apply (p_s_waxp k v s0 vl vu).
  split. exact kstable. split.
  apply bv.
  split.
  exact e0. exact e1.
  (* suite *)
  exact IHl.
  cut (List.In (AXp s) (enumXp_aux k kstable sat sc v bv (CNF.add (CXp2Clause (findCXp k v (NatSet.diff featureSet s0))) h))).
  exact IHl.
  elim H0.
  discriminate.
  tauto.
Qed.

Theorem CXp_all : forall (k : list T -> Tk) (kstable : stable k) (sat : CNF.t -> option NatSet.t) (sc : sat_correct sat) (v : list T) (bv : length v = nb_feature /\ is_bounded v),
not_trivial k (* théoriquement pas besoin, l'existence d'un CXp devrait suffir *) 
/\ valid_CNF CNF.empty -> 
(forall (s:NatSet.t), (List.In (CXp s) (enumXp k kstable sat sc v bv)) -> (is_CXp k v s)).
Proof.
  intro;intro;intro;intro;intro;intro;intro;intro.
  unfold enumXp.
  intro.
  (* is_CXp k v s *)
  functional induction (enumXp_aux k kstable sat sc v bv CNF.empty) using enumXp_aux_ind.
  elim H0.
  cut (List.In (CXp s) (enumXp_aux k kstable sat sc v bv (CNF.add (AXp2Clause (findAXp k v s0)) h))).
  apply IHl.
  split.
  apply H.
  apply valid_CNF_incr.
  apply H.
  apply valid_AXp2Clause.
  cut (is_weak_AXp k v (NatSet.diff featureSet s0)).
  intro s0_waxp.
  apply valid_set_findAXp.
  tauto.
  pose proof seeded_is_WAXP as p_s_waxp.
  apply (p_s_waxp k v s0 vl vu).
  split. exact kstable. split. apply bv. split. exact e0. exact e1.
  elim H0.
  discriminate.
  tauto.
  (* is_CXp k v s *)
  elim H0.
  (* CXp (findCXp k v (diff featureSet s0)) = CXp s -> is_CXp k v s *)
  intro.
  inversion H1.
  cut (is_weak_CXp k v (NatSet.diff featureSet (NatSet.diff featureSet s0))).
  intro s0_wcxp.
  apply correct_findCXp.
  destruct H.
  tauto.
  pose proof seeded_is_WCXP as p_s_wcxp.
  cut (NatSet.Equal (diff featureSet (diff featureSet s0)) s0).
  intro r.
  apply NatSet.eq_leibniz in r.
  rewrite r.
  apply (p_s_wcxp k v s0 vl vu).
  split. exact kstable. split. apply H. split.
  apply bv.
  split.
  apply bv.
  split.
  exact e0.
  split.
  exact e1.
  unfold sat_correct in sc.
  unfold sat_index_bound in sc.
  destruct sc.
  apply (v0 h s0).
  symmetry.
  exact e.
  apply H.
    (* diff featureSet (diff featureSet s0) = s0 *)
    apply diff_diff.
    unfold sat_correct in sc.
    unfold sat_index_bound in sc.
    destruct sc.
    apply valid_set_in_featureSet.
    apply (v0 h s0).
    symmetry.
    exact e.
    apply H.
  apply IHl.
  split.
  apply H.
  apply valid_CNF_incr.
  apply H.
  apply valid_CXp2Clause.
  apply valid_set_findCXp.
  split.
  apply kstable.
  split.
  apply H.
  split.
  pose proof seeded_is_WCXP as p_s_wcxp.
  cut (NatSet.Equal (diff featureSet (diff featureSet s0)) s0).
  intro r.
  apply NatSet.eq_leibniz in r.
  rewrite r.
  apply (p_s_wcxp k v s0 vl vu).
  split. exact kstable. split. apply H. split.
  apply bv.
  split.
  apply bv.
  split.
  exact e0.
  split.
  exact e1.
  unfold sat_correct in sc.
  unfold sat_index_bound in sc.
  destruct sc.
  apply (v0 h s0).
  symmetry.
  exact e.
  apply H. 
    (* diff featureSet (diff featureSet s0) = s0 *)
    apply diff_diff.
    unfold sat_correct in sc.
    unfold sat_index_bound in sc.
    destruct sc.
    apply valid_set_in_featureSet.
    apply (v0 h s0).
    symmetry.
    exact e.
    apply H.
  split.
  apply bv.
  apply bv.
Qed.


Theorem Xp_all : forall 
  (k : list T -> Tk) (kstable : stable k) 
  (sat : CNF.t -> option NatSet.t) (sc : sat_correct sat) 
  (v : list T) (bv : length v = nb_feature /\ is_bounded v),
   not_trivial k (* théoriquement pas besoin, l'existence d'un CXp devrait suffir *)  ->
(forall (xp:Xp), (List.In xp (enumXp k kstable sat sc v bv)) ->  
(exists (s:NatSet.t), (xp = (AXp s) /\ (is_AXp k v s)) \/ (xp = (CXp s) /\ (is_CXp k v s)))).
Proof.
  intros.
  destruct xp.
  exists t0.
  left.
  split.
  reflexivity.
  cut (List.In (AXp t0) (enumXp k kstable sat sc v bv)).
  generalize t0.
  apply AXp_all.
  split.
  apply sc.
  apply bv.
  exact H0.
  exists t0.
  right.
  split.
  reflexivity.
  cut (List.In (CXp t0) (enumXp k kstable sat sc v bv )).
  generalize t0.
  apply CXp_all.
  split. apply H. 
  unfold valid_CNF.
  unfold CNF.For_all.
  intros.
  apply CNF.empty_spec in H1.
  easy.
  exact H0.
Qed.

(* Completude *)

Definition sat_sol (h : CNF.t) (s : NatSet.t) : Prop := 
forall (c:Clause.t), CNF.In c h -> clause_satis c s.

Lemma sat_sol_aux : forall (sat : CNF.t -> option NatSet.t) (h : CNF.t) (s : NatSet.t), 
sat_correct sat ->
valid_CNF h ->
sat h = Some s -> sat_sol h s.
Proof.
  intros.
  unfold sat_sol.
  intros.
  destruct H.
  unfold sat_satis in H.
  specialize H with (p:=h) (r:=Some s).
  apply H in H1.
  destruct H1.
  destruct H1.
  destruct H1.
  inversion H1.
  apply H4.
  exact H2.
  destruct H1.
  discriminate.
Qed.

Lemma rewrite_lemma: forall (x:Clause.t) (s0:NatSet.t), (forall n : nat,
     ~
     (fun n0 : nat =>
      Clause.In (top n0) x /\ NatSet.In n0 s0 \/ Clause.In (bot n0) x /\ ~ NatSet.In n0 s0) n)
-> (forall n0 : nat,
      ~(Clause.In (top n0) x /\ NatSet.In n0 s0 \/ Clause.In (bot n0) x /\ ~ NatSet.In n0 s0)).
Proof.
  intros x s0.
  simpl.
  tauto.
Qed.

Lemma clause_satis_AXp_CXp : forall (k: list T -> Tk) (v:list T) (s1 s2:NatSet.t),
is_AXp k v s1 ->
is_CXp k v s2 ->
clause_satis (AXp2Clause s1) s2.
Proof.
  intros.
  unfold clause_satis.
  pose proof AXp_CXp_non_empty_inter.
  specialize H1 with (k:=k) (v:=v) (s1:=s1) (s2:=s2).
  apply H1 in H.
  destruct H.
  exists x.
  left.
  apply NatSet.inter_spec in H.
  destruct H.
  split.
  apply AXp2Clause_lemma.
  exact H.
  exact H2.
  exact H0.
Qed.

Lemma clause_satis_CXp_AXp : forall (k: list T -> Tk) (v:list T) (s1 s2:NatSet.t),
is_CXp k v s1 ->
is_AXp k v s2 ->
clause_satis (CXp2Clause s1) (NatSet.diff featureSet s2).
Proof.
  intros.
  unfold clause_satis.
  pose proof AXp_CXp_non_empty_inter.
  specialize H1 with (k:=k) (v:=v) (s1:=s2) (s2:=s1).
  apply H1 in H.
  destruct H.
  exists x.
  right.
  apply NatSet.inter_spec in H.
  destruct H.
  split.
  apply CXp2Clause_lemma.
  exact H2.
  intro.
  apply NatSet.diff_spec in H3.
  destruct H3.
  absurd (NatSet.In x s2).
  exact H4.
  exact H.
  exact H0.
Qed.

Lemma sat_sol_AXp_lemma : 
forall (k : list T -> Tk) (sat : CNF.t -> option NatSet.t) (v : list T) (s0 s1 : NatSet.t) (h : CNF.t),
not_trivial k /\ stable k ->
length v = nb_feature /\
is_bounded v ->
sat_correct sat ->
valid_CNF h ->
valid_set s0 ->
sat_sol h s0 ->
sat_sol h s1 ->
~ sat_sol (CNF.add (AXp2Clause (findAXp k v s1)) h) s0 ->
NatSet.Subset s0 (NatSet.diff featureSet (findAXp k v s1)).
Proof.
  intros.
  unfold sat_sol in H4.
  apply Logic.Classical_Pred_Type.not_all_ex_not in H6.
  destruct H6.
  apply Logic.Classical_Prop.imply_to_and in H6.
  destruct H6.
  apply CNF.add_spec in H6.
  destruct H6.
  unfold clause_satis in H7.
  pose proof Logic.Classical_Pred_Type.not_ex_all_not.
  specialize H8 with (U:=nat) 
  (P:= fun n => Clause.In (top n) x /\ NatSet.In n s0 \/ Clause.In (bot n) x /\ ~ NatSet.In n s0).
  specialize (H8 H7).
  pose proof rewrite_lemma.
  specialize H9 with (x:=x) (s0:=s0).
  specialize (H9 H8).
  clear H8 H7.
  rename H9 into H7.
  apply valid_set_in_featureSet in H3.
  unfold NatSet.Subset. 
  intros.
  apply NatSet.diff_spec.
  split.
  unfold NatSet.Subset in H3.
  apply H3.
  exact H8.
  specialize H7 with (n0:=a).
  apply Logic.Classical_Prop.not_or_and in H7.
  destruct H7.
  apply Logic.Classical_Prop.not_and_or in H7.
  destruct H7.
  apply Clause.eq_leibniz in H6.
  rewrite H6 in H7.
  pose proof AXp2Clause_lemma.
  specialize H10 with (x:=a) (s:=(findAXp k v s1)).
  apply contrapose in H10.
  exact H10.
  exact H7.
  absurd (NatSet.In a s0).
  exact H7.
  exact H8.
  apply H4 in H6.
  absurd (clause_satis x s0).
  exact H7.
  exact H6.
Qed.

Lemma sat_sol_CXp_lemma : 
forall (k : list T -> Tk) (sat : CNF.t -> option NatSet.t) (v : list T) (s0 s1 : NatSet.t) (h : CNF.t),
not_trivial k /\ stable k ->
length v = nb_feature /\
is_bounded v ->
sat_correct sat ->
valid_CNF h ->
valid_set s0 ->
sat_sol h s0 ->
sat_sol h s1 ->
~ sat_sol (CNF.add (CXp2Clause (findCXp k v (NatSet.diff featureSet s1))) h) s0 ->
NatSet.Subset (NatSet.diff featureSet s0) (NatSet.diff featureSet (findCXp k v (NatSet.diff featureSet s1))).
Proof.
  intros.
  unfold sat_sol in H4.
  apply Logic.Classical_Pred_Type.not_all_ex_not in H6.
  destruct H6.
  apply Logic.Classical_Prop.imply_to_and in H6.
  destruct H6.
  apply CNF.add_spec in H6.
  destruct H6.
  unfold clause_satis in H7.
  pose proof Logic.Classical_Pred_Type.not_ex_all_not.
  specialize H8 with (U:=nat) 
  (P:= fun n => Clause.In (top n) x /\ NatSet.In n s0 \/ Clause.In (bot n) x /\ ~ NatSet.In n s0).
  specialize (H8 H7).
  pose proof rewrite_lemma.
  specialize H9 with (x:=x) (s0:=s0).
  specialize (H9 H8).
  clear H8 H7.
  rename H9 into H7.
  unfold NatSet.Subset.
  intros.
  specialize H7 with (n0:=a).
  apply Logic.Classical_Prop.not_or_and in H7.
  destruct H7. 
  apply Logic.Classical_Prop.not_and_or in H9.
  destruct H9.
  apply Clause.eq_leibniz in H6.
  rewrite H6 in H9.
  pose proof CXp2Clause_lemma.
  specialize H10 with (x:=a) (s:=(findCXp k v (NatSet.diff featureSet s1))).
  apply contrapose in H10.
  apply NatSet.diff_spec.
  split.
  apply NatSet.diff_spec in H8.
  destruct H8.
  exact H8.
  exact H10.
  exact H9.
  apply NatSet.diff_spec.
  split.
  apply NatSet.diff_spec in H8.
  destruct H8.
  exact H8.
  apply NatSet.diff_spec in H8.
  destruct H8.
  absurd (~NatSet.In a s0).
  exact H9.
  exact H10.
  apply H4 in H6.
  absurd (clause_satis x s0).
  exact H7.
  exact H6.
Qed.

Lemma enumXp_aux_inv_AXp (k : list T -> Tk) (kstable : stable k) (sat : CNF.t -> option NatSet.t) (sc : sat_correct sat) (v : list T) (bv : length v = nb_feature /\ is_bounded v) (s : NatSet.t) :
not_trivial k ->
valid_CNF CNF.empty ->
is_AXp k v s ->
sat_sol CNF.empty (NatSet.diff featureSet s) -> 
(* we take the complement here since an AXp is a list of fixed features while the SAT problem runs on free ones *)
List.In (AXp s) (enumXp_aux k kstable sat sc v bv CNF.empty).
Proof.
  intros.
  functional induction (enumXp_aux k kstable sat sc v bv CNF.empty) using enumXp_aux_ind with (k:=k) (sat:=sat) (v:=v).

  (* List.In (AXp s) nil *)
  destruct sc.
  unfold sat_satis in H3.
  specialize H3 with (p:=h) (r:=None).
  apply H3 in e.
  destruct e.
  destruct H5.
  destruct H5.
  discriminate.
  destruct H5.
  specialize H6 with (s:=(NatSet.diff featureSet s)).
  destruct H6.
  unfold sat_sol in H2.
  specialize H2 with (c:=x).
  destruct H6.
  apply H2 in H6.
  absurd (clause_satis x (NatSet.diff featureSet s)).
  exact H7.
  exact H6.

  (* List.In (AXp s)
    (AXp (findAXp k v s0) :: enumXp_aux k sat v (CNF.add (AXp2Clause (findAXp k v s0)) h)) *)
  cut (sat_sol (CNF.add (AXp2Clause (findAXp k v s0)) h) (NatSet.diff featureSet s) 
  \/ ~sat_sol (CNF.add (AXp2Clause (findAXp k v s0)) h) (NatSet.diff featureSet s)).
  intro.
  destruct H3.

  (* sat_sol (CNF.add (AXp2Clause (findAXp k v s0)) h) (NatSet.diff featureSet s) *)
  (* s <> (findAXp k v sO) *)
  apply IHl in H3.
  apply Lists.List.in_cons.
  exact H3.
  apply valid_CNF_incr.
  exact H0.
  apply valid_AXp2Clause.
  cut (is_weak_AXp k v (NatSet.diff featureSet s0)).
  intro s0_waxp.
  apply valid_set_findAXp.
  tauto.
  pose proof seeded_is_WAXP as p_s_waxp.
  apply (p_s_waxp k v s0 vl vu).
  split. exact kstable. split. apply bv. split. exact e0. exact e1.

  (* ~ sat_sol (CNF.add (AXp2Clause (findAXp k v s0)) h) (NatSet.diff featureSet s) *)
  (* s = (findAXp k v sO) *)
  pose proof sat_sol_AXp_lemma.
  specialize H4 with (k:=k) (sat:=sat) (v:=v) (s0:=(NatSet.diff featureSet s)) (s1:=s0) (h:=h).
  apply H4 in H2.
  clear H4.
  apply subset_diff in H2.
  destruct H1.
  apply H4 in H2.
  destruct H2.
  apply NatSet.eq_leibniz in H2.
  rewrite H2.
  apply Lists.List.in_eq.
  pose proof correct_findAXp.
  specialize H5 with (k:=k) (v:=v) (s:= s0).
  cut (is_weak_AXp k v (NatSet.diff featureSet s0)).
  intro s0_waxp.
  assert (NH0 := conj kstable (conj s0_waxp  bv)).
  clear H0.
  apply H5 in NH0.
  clear H5.
  destruct NH0.
  destruct H5.
  destruct H6.
  absurd (is_weak_AXp k v (findAXp k v s0)).
  exact H2.
  exact H6.
  (*is_weak_AXp k v s0 *)
  pose proof seeded_is_WAXP as p_s_waxp.
  apply (p_s_waxp k v s0 vl vu).
  split. exact kstable. split. apply bv. split. exact e0. exact e1.
  (* suite *)
  destruct H1.
  destruct H1.
  apply valid_set_in_featureSet in H1.
  exact H1.
  pose proof valid_set_findAXp.
  specialize H4 with (k:=k) (v:=v) (s:= s0).
  cut (is_weak_AXp k v (NatSet.diff featureSet s0)).
  intro s0_waxp.
  assert (NH0 := conj kstable (conj s0_waxp  bv)).
  clear H0.
  apply H4 in NH0.
  apply valid_set_in_featureSet in NH0.
  exact NH0.
  (*is_weak_AXp k v s0 *)
  pose proof seeded_is_WAXP as p_s_waxp.
  apply (p_s_waxp k v s0 vl vu).
  split. exact kstable. split. apply bv. split. exact e0. exact e1.
  (* suite *)
  split.
  exact H.
  exact kstable.
  apply bv.
  exact sc.
  exact H0.
  apply valid_set_in_featureSet.
  apply NatSetProp.diff_subset.
  apply sat_sol_aux in e.
  exact e.
  exact sc.
  exact H0.
  exact H3.
  tauto.

  (* List.In (AXp s)
    (CXp (findCXp k v (diff featureSet s0))
    :: enumXp_aux k sat v (CNF.add (CXp2Clause (findCXp k v (diff featureSet s0))) h)) *)
  apply Lists.List.in_cons.
  apply IHl.
  apply valid_CNF_incr.
  exact H0.
  apply valid_CXp2Clause.
  cut (is_weak_CXp k v (NatSet.diff featureSet (NatSet.diff featureSet s0))).
  intro s0_wcxp.
  apply valid_set_findCXp.
  tauto.
  pose proof seeded_is_WCXP as p_s_wcxp.
  cut (NatSet.Equal (diff featureSet (diff featureSet s0)) s0).
  intro r.
  apply NatSet.eq_leibniz in r.
  rewrite r.
  apply (p_s_wcxp k v s0 vl vu).
  split. exact kstable. split. apply H. split. 
  apply bv.
  split.
  apply bv.
  split.
  exact e0.
  split.
  exact e1.
  unfold sat_correct in sc.
  unfold sat_index_bound in sc.
  destruct sc.
  apply (v0 h s0).
  symmetry.
  exact e.
  apply H0. 
    (* diff featureSet (diff featureSet s0) = s0 *)
    apply diff_diff.
    unfold sat_correct in sc.
    unfold sat_index_bound in sc.
    destruct sc.
    apply valid_set_in_featureSet.
    apply (v0 h s0).
    symmetry.
    exact e.
    exact H0.

  unfold sat_sol.
  intros.
  apply CNF.add_spec in H3.
  destruct H3.
  apply Clause.eq_leibniz in H3.
  rewrite H3.
  apply clause_satis_CXp_AXp with (k:=k) (v:=v).
  apply is_CXp_findCXp.
  cut (NatSet.Equal (diff featureSet (diff featureSet s0)) s0).
  intro r.
  apply NatSet.eq_leibniz in r.
  rewrite r.
  split. apply kstable. split. apply H.
  split.
  pose proof seeded_is_WCXP as p_s_wcxp.
  apply (p_s_wcxp k v s0 vl vu).
  split. exact kstable. split. apply H. split. 
  apply bv.
  split.
  apply bv.
  split.
  exact e0. 
  split.
  exact e1.
  unfold sat_correct in sc.
  unfold sat_index_bound in sc.
  destruct sc.
  apply (v0 h s0).
  symmetry.
  exact e.
  apply H0. 
  split. apply bv. apply bv.
    (* diff featureSet (diff featureSet s0) = s0 *)
    apply diff_diff.
    unfold sat_correct in sc.
    unfold sat_index_bound in sc.
    destruct sc.
    apply valid_set_in_featureSet.
    apply (v0 h s0).
    symmetry.
    exact e.
    exact H0.
  exact H1.
  unfold sat_sol in H2.
  apply H2.
  exact H3.
Qed.

Lemma all_AXp (k : list T -> Tk) (kstable : stable k) (sat : CNF.t -> option NatSet.t) (sc : sat_correct sat) (v : list T) (bv : length v = nb_feature /\  is_bounded v) : 
not_trivial k  ->
forall (s:NatSet.t), (is_AXp k v s) ->
List.In (AXp s) (enumXp k kstable sat sc v bv).
Proof.
  intros.
  pose proof enumXp_aux_inv_AXp.
  specialize H1 with (k:=k) (sat:=sat) (v:=v).
  unfold enumXp.
  apply H1.
  exact H.
  unfold valid_CNF.
  unfold CNF.For_all.
  intros.
  apply CNF.empty_spec in H2.
  easy.
  exact H0.
  unfold sat_sol.
  intros.
  apply CNF.empty_spec in H2.
  easy.
Qed.

Lemma enumXp_aux_inv_CXp (k : list T -> Tk) (kstable : stable k) (sat : CNF.t -> option NatSet.t) (sc : sat_correct sat) (v : list T) (bv : length v = nb_feature /\ is_bounded v) (s : NatSet.t) :
not_trivial k ->
valid_CNF CNF.empty ->
is_CXp k v s ->
sat_sol CNF.empty s -> 
List.In (CXp s) (enumXp_aux k kstable sat sc v bv CNF.empty).
Proof.
  intros.
  functional induction (enumXp_aux k kstable sat sc v bv CNF.empty) using enumXp_aux_ind with (k:=k) (sat:=sat) (v:=v).

  (* List.In (CXp s) nil *)
  destruct sc.
  unfold sat_satis in H3.
  apply (H3 h None) in e.
  destruct e.
  destruct H5.
  destruct H5.
  discriminate.
  destruct H5.
  specialize H6 with (s:=s).
  destruct H6.
  unfold sat_sol in H2.
  specialize H2 with (c:=x).
  destruct H6.
  apply H2 in H6.
  absurd (clause_satis x s).
  exact H7.
  exact H6.

  (* List.In (CXp s)
    (AXp (findAXp k v s0) :: enumXp_aux k sat v (CNF.add (AXp2Clause (findAXp k v s0)) h)) *)
  apply Lists.List.in_cons.
  apply IHl.
  apply valid_CNF_incr.
  exact H0.
  apply valid_AXp2Clause.
  apply valid_set_findAXp.
  cut (is_weak_AXp k v (NatSet.diff featureSet s0)).
  intro s0_waxp.
  tauto.
  (*is_weak_AXp k v s0 *)
  pose proof seeded_is_WAXP as p_s_waxp.
  apply (p_s_waxp k v s0 vl vu).
  split. exact kstable. split. apply bv. split. exact e0. exact e1.
  unfold sat_sol.
  intros.
  apply CNF.add_spec in H3.
  destruct H3.
  apply Clause.eq_leibniz in H3.
  rewrite H3.
  apply clause_satis_AXp_CXp with (k:=k) (v:=v).
  apply is_AXp_findAXp.
  cut (is_weak_AXp k v (NatSet.diff featureSet s0)).
  intro s0_waxp.
  tauto.
  (*is_weak_AXp k v s0 *)
  pose proof seeded_is_WAXP as p_s_waxp.
  apply (p_s_waxp k v s0 vl vu).
  split. exact kstable. split. apply bv. split. exact e0. exact e1.
  exact H1.
  unfold sat_sol in H2.
  apply H2.
  exact H3.

  (* List.In (CXp s)
    (CXp (findCXp k v (diff featureSet s0))
    :: enumXp_aux k sat v (CNF.add (CXp2Clause (findCXp k v (diff featureSet s0))) h)) *)
  cut (sat_sol (CNF.add (CXp2Clause (findCXp k v (NatSet.diff featureSet s0))) h) s
  \/ ~sat_sol (CNF.add (CXp2Clause (findCXp k v (NatSet.diff featureSet s0))) h) s).
  intro.
  destruct H3.

  (* sat_sol (CNF.add (CXp2Clause (findCXp k v (diff featureSet s0))) h) s *)
  (* s  <> (findCXp k v (NatSet.diff featureSet s0)) *)
  apply IHl in H3.
  apply Lists.List.in_cons.
  exact H3.
  apply valid_CNF_incr.
  exact H0.
  apply valid_CXp2Clause.
  pose proof correct_findCXp.
  apply valid_set_findCXp.
  split.
  exact kstable.
  split.
  exact H.
  split.
  cut (NatSet.Equal (diff featureSet (diff featureSet s0)) s0).
  intro r.
  apply NatSet.eq_leibniz in r.
  rewrite r.
  pose proof seeded_is_WCXP as p_s_wcxp.
  apply (p_s_wcxp k v s0 vl vu).
  split. exact kstable. split. apply H. split. 
  apply bv.
  split.
  apply bv.
  split.
  exact e0.
  split.
  exact e1.
  unfold sat_correct in sc.
  unfold sat_index_bound in sc.
  destruct sc.
  apply (v0 h s0).
  symmetry.
  exact e.
  apply H0. 
    (* diff featureSet (diff featureSet s0) = s0 *)
    apply diff_diff.
    unfold sat_correct in sc.
    unfold sat_index_bound in sc.
    destruct sc.
    apply valid_set_in_featureSet.
    apply (v0 h s0).
    symmetry.
    exact e.
    exact H0.
  apply bv.

  (* ~ sat_sol (CNF.add (CXp2Clause (findCXp k v (diff featureSet s0))) h) s *)
  (* s  = (findCXp k v (NatSet.diff featureSet s0)) *)
  pose proof sat_sol_CXp_lemma.
  specialize H4 with (k:=k) (sat:=sat) (v:=v) (s0:=s) (s1:=s0) (h:=h).
  apply H4 in H2.
  clear H4.
  apply subset_diff in H2.
  destruct H1.
  apply H4 in H2.
  destruct H2.
  apply NatSet.eq_leibniz in H2.
  rewrite H2.
  apply Lists.List.in_eq.
  pose proof correct_findCXp.
  specialize H5 with (k:=k) (v:=v) (s:=(NatSet.diff featureSet s0)).
  cut (is_weak_CXp k v (diff featureSet (diff featureSet s0))).
  intro wcxp.
  assert (NH0 := conj kstable (conj H (conj wcxp bv))).
  apply H5 in NH0.
  clear H5.
  destruct NH0.
  destruct H6.
  destruct H7.
  absurd (is_weak_CXp k v (findCXp k v (NatSet.diff featureSet s0))).
  exact H2.
  exact H7.

  
  cut (NatSet.Equal (diff featureSet (diff featureSet s0)) s0).
  intro r.
  apply NatSet.eq_leibniz in r.
  rewrite r.
  pose proof seeded_is_WCXP as p_s_wcxp.
  apply (p_s_wcxp k v s0 vl vu).
  split. exact kstable. split. apply H. split. 
  apply bv.
  split.
  apply bv.
  split.
  exact e0.
  split.
  exact e1.
  unfold sat_correct in sc.
  unfold sat_index_bound in sc.
  destruct sc.
  apply (v0 h s0).
  symmetry.
  exact e.
  apply H0. 
    (* diff featureSet (diff featureSet s0) = s0 *)
    apply diff_diff.
    unfold sat_correct in sc.
    unfold sat_index_bound in sc.
    destruct sc.
    apply valid_set_in_featureSet.
    apply (v0 h s0).
    symmetry.
    exact e.
    exact H0.
  (* suite *)
  destruct H1.
  destruct H1.
  apply valid_set_in_featureSet in H1.
  exact H1.
  pose proof valid_set_findCXp.
  specialize H4 with (k:=k) (v:=v) (s:=(NatSet.diff featureSet s0)).
  cut (is_weak_CXp k v (diff featureSet (diff featureSet s0))).
  intro wcxp.
  assert (NH0 := conj kstable (conj H (conj wcxp bv))).
  apply H4 in NH0.
  apply valid_set_in_featureSet in NH0.
  exact NH0.
  cut (NatSet.Equal (diff featureSet (diff featureSet s0)) s0).
  intro r.
  apply NatSet.eq_leibniz in r.
  rewrite r.
  pose proof seeded_is_WCXP as p_s_wcxp.
  apply (p_s_wcxp k v s0 vl vu).
  split. exact kstable. split. apply H. split. 
  apply bv.
  split.
  apply bv.
  split.
  exact e0.
  split.
  exact e1.
  unfold sat_correct in sc.
  unfold sat_index_bound in sc.
  destruct sc.
  apply (v0 h s0).
  symmetry.
  exact e.
  apply H0. 
    (* diff featureSet (diff featureSet s0) = s0 *)
    apply diff_diff.
    unfold sat_correct in sc.
    unfold sat_index_bound in sc.
    destruct sc.
    apply valid_set_in_featureSet.
    apply (v0 h s0).
    symmetry.
    exact e.
    exact H0.
  split.
  exact H.
  exact kstable.
  exact bv.
  exact sc.
  exact H0.
  destruct H1.
  destruct H1.
  exact H1.
  apply sat_sol_aux in e.
  exact e.
  exact sc.
  exact H0.
  exact H3.
  tauto.
Qed.

Lemma all_CXp : forall (k : list T -> Tk) (kstable : stable k) (sat : CNF.t -> option NatSet.t) (sc : sat_correct sat) (v : list T) (bv : length v = nb_feature /\ is_bounded v),
not_trivial k  ->
forall (s:NatSet.t), (is_CXp k v s) ->
List.In (CXp s) (enumXp k kstable sat sc v bv).
Proof.
  intros.
  pose proof enumXp_aux_inv_CXp.
  specialize H1 with (k:=k) (sat:=sat) (v:=v).
  unfold enumXp.
  apply H1.
  exact H.
  unfold valid_CNF.
  unfold CNF.For_all.
  intros.
  apply CNF.empty_spec in H2.
  easy.
  exact H0.
  unfold sat_sol.
  intros.
  apply CNF.empty_spec in H2.
  easy.
Qed.

Theorem all_Xp : forall (k : list T -> Tk) (kstable : stable k) (sat : CNF.t -> option NatSet.t) (sc : sat_correct sat) (v : list T) (bv : length v = nb_feature /\ is_bounded v),
not_trivial k ->
forall (s:NatSet.t), ((is_AXp k v s) -> List.In (AXp s) (enumXp k kstable sat sc v bv)) /\
((is_CXp k v s) -> List.In (CXp s) (enumXp k kstable sat sc v bv)).
Proof.
  intros.
  split.
  apply all_AXp.
  exact H.
  apply all_CXp.
  exact H.
Qed.

Extraction Language OCaml.
Unset Extraction AutoInline.
Extraction "enumXp" enumXp findAXp findCXp.
