Require Import Arith Lia Init.Datatypes.
Open Scope list_scope.

(* All feature have the same type : T*)
Parameter T : Type.
(* inferior or egals *)
Parameter led : T -> T -> Prop.
Axiom led_eq : forall (d1:T) (d2:T), d1=d2 -> led d1 d2.
Axiom led_borne : forall (d1:T) (d2:T) (d3:T), led d1 d2 /\ led d2 d3 /\ d1=d3 -> d1=d2 /\ d2=d3.
Axiom led_transitivity : forall (d1:T) (d2:T) (d3:T), led d1 d2 /\ led d2 d3 -> led d1 d3.
(* Type of the classes of the classifier *)
Parameter Tk : Type.
Parameter Tk_eq_dec : Tk -> Tk -> bool.
Axiom Tk_eq_coherent_eq : forall (d1:Tk) (d2:Tk), d1=d2 -> (Tk_eq_dec d1 d2)=true.
Axiom Tk_eq_coherent_neq : forall (d1:Tk) (d2:Tk), d1<>d2 -> (Tk_eq_dec d1 d2)=false.
Axiom Tk_tier_exclu : forall (d1:Tk) (d2:Tk), d1<>d2 \/ d1=d2.

Parameter Exception : T.

(* Number of feature *)
Parameter nb_feature : nat.
Axiom nb_feature_not_nul : nb_feature > 0.

(*** bounds on the features ***)
Parameter nu : nat -> T.
Axiom nu_n : forall (j:nat), j >= nb_feature -> nu j = Exception.
Parameter lambda : nat -> T.
Axiom lambda_n : forall (j:nat), j >= nb_feature -> lambda j = Exception.


Definition get  (i:nat) (v : list T) : T :=
 List.nth i v  Exception.

Definition is_bounded (v : list T) : Prop :=
  forall (j:nat), j>=0 /\ j< length v -> 
  led (lambda j) (get j v) /\ led (get j v) (nu j).