(** Federer (1969), 3.4.5, p. 320: the
    ideal of an original set germ is specified by local
    vanishing of actual analytic representatives. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric AnalyticGermRepresentatives AnalyticGermUP SetGermUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [vanishes_near_on]: the displayed condition
    f(x)=0 on S intersect U for a neighbourhood U of a,
    3.4.5, p. 320. Only actual local values enter. *)
Definition vanishes_near_on (X:topologicalType) (A:zmodType)
    (a:X) (S:set X) (f:X->A):Prop:=
  exists U:set X,open U /\U a /\forall x,S x ->U x ->f x=0.

(** Source for [is_analytic_set_ideal]: the independent
    membership law of ideal gamma_a(S), 3.4.5,
    p. 320. It requires the original local vanishing
    condition for every analytic and set representative. *)
Record is_analytic_set_ideal (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (a:X)
    (sigma:@set_germ_space (Topological.clone (real_norm_metric_space hNX) _) a)
    (I:set (analytic_germ_space hNX a)):Prop:={
  (** Source for [analytic_set_ideal_membership]: a germ
      lies in the ideal exactly when each representative
      vanishes locally on the represented set, 3.4.5, p. 320. *)
  analytic_set_ideal_membership:forall alpha,I alpha <->
    forall (f:@analytic_representative_type R X NX hNX a)
      (S:set (Topological.clone (real_norm_metric_space hNX) _)),
      analytic_germ f=alpha ->@set_germ (Topological.clone (real_norm_metric_space hNX) _) a S=sigma ->
      @vanishes_near_on (Topological.clone (real_norm_metric_space hNX) _) [the zmodType of R^o] a S (analytic_representative_value f)
}.
