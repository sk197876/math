(** Federer (1969), 3.1.24, pp. 237–239: the
    neighbourhood and regularity consequences of analyticity. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric NormRegularity NormRegularityLocal NormClassZeroTopology NormAnalyticUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [norm_analytic_at_domain]: a belongs to the
    original domain in Federer 3.1.24, p. 237;
    this follows from U containing a and U contained in A. *)
Lemma norm_analytic_at_domain (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (A:set X) (f:X->Y) a :
  @norm_analytic_at R X Y NX NY hNX hNY A f a -> A a.
Proof. move=>[U [c [ha [hUA _]]]]; exact (hUA a ha). Qed.

(** Source for [norm_analytic_at_neighbourhood]: the same
    smooth neighbourhood and bounds work at every one of its
    points, implicit in Federer 3.1.24, pp. 237–239. *)
Lemma norm_analytic_at_neighbourhood (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (A:set X) (f:X->Y) a :
  @norm_analytic_at R X Y NX NY hNX hNY A f a ->
  exists U:set X,U a /\ @open (real_norm_metric_space hNX) U /\
    forall b,U b -> @norm_analytic_at R X Y NX NY hNX hNY A f b.
Proof.
move=>[U [c [ha [hUA [hc hb]]]]].
exists U; split=>//; split.
- exact (@norm_class_zero_domain_open R X Y NX NY hNX U f (norm_class_continuous (hc 0%N))).
- move=>b hbu; exists U,c; by split=>//; split=>//; split.
Qed.

(** Source for [norm_analytic_class_all_orders]: an analytic
    function is smooth on its domain, Federer 3.1.24,
    p. 239, by locality of the class conditions. *)
Lemma norm_analytic_class_all_orders (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (A:set X) (f:X->Y) :
  @norm_analytic R X Y NX NY hNX hNY A f ->
  norm_class_all_orders hNX hNY A f.
Proof.
move=>hf k; apply: norm_class_local=>a ha.
have [U [c [hUa [hUA [hc hb]]]]]:=hf a ha.
exists U; split; first exact hUa.
split; first exact hUA.
exact (hc k).
Qed.

(** Source for [norm_analytic_domain_open]: analyticity requires
    an open domain, Federer 3.1.24, pp. 237–239.
    Its openness already follows from the local smooth neighbourhoods. *)
Lemma norm_analytic_domain_open (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (A:set X) (f:X->Y) :
  @norm_analytic R X Y NX NY hNX hNY A f -> @open (real_norm_metric_space hNX) A.
Proof.
move=>hf; exact (@norm_class_zero_domain_open R X Y NX NY hNX A f
  (norm_class_continuous (norm_analytic_class_all_orders hf 0%N))).
Qed.
