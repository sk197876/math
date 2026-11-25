(** Federer (1969), 4.1.7, p. 359:
    the weighted image functional has the
    original L1 continuity used for the
    Baire extension. This supporting implication
    is the same epsilon-delta argument as
    4.1.5, p. 350. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP MeasureLpMembershipUP
  MeasureLpConvergence LoneSeminormContinuityUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [lone_lipschitz_seminorm_continuous]:
    an L1 one-Lipschitz functional is continuous
    on the original partial representatives,
    supporting Federer 4.1.7, p. 359.
    Distance-zero representatives are retained. *)
Theorem lone_lipschitz_seminorm_continuous (R:realType) (X:choiceType)
    (Y:lmodType R) (NY:Y->R) (hNY:is_real_norm NY) (mu:set X->\bar R)
    (J:partial_function X (real_norm_metric_space hNY)->R):
  (forall f g,is_measure_lp_function mu 1 f->is_measure_lp_function mu 1 g->
    (`|J f-J g|%:E<=measure_lp_distance mu NY 1 f g)%E)->
  @is_lone_seminorm_continuous R X Y NY hNY mu J.
Proof.
move=>hLipschitz f hF epsilon hEpsilon.
exists epsilon;split;first exact:hEpsilon.
move=>g hG hDistance.
have hBound:=hLipschitz g f hG hF.
have hStrict:=le_lt_trans hBound hDistance.
by move:hStrict;rewrite lte_fin.
Qed.
