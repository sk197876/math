(** Federer (1969), 3.3.19, pp. 302–303:
    the actual first split of every sufficiently small
    original test set satisfies the three printed
    coefficient inequalities, including n>=5. *)
From mathcomp Require Import all_boot all_order all_algebra finmap reals classical_sets constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric MetricDiameter FactorialDiscScalesSealed
  CircularTrigonometrySealed CircularDiscTreeUP CircularDiscFirstSplitUP CircularDiscHitDiameter CircularDiscSmallCutoff.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Cutoff.
Variable R:realType.
Local Notation E:=(inner_metric_space (@euclidean_inner_productP R 2)).
Local Notation Sine:=(@CircularTrigonometry.sine R).
Local Notation p:=(@CircularTrigonometry.half_period R).
Variable H:nat->{fset E}.
Hypothesis hH:is_circular_disc_tree H.

(** Source for [circular_disc_first_split_cutoff]: the
    original diameter bound and actual first split
    imply the printed n>=5 and both strict
    sine-coefficient bounds in 3.3.19, p. 303.
    No supplied split radius or scalar margin
    is added as an original theorem hypothesis. *)
Theorem circular_disc_first_split_cutoff (lam:R):0<lam ->lam<p ->
  exists d:R,0<d /\forall j (T:set E),
  is_circular_first_split H T j.+1 ->(extended_metric_diameter T<=d%:E)%E ->
  (5<=j+4)%N /\lam<((j+4)%:R-1)* Sine (p/(j+4)%:R) /\
    lam*(1/2+((j+4).+1)%:R^-1)<((j+4)%:R-1)* Sine (p/(j+4)%:R)-1.
Proof.
move=>hlam hlamP.
have [d [hd hCutoff]]:=@circular_disc_small_radius_cutoff R lam hlam hlamP.
exists d;split=>//;move=>j T hFirst hDiameter.
have hRadius:=@circular_disc_two_hits_radius_below_diameter R H hH j.+1 T d hFirst.1 hDiameter.
exact:hCutoff j (ltW hRadius).
Qed.
End Cutoff.
