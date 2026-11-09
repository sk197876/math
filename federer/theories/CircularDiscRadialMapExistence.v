(** Federer (1969), 3.3.19, p. 305: existence of the
    actual original radial map. Original parent uniqueness
    proves single-valuedness; no global selected parent or
    value outside the printed domain is introduced. *)
From mathcomp Require Import all_boot all_order all_algebra finmap reals boolp classical_sets topology.
From Federer Require Import EuclideanInnerProduct InnerMetric MetricClosedBalls FactorialDiscScalesSealed
  CircularDiscRefinement CircularDiscTreeUP CircularDiscLimitUP CircularDiscTreeTopology CircularDiscLevelPieces
  CircularDiscRadialDirection CircularDiscRadialMapUP PartialFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Existence.
Variable R:realType.
Local Notation E:=(inner_metric_space (@euclidean_inner_productP R 2)).
Local Notation rho:=(@FactorialDiscScales.radius R).
Variable H:nat->{fset E}.
Hypothesis hH:is_circular_disc_tree H.

(** Source for [circular_disc_radial_map_exists]: the original
    eta_n in 3.3.19, p. 305, exists with its exact
    printed domain and formula. Our auxiliary n=4 level
    is also allowed, while all printed n>=5 remain. *)
Theorem circular_disc_radial_map_exists j:
  exists eta:partial_function E E,is_circular_disc_radial_map H j eta.
Proof.
pose G:=fun x v:E=>circular_disc_level_union H j.+1 x /\
  exists z:E,z \in H j /\metric_closed_ball z (rho j) x /\
    v=circular_disc_radial_direction z x.
have hSingle:forall x v w,G x v ->G x w ->v=w.
  move=>x v w [_ [z [hz [hxZ ->]]]] [_ [t [ht [hxT ->]]]].
  have hEqual:=@circular_disc_level_point_unique R H hH j x z t hz ht hxZ hxT.
  by rewrite hEqual.
pose eta:partial_function E E:=@Build_partial_function E E G hSingle.
exists eta;constructor.
- move=>x;split.
  + by move=>[v [hx _]].
  + move=>hx.
    have hxParent:=@circular_disc_levels_nested R H hH j j.+1 (leqnSn j) x hx.
    have [z [hz hxZ]]:=hxParent.
    exists (circular_disc_radial_direction z x);split=>//.
    exists z;by split=>//;split.
- move=>x z v hz hxZ [_ [t [ht [hxT ->]]]].
  have hEqual:=@circular_disc_level_point_unique R H hH j x t z ht hz hxT hxZ.
  by rewrite hEqual.
Qed.
End Existence.
