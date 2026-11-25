(** Federer (1969), 4.1.8, p. 362: specify
    the original finite product of oriented segments
    by its empty, single-factor and attachment laws.
    The actual current witness and all boundary
    assertions are proved separately. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import OrientedSegmentFactor OrientedRectangleDomain OrientedRectangleSpaces
  EuclideanFundamentalCurrent.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section OrientedRectangleCurrentUP.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Local Notation Factor := (oriented_segment_factor R).
Local Notation C := (fun f=>@oriented_rectangle_space R h2 f (size f)).
Local Notation Product := (@oriented_rectangle_product R h2).

(** Source for [is_oriented_rectangle_current]: the
    original ordered finite Cartesian product of the
    segment currents in Federer 4.1.8, p. 362.
    The empty product has the original E^0 value;
    no Stokes or box-identification conclusion is assumed. *)
Definition is_oriented_rectangle_current (P:forall f:seq Factor,C f):Prop:=
  P [::]=@euclidean_fundamental_current R h2 0%N /\
  (forall a,P [::a]=@oriented_segment_factor_current R h2 a) /\
  (forall a b t,P (a::b::t)=Product a b t 1%N (size (b::t))
    (@oriented_segment_factor_current R h2 a) (P (b::t))).
End OrientedRectangleCurrentUP.
