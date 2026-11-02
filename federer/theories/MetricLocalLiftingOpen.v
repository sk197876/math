(** General metric topology supporting Federer (1969),
    3.2.28(4), printed p. 267: the explicit ball
    lifting estimate implies openness of the square map
    onto its image. No continuity or compactness substitutes
    for the actual local lifting law. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets topology.
From Federer Require Import HomeomorphismUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [metric_local_lifting_open]: the ball-lifting
    argument after the distance formula in Federer 3.2.28(4),
    p. 267. Supporting general topology: if every small
    target ball lifts into any prescribed source ball, the
    map takes open sets to open sets. *)
Theorem metric_local_lifting_open (R:realType) (X Y:metricType R) (f:X->Y):
  (forall x (e:R),0<e ->exists d:R,0<d /\forall y,
    mdist (f x) y<d ->exists z,mdist x z<e /\f z=y) ->is_open_map f.
Proof.
move=>hLift U hU.
rewrite openE in hU.
rewrite openE=>y [x hx hxy].
have hNb:nbhs x U:=hU x hx.
have [e he hBall]:=(metricType_numDomainType.nbhs_mdistP x U).1 hNb.
have [d [hd hL]]:=hLift x e he.
apply:(metricType_numDomainType.nbhs_mdistP y (f @` U)).2.
exists d; first exact hd.
move=>v hv.
have hNear:mdist (f x) v<d by rewrite hxy.
have [z [hDist hValue]]:=hL v hNear.
exists z; last exact hValue.
exact:hBall z hDist.
Qed.
