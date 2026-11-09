(** Federer (1969), 3.3.19, p. 304:
    the actual original intersections with distinct
    level discs are congruent. Their congruence is
    proved by actual translation of every later
    original descendant and of the limit intersection. *)
From mathcomp Require Import all_boot all_order all_algebra finmap reals boolp classical_sets topology.
From Federer Require Import EuclideanInnerProduct InnerMetric MetricClosedBalls
  FactorialDiscScalesUP FactorialDiscScalesSealed FactorialDiscScaleLaws
  CircularDiscTreeUP CircularDiscLimitUP CircularDiscAncestors CircularDiscLevelPieces
  CircularDiscTranslationGeometry.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope fset_scope.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Pieces.
Variable R:realType.
Local Notation E:=(inner_metric_space (@euclidean_inner_productP R 2)).
Local Notation rho:=(@FactorialDiscScales.radius R).
Variable H:nat->{fset E}.
Hypothesis hH:is_circular_disc_tree H.
Variable A:set E.
Hypothesis hA:is_circular_disc_limit H A.

(** Source for [circular_disc_descendant_translation]:
    actual descendant translation at any later
    original level, supporting the level-piece
    congruence of 3.3.19, p. 304. *)
Lemma circular_disc_descendant_translation j k (c d w:E):
  (j<=k)%N ->c \in H j ->d \in H j ->w \in H k ->
  metric_closed_ball w (rho k) `&` metric_closed_ball c (rho j)!=set0 ->
  w+(d-c) \in H k.
Proof.
move=>hjk hc hd hw hMeet.
have hLevel:(j+(k-j)=k)%N by rewrite subnKC.
rewrite -hLevel in hw hMeet *.
exact:(@circular_disc_descendant_translation_offset R H hH j c d hc hd (k-j)%N w hw hMeet).
Qed.

(** Source for [circular_disc_piece_translation_inclusion]:
    translation from one original level disc to
    another sends its whole original A-piece into
    the other original A-piece, 3.3.19,
    p. 304. No replaced limit set or
    independent subtree is used. *)
Theorem circular_disc_piece_translation_inclusion j (c d:E):
  c \in H j ->d \in H j ->forall x,
  (A `&` metric_closed_ball c (rho j)) x ->
  (A `&` metric_closed_ball d (rho j)) (x+(d-c)).
Proof.
move=>hc hd x [hxA hxC].
have hCentre:c+(d-c)=d by rewrite addrCA subrr addr0.
have hTranslatedBall:metric_closed_ball d (rho j) (x+(d-c)).
  have hShift:=(@circular_disc_ball_translation R c (d-c) x (rho j)).2 hxC.
  by rewrite hCentre in hShift.
split;last exact hTranslatedBall.
apply:(hA _).2=>k.
case:(leqP j k)=>hjk.
- have [w [hw hxW]]:=(hA x).1 hxA k.
  have hMeet:metric_closed_ball w (rho k) `&` metric_closed_ball c (rho j)!=set0.
    by exists x;split.
  have hShift:=@circular_disc_descendant_translation j k c d w hjk hc hd hw hMeet.
  exists (w+(d-c));split=>//.
  exact:(@circular_disc_ball_translation R w (d-c) x (rho k)).2 hxW.
- have hkj:(k<=j)%N:=ltnW hjk.
  have [a [ha hInside]]:=@circular_disc_ancestor_exists R H hH k j hkj d hd.
  exists a;split=>//;exact:hInside _ hTranslatedBall.
Qed.

(** Source for [circular_disc_level_pieces_translates]:
    the exact original A-intersections in every
    original level are translates, proving the
    congruence assertion of 3.3.19, p. 304.
    The inverse translation proves the reverse
    inclusion, including all original boundary points. *)
Theorem circular_disc_level_pieces_translates j (c d:E):
  c \in H j ->d \in H j ->
  (fun x:E=>x+(d-c)) @` (A `&` metric_closed_ball c (rho j))=
    A `&` metric_closed_ball d (rho j).
Proof.
move=>hc hd;apply/seteqP;split=>y.
- move=>[x hx <-];exact:(@circular_disc_piece_translation_inclusion j c d hc hd x hx).
- move=>hy.
  have hBack:=@circular_disc_piece_translation_inclusion j d c hd hc y hy.
  exists (y+(c-d));first exact hBack.
  have hCancel:(c-d)+(d-c)=0 by rewrite addrA subrK subrr.
  by rewrite -addrA hCancel addr0.
Qed.
End Pieces.
