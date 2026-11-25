(** Federer (1969), 2.10.14, p. 177: for a locally finite- variation curve,
    the printed upper-limit jumps are the jumps of its scalar arc-length
    parameter from 2.5.16, p. 109. The distance upper-limit formulation
    needs no completeness of the metric target: split finite chains near x
    and use the scalar one-sided limits of s. Erratum p. 3, book p. 177 line
    23, concerns the upper integral, not these identities. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology lra.
From Federer Require Import CurveOneSidedJumpUP CurveVariationUP CurveArcLength
  CurveOneSidedLimits ExtendedRealBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [curve_right_jump_arc_length_upper]: supporting
    upper estimate for alpha_+ in 2.10.14, p. 177, using
    distance(g(x),g(t)) <= s(t)-s(x) and the scalar right
    limit s(x+) in 2.5.16, p. 109. *)
Lemma curve_right_jump_arc_length_upper (R : realType) (Y : metricType R)
    (g : R -> Y) (x : R) : curve_locally_finite_variation g ->
  curve_right_jump_size g x<=((arc_length_right g x-arc_length g x)%R)%:E.
Proof.
move=> hg; apply/lee_addgt0Pr=> e he; rewrite -EFinD.
have [u hxu hu] := arc_length_right_adherent hg x he.
apply: curve_one_sided_jump_upper_bound; exists (u-x)%R; split; first by rewrite subr_gt0.
move=> t; rewrite /curve_side_offset /= => /andP[hxt htu].
have hxt' : (x<t)%R by lra.
have htu' : (t<=u)%R by lra.
have hd := @arc_length_distance R Y g hg x t (ltW hxt').
have hs := @arc_length_monotone R Y g hg t u htu'.
rewrite metric_sym lee_fin; lra.
Qed.

(** Source for [curve_left_jump_arc_length_upper]: supporting
    upper estimate for alpha_- in 2.10.14, p. 177, using
    the scalar left limit s(x-) of 2.5.16, p. 109. *)
Lemma curve_left_jump_arc_length_upper (R : realType) (Y : metricType R)
    (g : R -> Y) (x : R) : curve_locally_finite_variation g ->
  curve_left_jump_size g x<=((arc_length g x-arc_length_left g x)%R)%:E.
Proof.
move=> hg; apply/lee_addgt0Pr=> e he; rewrite -EFinD.
have [u hux hu] := arc_length_left_adherent hg x he.
apply: curve_one_sided_jump_upper_bound; exists (x-u)%R; split; first by rewrite subr_gt0.
move=> t; rewrite /curve_side_offset /= => /andP[htx hut].
have htx' : (t<x)%R by lra.
have hut' : (u<=t)%R by lra.
have hd := @arc_length_distance R Y g hg t x (ltW htx').
have hs := @arc_length_monotone R Y g hg u t hut'.
rewrite lee_fin; lra.
Qed.

(** Source for [curve_right_jump_arc_length_lower]: supporting
    reverse estimate for alpha_+ in 2.10.14, p. 177.
    Split each finite chain at its first term above x,
    as in the proof of the right jump identity in 2.5.16,
    p. 109. An eventual distance bound replaces the existence
    of a right limit in the target. *)
Lemma curve_right_jump_arc_length_lower (R : realType) (Y : metricType R)
    (g : R -> Y) (x : R) : curve_locally_finite_variation g ->
  ((arc_length_right g x-arc_length g x)%R)%:E<=curve_right_jump_size g x.
Proof.
move=> hg; apply: extended_real_inf_greatest=> b hb.
case: b hb=> [r| |] hb.
2: exact: leey.
2: by have hnon := curve_side_distance_upper_bound_nonnegative hb; move: hnon.
rewrite lee_fin; apply/ler_addgt0Pr=> e he.
have [d [hd hbound]] := hb.
have [u1 hxu1 hu1] := arc_length_right_adherent hg x he.
pose v : R := Order.min (x+d)%R u1.
have hxv : (x<v)%R by rewrite /v lt_min; apply/andP; split; lra.
have [hxu huv] := midf_lt hxv.
pose u : R := ((x+v)/2)%R.
have hxu' : (x<u)%R := hxu.
have hvd : (v<=x+d)%R by rewrite /v ge_min lexx.
have hvu1 : (v<=u1)%R by rewrite /v ge_min lexx orbT.
have hud : (u<x+d)%R := lt_le_trans huv hvd.
have huu1 : (u<=u1)%R := le_trans (ltW huv) hvu1.
have hsu : (arc_length g u<arc_length_right g x+e)%R.
  exact: le_lt_trans (@arc_length_monotone R Y g hg u u1 huu1) hu1.
have hV : curve_variation g x u<=(r+e)%R%:E.
  apply: extended_real_sup_least=> z [p [hp ->]].
  have [tm [hxtm [htmu hsplit]]] := @partition_chain_sum_split_right R Y g x u p hxu hp.
  apply: le_trans hsplit _.
  rewrite -(@arc_length_increment R Y g hg tm u htmu) -EFinD lee_fin.
  have hrem := @arc_length_right_le R Y g hg x tm hxtm.
  have ht : (0<curve_side_offset true x tm<d)%R.
    rewrite /curve_side_offset /=; apply/andP; split; lra.
  have hdist := hbound tm ht; rewrite lee_fin (metric_sym (g tm) (g x)) in hdist.
  lra.
have hr := @arc_length_right_le R Y g hg x u hxu.
rewrite -(@arc_length_increment R Y g hg x u (ltW hxu)) lee_fin in hV.
lra.
Qed.

(** Source for [curve_left_jump_arc_length_lower]: supporting
    reverse estimate for alpha_- in 2.10.14, p. 177.
    Use the last chain term below x, the left-hand form of
    the proof of 2.5.16, p. 109, without assuming a
    left limit in the metric target. *)
Lemma curve_left_jump_arc_length_lower (R : realType) (Y : metricType R)
    (g : R -> Y) (x : R) : curve_locally_finite_variation g ->
  ((arc_length g x-arc_length_left g x)%R)%:E<=curve_left_jump_size g x.
Proof.
move=> hg; apply: extended_real_inf_greatest=> b hb.
case: b hb=> [r| |] hb.
2: exact: leey.
2: by have hnon := curve_side_distance_upper_bound_nonnegative hb; move: hnon.
rewrite lee_fin; apply/ler_addgt0Pr=> e he.
have [d [hd hbound]] := hb.
have [u1 hu1x hu1] := arc_length_left_adherent hg x he.
pose v : R := Order.max (x-d)%R u1.
have hvx : (v<x)%R by rewrite /v gt_max; apply/andP; split; lra.
have [hvu hux] := midf_lt hvx.
pose u : R := ((v+x)/2)%R.
have hux' : (u<x)%R := hux.
have hdv : (x-d<=v)%R by rewrite /v le_max lexx.
have hu1v : (u1<=v)%R by rewrite /v le_max lexx orbT.
have hdu : (x-d<u)%R := le_lt_trans hdv hvu.
have hu1u : (u1<=u)%R := le_trans hu1v (ltW hvu).
have hsu : (arc_length_left g x-e<arc_length g u)%R.
  exact: lt_le_trans hu1 (@arc_length_monotone R Y g hg u1 u hu1u).
have hV : curve_variation g u x<=(r+e)%R%:E.
  apply: extended_real_sup_least=> z [p [hp ->]].
  have [tm [hutm [htmx hsplit]]] := @partition_chain_sum_split_left R Y g u x p hux hp.
  apply: le_trans hsplit _.
  rewrite -(@arc_length_increment R Y g hg u tm hutm) -EFinD lee_fin.
  have hrem := @arc_length_le_left R Y g hg tm x htmx.
  have ht : (0<curve_side_offset false x tm<d)%R.
    rewrite /curve_side_offset /=; apply/andP; split; lra.
  have hdist := hbound tm ht; rewrite lee_fin in hdist.
  lra.
have hr := @arc_length_le_left R Y g hg u x hux.
rewrite -(@arc_length_increment R Y g hg u x (ltW hux)) lee_fin in hV.
lra.
Qed.

(** Source for [curve_right_jump_arc_length]: direct supporting
    identification alpha_+(x)=s(x+)-s(x) for the locally BV
    case of 2.10.14, p. 177. The scalar right limit exists
    by 2.5.16, p. 109, even for an incomplete metric target. *)
Theorem curve_right_jump_arc_length (R : realType) (Y : metricType R)
    (g : R -> Y) (x : R) : curve_locally_finite_variation g ->
  curve_right_jump_size g x=((arc_length_right g x-arc_length g x)%R)%:E.
Proof.
move=> hg; apply/eqP; rewrite eq_le (curve_right_jump_arc_length_upper x hg) /=.
exact: curve_right_jump_arc_length_lower x hg.
Qed.

(** Source for [curve_left_jump_arc_length]: direct supporting
    identification alpha_-(x)=s(x)-s(x-) for the locally BV
    case of 2.10.14, p. 177. This is the left-hand scalar
    jump from 2.5.16, p. 109, with no target completeness. *)
Theorem curve_left_jump_arc_length (R : realType) (Y : metricType R)
    (g : R -> Y) (x : R) : curve_locally_finite_variation g ->
  curve_left_jump_size g x=((arc_length g x-arc_length_left g x)%R)%:E.
Proof.
move=> hg; apply/eqP; rewrite eq_le (curve_left_jump_arc_length_upper x hg) /=.
exact: curve_left_jump_arc_length_lower x hg.
Qed.
