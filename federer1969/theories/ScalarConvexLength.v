(** Supporting segment argument for the degree-one gauge identity in Federer
    (1969), 2.10.4, p. 172. A convex scalar set contains the interval
    between any two of its points, so its Lebesgue measure bounds their
    distance. Use the actual segment-length law of 2.5.17, p. 111. This is a
    proof ingredient, not an extra numbered claim. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From mathcomp Require Import lra.
From Federer Require Import InnerConvex LebesgueScalarMeasure MeasureUP MeasureBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [linear_image_inner_convex]: supporting
    convexity of projection images for Federer 2.10.4,
    p. 172, from linearity and the defining segment
    property, with no topological or dimension premise. *)
Lemma linear_image_inner_convex (R : realFieldType) (V W : lmodType R)
    (f : {linear V -> W}) (A : set V) : is_inner_convex A -> is_inner_convex (f @` A).
Proof.
move=> hc _ _ [x hx <-] [y hy <-] t ht0 ht1.
exists ((1-t)*:x+t*:y); first exact: hc x y hx hy t ht0 ht1.
by rewrite linearD !linearZ.
Qed.

(** Source for [real_convex_contains_segment]: supporting
    interval inclusion in the degree-one observation
    of Federer 2.10.4, p. 172. Coincident
    endpoints are handled explicitly. *)
Lemma real_convex_contains_segment (R : realType) (C : set R) (a b : R) :
  @is_inner_convex R R^o C -> C a -> C b -> a<=b -> `[a,b] `<=` C.
Proof.
move=> hc ha hb hab z; rewrite /= in_itv /= => /andP[haz hzb].
case: (eqVneq a b)=> [he|hne].
- have hz : z=a.
    apply/eqP; rewrite eq_le; apply/andP; split; [by rewrite he|exact haz].
  by rewrite hz.
have hba : 0<b-a by rewrite subr_gt0 lt_neqAle hne hab.
pose t := (z-a)/(b-a).
have ht0 : 0<=t by rewrite /t divr_ge0 // subr_ge0.
have ht1 : t<=1 by rewrite /t ler_pdivrMr // mul1r lerD2r.
have heq : (1-t)*a+t*b=z.
  have he : (1-t)*a+t*b=a+t*(b-a) by lra.
  rewrite he /t divfK ?gt_eqF //; by rewrite addrC subrK.
have hh := hc a b ha hb t ht0 ht1.
change (C ((1-t)*a+t*b)) in hh; by rewrite heq in hh.
Qed.

(** Source for [real_convex_pair_length_bound]: supporting
    Lebesgue-length lower bound for projected convex
    sets in Federer 2.10.4, p. 172. No
    measurability or boundedness of C is assumed. *)
Theorem real_convex_pair_length_bound (R : realType) (C : set R) (a b : R) :
  @is_inner_convex R R^o C -> C a -> C b -> (`|a-b|%:E<=lebesgue_scalar_measure C)%E.
Proof.
move=> hc ha hb.
case: (leP a b)=> hab.
- have hh := @measure_mono R R (@lebesgue_scalar_measure R) (lebesgue_scalar_is_measure R)
    `[a,b] C (real_convex_contains_segment hc ha hb hab).
  rewrite (lebesgue_scalar_segment hab) in hh.
  by rewrite -[a-b]opprB normrN ger0_norm // subr_ge0.
- have hba := ltW hab.
  have hh := @measure_mono R R (@lebesgue_scalar_measure R) (lebesgue_scalar_is_measure R)
    `[b,a] C (real_convex_contains_segment hc hb ha hba).
  rewrite (lebesgue_scalar_segment hba) in hh.
  by rewrite ger0_norm // subr_ge0.
Qed.
