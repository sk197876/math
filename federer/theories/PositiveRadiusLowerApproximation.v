(** Federer (1969), 3.2.17, p. 254:
    infer lower density bounds from uniform
    small-radius estimates approaching the proposed
    finite bound. These are consequences of the
    abstract extended infimum and supremum laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal lra.
From Federer Require Import ExtendedRealBounds PositiveRadiusLimits.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [positive_radius_lower_eventual_bound]:
    supporting lower-limit step in the first
    conclusion of Federer 3.2.17, p. 254.
    A bound on one positive neighbourhood of
    radii is a bound for the liminf. *)
Lemma positive_radius_lower_eventual_bound (R : realType) (f : R -> \bar R) b (d : R) :
  (0<d)%R -> (forall r : R, (0<r<d)%R -> b<=f r) ->
  b<=positive_radius_lower_limit f.
Proof.
move=> hd hb; apply: (le_trans _ (positive_radius_lower_ge_level f hd)).
apply: extended_real_inf_greatest=> y [r [hr ->]]; exact: hb r hr.
Qed.

(** Source for [positive_radius_lower_approximate_bound]:
    arbitrarily accurate finite lower estimates
    imply the limiting lower bound in Federer
    3.2.17, p. 254. No finiteness
    of the function values is assumed. *)
Theorem positive_radius_lower_approximate_bound (R : realType)
    (f : R -> \bar R) (b : R) :
  (forall e : R, (0<e)%R -> exists d : R, (0<d)%R /\
    forall r : R, (0<r<d)%R -> (b-e)%R%:E<=f r) ->
  b%:E<=positive_radius_lower_limit f.
Proof.
move=> hSmall.
have hEach (e : R) (he : (0<e)%R) : (b-e)%R%:E<=positive_radius_lower_limit f.
  have [d [hd hs]] := hSmall e he.
  exact: (positive_radius_lower_eventual_bound hd hs).
case heq : (positive_radius_lower_limit f)=> [v| |].
- rewrite lee_fin leNgt; apply/negP=> hv.
  have he : (0<(b-v)/2)%R by rewrite divr_gt0 // subr_gt0.
  have hh := hEach _ he; rewrite heq lee_fin in hh.
  clear hEach hSmall heq f; lra.
- exact: leey.
- have hh := hEach 1%R (@ltr01 R); by rewrite heq leNgt ltNyr in hh.
Qed.

(** Source for [positive_radius_lower_scaled_one_bound]:
    the lower comparison by lambda^(-2m)
    times source density one in Federer
    3.2.17, p. 254. The positive
    coefficient is kept abstract in this helper. *)
Lemma positive_radius_lower_scaled_one_bound (R : realType)
    (f : R -> \bar R) (b : R) :
  (0<b)%R ->
  (forall e : R, (0<e)%R -> exists d : R, (0<d)%R /\
    forall r : R, (0<r<d)%R -> ((1-e)*b)%R%:E<=f r) ->
  b%:E<=positive_radius_lower_limit f.
Proof.
move=> hb hSmall; apply: positive_radius_lower_approximate_bound=> e he.
have ht : (0<e/(b+1))%R by rewrite divr_gt0 // ltr_wpDl ?ltW.
have [d [hd hs]] := hSmall _ ht.
exists d; split=> // r hr; apply: (le_trans _ (hs r hr)).
rewrite lee_fin.
have hmul : (e/(b+1)*(b+1)=e)%R by rewrite divfK ?gt_eqF // ltr_wpDl ?ltW.
lra.
Qed.
