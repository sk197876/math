(** Federer (1969), 2.8.9, p. 146, first example: x = a + [N(c-a)/N(b-a)]
    (b-a), and rho(x,c)/rho(a,c) is the distance between the unit
    directions. This works for every norm; strict convexity is unnecessary
    for existence of this particular radial point. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals topology lra.
From Federer Require Import RealNormUP NormMetric DirectionalLimitationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section Directions.
Variable R : realType.
Variable V : lmodType R.
Variable N : V -> R.
Hypothesis hN : is_real_norm N.
Local Notation M := (real_norm_metric_space hN).

(** Source for [norm_direction]: the direction (b-a)/N(b-a) in Federer
    2.8.9, p. 146 *)
Definition norm_direction (a b : M) : M := (N (b-a))^-1 *: (b-a).

(** Source for [norm_direction_unit]: the directions lie on
    the unit sphere, Federer 2.8.9, p. 146. Supporting
    consequence of positive definiteness and homogeneity. *)
Lemma norm_direction_unit (a b : M) : b <> a -> N (norm_direction a b) = 1.
Proof.
move=> hba.
have hp : 0 < N (b-a).
  rewrite (real_norm_positive hN.1 hN.2) subr_eq0.
  by apply/eqP.
rewrite /norm_direction (real_seminorm_scale hN.1) gtr0_norm ?invr_gt0 //.
by rewrite mulVf //; exact: lt0r_neq0.
Qed.

(** Source for [norm_radial_projection]: the explicit radial
    point and distance ratio in Federer 2.8.9, p. 146.
    The equations are proved from the norm laws, so the result
    applies also to norms whose radial projection is not unique. *)
Lemma norm_radial_projection (a b c : M) : b <> a -> c <> a ->
    mdist a c <= mdist a b ->
  exists x : M, is_radial_projection_configuration a b c x /\
    mdist x c / mdist a c = mdist (norm_direction a b) (norm_direction a c).
Proof.
move=> hba hca horder.
have hp v : v <> a -> 0 < N (v-a).
  move=> hva; rewrite (real_norm_positive hN.1 hN.2) subr_eq0.
  by apply/eqP.
have hB := hp b hba; have hC := hp c hca.
have hB0 : N (b-a) != 0 := lt0r_neq0 hB.
have hC0 : N (c-a) != 0 := lt0r_neq0 hC.
have hCB : N (c-a) <= N (b-a).
  by move: horder; rewrite !real_norm_metric_distanceE !(real_seminorm_subtract hN.1 a).
pose q := N (c-a) / N (b-a).
have hq : 0 < q by rewrite /q divr_gt0.
have hq1 : q <= 1 by rewrite /q ler_pdivrMr // mul1r.
pose x : M := a + q *: (b-a).
have hx : x-a = q *: (b-a) by rewrite /x addrC addKr.
have hxb : b-x = (1-q) *: (b-a).
  rewrite /x opprD addrA scalerBl scale1r; reflexivity.
have hxc : x-c = N (c-a) *: (norm_direction a b - norm_direction a c).
  rewrite /norm_direction scalerBr !scalerA mulfV // scale1r.
  by rewrite /x /q opprB !addrA [a + _]addrC.
exists x; split.
- split=> //; split.
  + rewrite real_norm_metric_distanceE (real_seminorm_subtract hN.1) hx
      (real_seminorm_scale hN.1) gtr0_norm // /q divfK //.
    by rewrite real_norm_metric_distanceE (real_seminorm_subtract hN.1).
  + rewrite real_norm_metric_distanceE (real_seminorm_subtract hN.1) hxb
      (real_seminorm_scale hN.1) ger0_norm ?subr_ge0 // mulrBl mul1r /q divfK //.
    by rewrite !real_norm_metric_distanceE !(real_seminorm_subtract hN.1 a).
- rewrite !real_norm_metric_distanceE (real_seminorm_subtract hN.1 a) hxc
    (real_seminorm_scale hN.1) gtr0_norm //.
  by rewrite mulrAC mulfV // mul1r.
Qed.

(** Source for [separated_norm_directions]: the distance between directions
    is at least eta for each pair of distinct b,c in the separated set of
    Federer 2.8.9, p. 146. The radial points of [norm_radial_projection] are
    used in Federer's quantified condition. Supporting lemma *)
Lemma separated_norm_directions (a : M) (eta : R) (B : set M) :
  B `<=` ~` [set a] -> directionally_separated_from a eta B ->
  forall b c, B b -> B c -> b <> c ->
    eta <= mdist (norm_direction a b) (norm_direction a c).
Proof.
move=> hB hs b c hb hc hbc.
have hba : b <> a := hB b hb.
have hca : c <> a := hB c hc.
case: (leP (mdist a c) (mdist a b))=> [hcb|hcb].
- have [x [hx he]] := norm_radial_projection hba hca hcb.
  rewrite -he; exact: hs b c hb hc hbc x hx.
- have [x [hx he]] := norm_radial_projection hca hba (ltW hcb).
  have hcbne : c <> b by move=> h; apply: hbc; exact: esym h.
  have h := hs c b hc hb hcbne x hx.
  by rewrite he (metric_sym (norm_direction a c) (norm_direction a b)) in h.
Qed.
End Directions.
