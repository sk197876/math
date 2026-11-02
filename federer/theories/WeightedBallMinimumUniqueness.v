(** Federer (1969), 2.10.40, printed p. 200: the parallelogram identity and
    a uniform radius bound force any two minimum-scale feasible centres to
    coincide. Derive this from the abstract minimum laws, not from its
    private existence witness. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets topology lra.
From Federer Require Import EuclideanInnerProduct InnerProductUP InnerNorm InnerMetric
  InnerMidpointParallelogram WeightedBallMinimumUP WeightedBallParameterBounds WeightedMidpointScale.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [weighted_ball_midpoint_square_bound]: direct
    parallelogram inequality in the uniqueness computation
    of 2.10.40, p. 200. The squared separation
    subtracts a uniform positive amount before normalising
    by the prescribed radius. *)
Lemma weighted_ball_midpoint_square_bound (R : realType) n P (c : R)
    (y z : inner_metric_space (@euclidean_inner_productP R n)) :
  0<=c -> positive_ball_parameter_family P ->
  weighted_ball_centres P c y -> weighted_ball_centres P c z ->
  forall p, P p ->
    4*inner_norm (@euclidean_inner_productP R n) ((2:R)^-1*:(y+z)-p.1)^+2+
      inner_norm (@euclidean_inner_productP R n) (y-z)^+2<=4* p.2^+2*c^+2.
Proof.
move=> hc hP hy hz p hp.
pose N := inner_norm (@euclidean_inner_productP R n).
have hrc : 0<=p.2*c := mulr_ge0 (ltW (hP p hp)) hc.
have hysq : N (y-p.1)^+2<=(p.2*c)^+2.
  by rewrite (ler_sqr (inner_norm_nonnegative _ _) hrc); exact: hy p hp.
have hzsq : N (z-p.1)^+2<=(p.2*c)^+2.
  by rewrite (ler_sqr (inner_norm_nonnegative _ _) hrc); exact: hz p hp.
have hh := @inner_midpoint_parallelogram R _ _ (@euclidean_inner_productP R n) p.1 y z.
rewrite -[p.1-(2:R)^-1*:(y+z)]opprB inner_normN
  -[p.1-y]opprB inner_normN -[p.1-z]opprB inner_normN in hh.
rewrite exprMn in hysq hzsq.
change (4*N ((2:R)^-1*:(y+z)-p.1)^+2+N (y-z)^+2=
  2*(N (y-p.1)^+2+N (z-p.1)^+2)) in hh.
change (is_true (4*N ((2:R)^-1*:(y+z)-p.1)^+2+N (y-z)^+2<=4* p.2^+2*c^+2)).
nra.
Qed.

(** Source for [weighted_ball_minimum_centres_unique]: direct
    singleton conclusion for Y_c in 2.10.40,
    pp. 199–200, from the abstract least-scale laws.
    Compactness supplies the uniform finite radius bound;
    zero minimum scale and dimension zero are included. *)
Theorem weighted_ball_minimum_centres_unique (R : realType) n
    (P : set ((inner_metric_space (@euclidean_inner_productP R n))*R^o))
    (D : weighted_ball_minimum_data R n) :
  compact P -> P !=set0 -> positive_ball_parameter_family P ->
  is_weighted_ball_minimum P D -> forall y z,
    weighted_ball_centres P (weighted_minimum_scale D) y ->
    weighted_ball_centres P (weighted_minimum_scale D) z -> y=z.
Proof.
move=> hP hne hpos hD y z hy hz.
case: (eqVneq y z)=> [he|hneYZ]; first exact he.
pose N := inner_norm (@euclidean_inner_productP R n).
pose c := weighted_minimum_scale D.
pose sep := N (y-z).
have hsep : 0<sep by rewrite /sep inner_norm_gt0 subr_eq0.
have hc := weighted_minimum_scale_nonnegative_law hD.
have [lo [mu [_ [hmu hr]]]] := @compact_positive_ball_radius_bounds R n P hP hne hpos.
have hmid := @weighted_ball_midpoint_square_bound R n P c y z hc hpos hy hz.
have [p0 hp0] := hne.
have hp0r := hpos p0 hp0.
have /andP [_ hrmu] := hr p0 hp0.
have hrr : p0.2^+2<=mu^+2 by rewrite (ler_sqr (ltW hp0r) (ltW hmu)).
have hprod := ler_wpM2r (sqr_ge0 c) hrr.
have hm0 := hmid p0 hp0.
change (is_true (4*N ((2:R)^-1*:(y+z)-p0.1)^+2+sep^+2<=4* p0.2^+2*c^+2)) in hm0.
have hn0 := sqr_ge0 (N ((2:R)^-1*:(y+z)-p0.1)).
have hsepbound : sep^+2<=4*mu^+2*c^+2 by nra.
have [t [ht [htc hshrink]]] := @weighted_midpoint_strict_scale R c mu sep hc hmu hsep hsepbound.
have hfeasible : weighted_ball_centres P t ((2:R)^-1*:(y+z)).
  move=> p hp; have /andP [_ hrp] := hr p hp.
  exact (hshrink p.2 (N ((2:R)^-1*:(y+z)-p.1)) (hpos p hp) hrp
    (inner_norm_nonnegative _ _) (hmid p hp)).
have hleast := @weighted_minimum_least_law R n P D hD t ((2:R)^-1*:(y+z)) ht hfeasible.
have hfalse := lt_le_trans htc hleast; by rewrite ltxx in hfalse.
Qed.
