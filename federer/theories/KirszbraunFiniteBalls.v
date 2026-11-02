(** Federer (1969), 2.10.43, printed p. 201: finitely many prescribed balls
    B(f(x),|x-a|) have a common point when f is nonexpanding on the finite
    source and a is a new source point. Apply the sealed minimum of 2.10.40,
    represent its centre by contact centres, lift their source preimages and
    prove the least dilation at most one. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals classical_sets cardinality topology.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerNorm InnerMetric
  WeightedBallMinimumUP WeightedBallMinimum WeightedBallMinimumGeometry WeightedBallContactNonempty
  ConvexHullFiniteSupport KirszbraunBallParameters KirszbraunWeightedScale.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [kirszbraun_finite_ball_intersection]: direct
    finite-intersection assertion in 2.10.43, p. 201.
    Zero weights and repeated contact points are
    allowed in the finite representation; strict
    positivity of the squared source budget replaces
    the printed split between one and several contacts.
    The original finite source may itself be empty. *)
Theorem kirszbraun_finite_ball_intersection (R : realType) m n
    (F : set (inner_metric_space (@euclidean_inner_productP R m)))
    (f : inner_metric_space (@euclidean_inner_productP R m) ->
      inner_metric_space (@euclidean_inner_productP R n))
    (a : inner_metric_space (@euclidean_inner_productP R m)) :
  finite_set F -> (forall x, F x -> x!=a) ->
  (forall x y, F x -> F y -> inner_norm (@euclidean_inner_productP R n) (f x-f y)<=
    inner_norm (@euclidean_inner_productP R m) (x-y)) ->
  exists b, forall x, F x -> inner_norm (@euclidean_inner_productP R n) (b-f x)<=
    inner_norm (@euclidean_inner_productP R m) (x-a).
Proof.
move=> hF hnew hLip.
case: (pselect (F !=set0))=> [hne|hempty]; last first.
  exists 0=> x hx; exfalso; apply: hempty; by exists x.
pose P := kirszbraun_ball_parameters F f a.
have hP : compact P := @kirszbraun_ball_parameters_compact R m n F f a hF.
have hPne : P !=set0 := @kirszbraun_ball_parameters_nonempty R m n F f a hne.
have hpos : positive_ball_parameter_family P := @kirszbraun_ball_parameters_positive R m n F f a hnew.
pose D := @compact_weighted_ball_minimum R n P hP hPne hpos.
have hD := @compact_weighted_ball_minimum_specification R n P hP hPne hpos.
pose b := weighted_minimum_centre D.
pose c := weighted_minimum_scale D.
pose A := weighted_ball_contact_centres P b c.
have hAne : A !=set0 := @weighted_ball_minimum_contacts_nonempty R n P D hP hPne hpos hD.
have hAhull := @weighted_ball_minimum_contact_hull R n P D hP hPne hpos hD.
have [k [v [w [hk [hv [hw [hsum hvalue]]]]]]] :=
  @convex_hull_finite_support R (R_n R n) n (@coordinate_basis R n) A b
    (@coordinate_basisP R n) hAne hAhull.
have hchoice i : exists x, F x /\ v i=f x /\
    inner_norm (@euclidean_inner_productP R n) (v i-b)=
      c*inner_norm (@euclidean_inner_productP R m) (x-a).
  exact (@kirszbraun_contact_source_preimage R m n F f a b (v i) c (hv i)).
pose u i := sval (cid (hchoice i)).
have hu i := svalP (cid (hchoice i)).
have hmean : \sum_i w i*:(v i-b)=0.
  under eq_bigr do rewrite scalerBr.
  by rewrite sumrB -scaler_suml hsum scale1r -hvalue subrr.
have hc : c<=1.
  apply: (@kirszbraun_weighted_contact_scale_le_one R (R_n R m) (R_n R n)
    _ _ (@euclidean_inner_productP R m) (@euclidean_inner_productP R n)
    _ u v w a b c (weighted_minimum_scale_nonnegative_law hD) hw hsum hmean).
  - move=> i; exact: (hu i).2.2.
  - move=> i j; rewrite (hu i).2.1 (hu j).2.1.
    exact: hLip _ _ (hu i).1 (hu j).1.
  - move=> i; exact: hnew _ (hu i).1.
exists b=> x hx.
have hp : P (f x,inner_norm (@euclidean_inner_productP R m) (x-a)).
  exists x; repeat split=> //.
have hh := weighted_minimum_feasible_law hD hp.
apply: le_trans hh _.
have hmul := ler_wpM2l (inner_norm_nonnegative (@euclidean_inner_productP R m) (x-a)) hc.
by rewrite mulr1 in hmul.
Qed.
