(** Supporting compact replacement for Federer (1969), 2.10.3, p. 172: the
    closure of a bounded Euclidean generator is compact. Use the
    finite-basis bounded-compactness theorem already proved for 1.7.1, p.
    28, and unchanged metric diameter under closure from 2.10.2(1), p. 171.
    This is a proof ingredient, not an additional separately numbered
    statement. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct FiniteCoordinates
  InnerNorm InnerNormInequalities InnerMetric InnerBoundedness InnerFiniteCompactness
  MetricDiameterUP MetricDiameter MetricDiameterClosure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_bounded_set_closure_compact]:
    supporting bounded-generator compactification for
    Federer 2.10.3, p. 172. A finite real diameter
    bound and nonemptiness give a norm bound after
    choosing one point. Dimension zero and zero diameter
    are included. *)
Theorem euclidean_bounded_set_closure_compact (R : realType) (n : nat)
    (A : set (inner_metric_space (@euclidean_inner_productP R n))) (d : R) :
  A !=set0 -> (extended_metric_diameter A<=d%:E)%E -> compact (closure A).
Proof.
move=> [a ha] hd.
have hcomp := @inner_finite_basis_boundedly_compact R (R_n R n)
  (@euclidean_inner_product R n) (@euclidean_inner_productP R n)
  n (@coordinate_basis R n) (@coordinate_basisP R n).
apply: hcomp; first exact: closed_closure.
exists (inner_norm (@euclidean_inner_productP R n) a+d)=> x hx.
have hac : closure A a := subset_closure ha.
have hdiam : (extended_metric_diameter (closure A)<=d%:E)%E.
  by rewrite extended_metric_diameter_closure.
have hdist := le_trans (metric_diameter_upper
  (extended_metric_diameter_specification (closure A)) hx hac) hdiam.
have hbound : inner_norm (@euclidean_inner_productP R n) (x-a)<=d.
  by move: hdist; rewrite lee_fin inner_metric_distanceE.
have hh := @inner_norm_triangle R (R_n R n) (@euclidean_inner_product R n)
  (@euclidean_inner_productP R n) (x-a) a.
rewrite subrK in hh; apply: le_trans hh _.
have hb := lerD hbound (lexx (inner_norm (@euclidean_inner_productP R n) a)).
by rewrite [d+_]addrC in hb.
Qed.
