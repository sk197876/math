(** Federer (1969), 3.2.18, p. 255:
    agreeing differentiable representatives on a
    full-density source set have the same
    differential. This justifies the differential
    bounds after a Kirszbraun extension, rather
    than assuming that every extension preserves them. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  RealNormUP HilbertFormCompactness NormDifferentialUP PartialFunctionUP
  EuclideanLebesgueDimensions CenteredBallRelations MeasureSetDensity
  TangentConeUP TangentConeBasic EuclideanFullDensityTangent NormVanishingTangent.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_differentials_agree_on_full_density]:
    the derivative agreement needed when combining
    3.2.2 and 2.10.43 in Federer
    3.2.18, p. 255. Equality on
    the density-one set determines every source
    direction; no differentiability of an extension
    is inferred from agreement alone. *)
Theorem euclidean_differentials_agree_on_full_density (R : realType) m
    (Y : lmodType R) (NY : Y -> R) (hNY : is_real_norm NY)
    (S : set (R_n R m)) (f g : R_n R m -> Y) a
    (D E : Hom (R_n R m) Y) :
  (forall x, S x -> f x=g x) ->
  partial_function_graph (measure_set_density (@euclidean_lebesgue_measure R m)
    (@centered_closed_ball_relation R
      [the metricType R of inner_metric_space (@euclidean_inner_productP R m)]) (~` S)) a 0%E ->
  has_norm_differential (inner_norm (@euclidean_inner_productP R m)) NY setT f a D ->
  has_norm_differential (inner_norm (@euclidean_inner_productP R m)) NY setT g a E -> D=E.
Proof.
move=> hAgree hFull hD hE.
pose NX := inner_norm (@euclidean_inner_productP R m).
pose hNX := inner_norm_real_norm (@euclidean_inner_productP R m).
have hTan := euclidean_full_density_tangent hFull.
have hZero : norm_tangent_cone NX S a 0 by rewrite hTan.
have hcl := @norm_tangent_base_closure R (R_n R m) NX hNX S a 0 hZero.
have hDE := @norm_differentials_agree_on_tangent R (R_n R m) Y NX NY hNX hNY
  setT setT S f g a D E hD hE hcl (fun x hx _ _=>hAgree x hx).
apply: hom_ext=> v; apply: hDE; by rewrite hTan.
Qed.
