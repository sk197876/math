(** Federer (1969), 3.1.24, p. 240: approximate
    differentiation shows that all derivatives vanish on the
    density-one part of an analytic zero set. This is the
    first-order supporting implication, with an arbitrary normed target. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerNormInequalities HilbertFormCompactness InnerMetric
  RealNormUP EuclideanLebesgueDimensions CenteredBallRelations PartialFunctionUP MeasureSetDensity
  NormDifferentialUP NormDifferentialLinear NormDifferentialLocalAgreement
  OrdinaryDifferentialOnDensityDomain ApproximateDifferentialUniqueness.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [norm_differential_zero_on_density_set]: supporting
    Z contained in W in Federer 3.1.24, p. 240.
    If a differentiable function vanishes on a set of density
    one at a, its differential at a is zero. The actual
    open differentiability domain may be larger than that set;
    positive Euclidean dimension is explicit because the project's
    punctured approximate quotient is empty in dimension zero. *)
Theorem norm_differential_zero_on_density_set (R:realType) n
    (Y:lmodType R) (NY:Y->R) (hNY:is_real_norm NY)
    (A S:set (R_n R n.+1)) (f:R_n R n.+1->Y) a (L:Hom (R_n R n.+1) Y) :
  S a -> (forall x,S x -> f x=0) ->
  partial_function_graph
    (measure_set_density (@euclidean_lebesgue_measure R n.+1)
      (@centered_closed_ball_relation R
        [the metricType R of inner_metric_space (@euclidean_inner_productP R n.+1)])
      (~` S)) a 0%E ->
  has_norm_differential (inner_norm (@euclidean_inner_productP R n.+1)) NY A f a L -> L=0.
Proof.
move=>ha hS hden hL.
pose NX:=inner_norm (@euclidean_inner_productP R n.+1).
have hNX:=inner_norm_real_norm (@euclidean_inner_productP R n.+1).
have [r [hr hball]]:=norm_differential_interior hL.
have hglobal:has_norm_differential NX NY setT f a L.
  apply: (@norm_differential_local_agreement R (R_n R n.+1) Y NX NY hNX
    A setT f f a L r hr _ _ hL).
  - move=>v hv; split=>_; last exact (hball v hv); exact Logic.I.
  - by move=>v hv hA.
have hap:=@ordinary_differential_on_density_domain R n Y NY hNY S f f a L
  (fun x hx=>erefl) ha hden hglobal.
have hwhole:norm_domain_interior NX setT a.
  exists 1; split; first exact ltr01; by move=>v hv.
have hz:=@norm_differential_constant R (R_n R n.+1) Y NX NY hNX hNY setT a 0 hwhole.
have hap0:=@ordinary_differential_on_density_domain R n Y NY hNY S f (fun _=>0) a 0
  hS ha hden hz.
exact (@approximate_differential_unique R n.+1 Y NY hNY S f a L 0 hap hap0).
Qed.
