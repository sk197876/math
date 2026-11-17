(** Federer (1969), 3.4.8(10), pp. 331–332:
    retain the original ambient dimension n
    in the prescribed projection chart.
    The proved joint-coordinate theorem uses
    the equivalent indexing n=m+(n-m). *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormAnalyticUP NormCoordinateSystemUP
  GrassmannAbbreviations EuclideanInnerProduct InnerNorm HilbertFormCompactness InnerConvex AnalyticEquationProjectionChart.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [analytic_equation_projection_chart_any_dimension]:
    the original m-dimensional chart in
    R^n, 3.4.8(10), pp. 331–332.
    This index connection changes no vector,
    equation, projection or theorem hypothesis. *)
Theorem analytic_equation_projection_chart_any_dimension (R:realType) n m (hMN:(m<=n)%N):
  forall (A Z:set (R_n R n)) (P:Hom (R_n R n) (R_n R m))
    (f:'I_(n-m)->R_n R n->R) (delta:R_n R n->R),
  norm_bounded_linear (inner_norm (@euclidean_inner_productP R n))
    (inner_norm (@euclidean_inner_productP R m)) P ->
  (forall j,@norm_analytic R (R_n R n) R^o (inner_norm (@euclidean_inner_productP R n))
    (fun t:R^o=>`|t|) (inner_norm_real_norm (@euclidean_inner_productP R n))
    (@scalar_absolute_value_norm R) A (f j)) ->
  @norm_analytic R (R_n R n) R^o (inner_norm (@euclidean_inner_productP R n))
    (fun t:R^o=>`|t|) (inner_norm_real_norm (@euclidean_inner_productP R n))
    (@scalar_absolute_value_norm R) A delta ->
  (forall x,Z x <->A x /\(forall j,f j x = 0) /\delta x<>0) ->
  (forall a,Z a ->exists D:'I_(n-m)->Hom (R_n R n) R^o,
    (forall j,has_norm_differential (inner_norm (@euclidean_inner_productP R n))
      (fun t:R^o=>`|t|) A (f j) a (D j)) /\
    forall u,P u = 0 ->(forall j,D j u = 0) ->u=0) ->
  forall a,Z a ->exists (U:set (R_n R n)) (V:set (R_n R m)) (psi:R_n R m->R_n R n),
    U a /\(forall x,U x ->A x /\delta x<>0) /\is_inner_convex V /\
    @norm_analytic R (R_n R n) (R_n R m) (inner_norm (@euclidean_inner_productP R n))
      (inner_norm (@euclidean_inner_productP R m)) (inner_norm_real_norm (@euclidean_inner_productP R n))
      (inner_norm_real_norm (@euclidean_inner_productP R m)) U P /\
    @norm_analytic R (R_n R m) (R_n R n) (inner_norm (@euclidean_inner_productP R m))
      (inner_norm (@euclidean_inner_productP R n)) (inner_norm_real_norm (@euclidean_inner_productP R m))
      (inner_norm_real_norm (@euclidean_inner_productP R n)) V psi /\
    is_norm_coordinate_system (inner_norm_real_norm (@euclidean_inner_productP R n))
      (inner_norm_real_norm (@euclidean_inner_productP R m)) Z U V P psi 1%N.
Proof.
have hSize:n=(m+(n-m))%N by rewrite subnKC.
rewrite hSize addKn.
move=>A Z P f delta hP hF hDelta hZ hJoint a ha.
exact:(@analytic_equation_projection_chart R m (n-m) A Z P hP f delta hF hDelta hZ hJoint a ha).
Qed.
