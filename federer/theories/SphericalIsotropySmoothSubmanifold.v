(** Federer (1969), 3.2.47, p. 283: the actual
    isotropy I is a mu-dimensional submanifold in the
    original Hilbert Hom ambient space. Its proved isometry
    with O(n-1) and the actual ambient isometric-image theorem
    give common local charts of every finite order. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct
  InnerNorm InnerMetric EuclideanHomInnerCharts EuclideanStiefelSmooth
  FiniteInnerChartUP FiniteInnerSubmanifoldUP FiniteInnerSmoothSubmanifoldUP
  FiniteInnerIsometricSmoothSubmanifold SphericalOrthogonalProductAlgebra SphericalIsotropyIsometry.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [spherical_isotropy_smooth_submanifold]: the actual
    dimension and smooth charts of I,
    as used in 3.2.47, p. 283. The ambient
    metric, base point and whole original isotropy are retained;
    isometric coordinates are proved to exist locally. *)
Theorem spherical_isotropy_smooth_submanifold (R:realType) n (c:R_n R (1+n)):
  inner_norm (@euclidean_inner_productP R (1+n)) c= 1 ->
  is_inner_smooth_submanifold (@euclidean_hom_inner_product R (1+n) (1+n))
    (n*(n-1)%/2)%N (spherical_orthogonal_isotropy c).
Proof.
move=>hc.
have [F [G [hCancel [hDistance hImage]]]]:=@spherical_isotropy_isometric_parametrization R n c hc.
have [eY [pY hTarget]]:=@euclidean_hom_inner_chart_exists R (1+n) (1+n).
have hSource:=@euclidean_stiefel_smooth_submanifold R n n.
have hDegree:(n*(2*n-n-1)%/2=n*(n-1)%/2)%N.
  by rewrite mul2n -addnn addKn.
rewrite hDegree in hSource.
have hMetric x y:
    mdist (F x:inner_metric_space (@euclidean_hom_inner_productP R (1+n) (1+n))) (F y)=
    mdist (x:inner_metric_space (@euclidean_hom_inner_productP R n n)) y.
  rewrite !inner_metric_distanceE; exact:hDistance x y.
have hResult:=@finite_inner_isometric_smooth_submanifold_image R
  (Hom (R_n R n) (R_n R n)) (Hom (R_n R (1+n)) (R_n R (1+n))) _ _
  (@euclidean_hom_inner_productP R n n) (@euclidean_hom_inner_productP R (1+n) (1+n))
  (n*(n-1)%/2)%N _ F ((1+n)*(1+n))%N eY pY hTarget hSource hMetric.
by rewrite hImage in hResult.
Qed.
