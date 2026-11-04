(** Federer (1969), 3.2.47, pp. 282–283: the
    actual unit sphere is the smooth homogeneous-space target.
    Its exact identification with the one-frame Stiefel manifold
    from 3.2.28, p. 267, proves common smooth local
    charts in the original Euclidean norm. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets topology.
From Federer Require Import Hom TensorUP GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct InnerNorm InnerMetric OrthogonalMaps EuclideanHomInnerCharts
  EuclideanStiefelSmooth EuclideanOneFrameSphere UnitSphereSpace
  FiniteInnerChartUP FiniteInnerSmoothSubmanifoldUP FiniteInnerIsometricSmoothSubmanifold.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [spherical_unit_sphere_smooth]: the actual
    unit sphere has dimension N-1 and common smooth
    local charts of every order, supporting the target
    geometry of 3.2.47, p. 283. N=1 retains
    the two-point sphere; N=0 is the empty set. *)
Theorem spherical_unit_sphere_smooth (R:realType) N:
  is_inner_smooth_submanifold (@euclidean_inner_product R N) (N-1)%N
    (@euclidean_unit_sphere_set R N).
Proof.
have hDimension:(1*(2*N-1-1)%/2=N-1)%N.
  case:N=>[|n]; first by [].
  by rewrite mul1n mulnS ?add2n ?addn2 !subn1 mulnC mulnK.
pose V:=R_n R N.
pose H:=Hom (R_n R 1) V.
pose hH:=@euclidean_hom_inner_productP R 1 N.
pose hV:=@euclidean_inner_productP R N.
pose O:set H:=[set g|is_orthogonal_map (@euclidean_inner_product R 1)
  (@euclidean_inner_product R N) (hom_as_linear g)].
pose F:=fun g:H=>g (@coordinate_basis R 1 ord0).
pose idV:Hom V V:=hom_of_linear (linear_id V).
have hIdentity:is_finite_inner_chart (@euclidean_inner_product R N) idV idV.
  constructor; [by move=>x|by move=>x|by move=>x y].
have hSource:=@euclidean_stiefel_smooth_submanifold R 1 N.
rewrite hDimension in hSource.
have hMetric (g h:H):mdist (F g:inner_metric_space hV) (F h)=
    mdist (g:inner_metric_space hH) h.
  rewrite !inner_metric_distanceE.
  have hNorm:=@euclidean_one_frame_evaluation_norm R N (g-h).
  change (inner_norm hH (g-h)=inner_norm hV
    (g (@coordinate_basis R 1 ord0)-h (@coordinate_basis R 1 ord0))) in hNorm.
  exact:esym hNorm.
have hResult:=@finite_inner_isometric_smooth_submanifold_image R H V _ _ hH hV
  (N-1)%N O F N idV idV hIdentity hSource hMetric.
by rewrite (@euclidean_one_frame_sphere_image R N) in hResult.
Qed.
