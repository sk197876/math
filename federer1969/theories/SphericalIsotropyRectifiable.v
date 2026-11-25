(** Federer (1969), 3.2.47, pp. 282–283: the
    actual isotropy is compact and genuinely mu rectifiable.
    These facts follow from the proved isometry with O(n-1),
    its actual compact smooth manifold, and Lipschitz image laws. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  OrthogonalMaps EuclideanHomInnerCharts EuclideanStiefelSmooth EuclideanStiefelCompact
  FiniteInnerSmoothSubmanifoldUP FiniteInnerCompactSubmanifold RectifiableSetUP
  LipschitzUP LipschitzBasic NormMetricScaleContinuity LipschitzRectifiableImages
  SphericalOrthogonalProductAlgebra SphericalIsotropyIsometry.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [spherical_isotropy_compact_rectifiable]: the actual
    original I is compact and mu rectifiable, as
    used in 3.2.47(1),(2), p. 283. The degree
    is mu=n(n-1)/2 for ambient dimension n+1;
    zero degree uses the printed finite-set convention. *)
Theorem spherical_isotropy_compact_rectifiable (R:realType) n (c:R_n R (1+n)):
  inner_norm (@euclidean_inner_productP R (1+n)) c= 1 ->
  @compact [the topologicalType of inner_metric_space (@euclidean_hom_inner_productP R (1+n) (1+n))]
    (spherical_orthogonal_isotropy c) /\
  @is_m_rectifiable R (inner_metric_space (@euclidean_hom_inner_productP R (1+n) (1+n)))
    (n*(n-1)%/2)%N (spherical_orthogonal_isotropy c).
Proof.
move=>hc.
pose X:=inner_metric_space (@euclidean_hom_inner_productP R n n).
pose Y:=inner_metric_space (@euclidean_hom_inner_productP R (1+n) (1+n)).
pose O:set X:=[set h|is_orthogonal_map (@euclidean_inner_product R n)
  (@euclidean_inner_product R n) (hom_as_linear h)].
have [F [G [hCancel [hDistance hImage]]]]:=@spherical_isotropy_isometric_parametrization R n c hc.
have hD (h g:X):@mdist R Y (F h) (F g)=mdist h g.
  rewrite !inner_metric_distanceE; exact:hDistance.
have hLip:is_metric_lipschitz O (F:X->Y).
  apply:metric_lipschitz_of_bound; split; first exact:ler01.
  by move=>h g _ _; rewrite hD mul1r.
have hCompact:@compact [the topologicalType of X] O:=@euclidean_stiefel_compact R n n.
have hContinuous:continuous (F:X->Y).
  apply:(@metric_fixed_lipschitz_continuous R X Y F 1 ler01).
  by move=>h g; rewrite hD mul1r.
have hRect:@is_m_rectifiable R X (n*(2*n-n-1)%/2)%N O.
  apply:(@finite_inner_compact_submanifold_rectifiable R (Hom (R_n R n) (R_n R n))
    _ (@euclidean_hom_inner_productP R n n) (n*(2*n-n-1)%/2)%N 1 O O (leqnn 1)).
  - exact:inner_smooth_submanifold_class (@euclidean_stiefel_smooth_submanifold R n n) 1%N.
  - exact:subset_refl.
  - exact hCompact.
have hDegree:(n*(2*n-n-1)%/2=n*(n-1)%/2)%N by rewrite mul2n -addnn addKn.
rewrite hDegree in hRect.
have hImageCompact:=continuous_compact (continuous_subspaceT hContinuous) hCompact.
have hImageRectifiable:=@rectifiable_lipschitz_image R X Y (n*(n-1)%/2)%N O F hLip hRect.
by rewrite hImage in hImageCompact hImageRectifiable; split.
Qed.
