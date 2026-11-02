(** Federer (1969), 3.2.35, p. 271:
    the actual unit sphere is finitely rectifiable,
    using the compact one-frame Stiefel manifold
    already proved in 3.2.28, pp. 263--267. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets topology.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerNorm InnerMetric
  EuclideanHomInnerCharts OrthogonalMaps EuclideanStiefelSmooth EuclideanStiefelCompact
  FiniteInnerSmoothSubmanifoldUP FiniteInnerCompactSubmanifold EuclideanOneFrameSphere
  RectifiableSetUP LipschitzUP LipschitzRectifiableImages.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_unit_sphere_rectifiable]: the
    finite rectifiable sphere used in the boundary
    parametrization of Federer 3.2.35, p. 271.
    The compact O(n,1) manifold from 3.2.28,
    pp. 263--267, has dimension n-1. Its
    actual evaluation isometry onto the unit sphere
    transfers genuine finite rectifiability. At n=1
    the two points use the finite-set degree-zero
    convention of 3.2.14, p. 252; at n=0
    the sphere is empty. *)
Theorem euclidean_unit_sphere_rectifiable (R:realType) n:
  @is_m_rectifiable R (inner_metric_space (@euclidean_inner_productP R n)) (n-1)
    [set y|inner_norm (@euclidean_inner_productP R n) y= 1].
Proof.
have hDimension:(1*(2*n-1-1)%/2=n-1)%N.
  case:n=>[|k]; first by [].
  by rewrite mul1n mulnS ?add2n ?addn2 !subn1 mulnC mulnK.
pose X:=inner_metric_space (@euclidean_hom_inner_productP R 1 n).
pose Y:=inner_metric_space (@euclidean_inner_productP R n).
pose O:set X:=[set g|is_orthogonal_map (@euclidean_inner_product R 1)
  (@euclidean_inner_product R n) (hom_as_linear g)].
have hClass:=inner_smooth_submanifold_class (@euclidean_stiefel_smooth_submanifold R 1 n) 1%N.
have hRect:=@finite_inner_compact_submanifold_rectifiable R
  (Hom (R_n R 1) (R_n R n)) (@euclidean_hom_inner_product R 1 n)
  (@euclidean_hom_inner_productP R 1 n) (1*(2*n-1-1)%/2)%N 1 O O
  (leqnn 1) hClass (fun x hx=>hx) (@euclidean_stiefel_compact R 1 n).
rewrite hDimension in hRect.
have hLip:@is_metric_lipschitz R X Y O (fun g=>g (@coordinate_basis R 1 ord0)).
  exists 1; split; first exact:ltr01.
  split; first exact:ler01.
  move=>g h _ _; rewrite !inner_metric_distanceE mul1r.
  have hNorm:=@euclidean_one_frame_evaluation_norm R n (g-h).
  change (inner_norm (@euclidean_hom_inner_productP R 1 n) (g-h)=
    inner_norm (@euclidean_inner_productP R n)
      (g (@coordinate_basis R 1 ord0)-h (@coordinate_basis R 1 ord0))) in hNorm.
  by rewrite hNorm.
have hResult:=@rectifiable_lipschitz_image R X Y (n-1) O
  (fun g=>g (@coordinate_basis R 1 ord0)) hLip hRect.
by rewrite (@euclidean_one_frame_sphere_image R n) in hResult.
Qed.
