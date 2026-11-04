(** Federer (1969), 3.2.48, p. 284: Psi is Lipschitz
    on its actual compact orthogonal-group product. Its ambient
    polynomial need not have a global Lipschitz bound; compactness
    and actual class-one regularity discharge the required premise. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  HilbertFormCompactness EuclideanHomInnerCharts OrthogonalMaps EuclideanStiefelCompact
  ProductInner FiniteInnerCartesianTransfer NormRegularity InnerClassOneCompactLipschitz
  LipschitzUP OrthogonalKinematicMap.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [orthogonal_kinematic_lipschitz]: the actual
    Lipschitz premise for the application of 3.2.22 in
    3.2.48, p. 284. The domain is the original
    full orthogonal-group Cartesian product, without a supplied
    bound or a false global bound for the ambient polynomial. *)
Theorem orthogonal_kinematic_lipschitz (R:realType) N:
  @is_metric_lipschitz R
    (inner_metric_space (product_inner_productP
      (@euclidean_hom_inner_productP R N N) (@euclidean_hom_inner_productP R N N)))
    (inner_metric_space (@euclidean_hom_inner_productP R N N))
    [set z:Hom (R_n R N) (R_n R N)*Hom (R_n R N) (R_n R N)|
      is_orthogonal_map (@euclidean_inner_product R N)
        (@euclidean_inner_product R N) (hom_as_linear z.1) /\
      is_orthogonal_map (@euclidean_inner_product R N)
        (@euclidean_inner_product R N) (hom_as_linear z.2)]
    (@orthogonal_kinematic_map R N).
Proof.
pose H:=Hom (R_n R N) (R_n R N).
pose hH:=@euclidean_hom_inner_productP R N N.
pose P:lmodType R:=[the lmodType R of (H*H)%type].
pose hP:=product_inner_productP hH hH.
pose O:=[set g:H|is_orthogonal_map (@euclidean_inner_product R N)
  (@euclidean_inner_product R N) (hom_as_linear g)].
have [e [p hChart]]:=@euclidean_hom_inner_chart_exists R N N.
have hCompact:=@finite_inner_cartesian_compact R H H _ _ hH hH _ _
  e p e p hChart hChart O O (@euclidean_stiefel_compact R N N) (@euclidean_stiefel_compact R N N).
exact (@inner_class_one_compact_lipschitz R P H _ _ hP hH setT _
  (@orthogonal_kinematic_map R N)
  ((@norm_class_firstP R P H _ _ (inner_norm_real_norm hP)
    (inner_norm_real_norm hH) setT (@orthogonal_kinematic_map R N)).1
    (@orthogonal_kinematic_map_class R N 1%N))
  (fun z _=>I) hCompact).
Qed.
