(** Federer (1969), 3.2.28(3), printed p. 266:
    the fibre measure of S is the Hausdorff measure
    of S^(n-m). The actual isometric parametrization
    proves the normalization; 3.2.13, p. 251,
    then evaluates it in Gamma functions. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  OrthogonalMaps EuclideanHomInnerCharts EuclideanForgetfulFibre HausdorffMeasure
  HausdorffIsometricEmbedding SphereGammaMass EulerGamma EulerGammaHalfParameters.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_forgetful_fibre_measure]: the
    displayed sphere-fibre measure in Federer 3.2.28(3),
    p. 266. It holds for every natural Hausdorff
    degree and uses the actual Hilbert Hom ambient
    space on the fibre side. *)
Theorem euclidean_forgetful_fibre_measure (R:realType) k n
    (alpha:Hom (R_n R k) (R_n R k.+1))
    (beta:Hom (R_n R k) (R_n R n)):
  (k<=n)%N ->
  is_orthogonal_map (@euclidean_inner_product R k) (@euclidean_inner_product R k.+1)
    (hom_as_linear alpha) ->
  is_orthogonal_map (@euclidean_inner_product R k) (@euclidean_inner_product R n)
    (hom_as_linear beta) ->forall q,
  @hausdorff_measure R (inner_metric_space (@euclidean_hom_inner_productP R k.+1 n)) q
    [set h|is_orthogonal_map (@euclidean_inner_product R k.+1)
      (@euclidean_inner_product R n) (hom_as_linear h) /\hom_comp h alpha=beta]=
  @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R (n-k))) q
    [set z|inner_norm (@euclidean_inner_productP R (n-k)) z= 1].
Proof.
move=>hkn hA hB q.
have [F [G [hCan [hDist hImage]]]]:=
  @euclidean_forgetful_fibre_isometric_parametrisation R k n alpha beta hkn hA hB.
rewrite -hImage.
exact:(@hausdorff_isometric_embedding_invariance R
  (inner_metric_space (@euclidean_inner_productP R (n-k)))
  (inner_metric_space (@euclidean_hom_inner_productP R k.+1 n)) F G hCan hDist q _).
Qed.

(** Source for [euclidean_forgetful_fibre_gamma_measure]: the
    sphere measure in the recurrence of Federer 3.2.28(3),
    p. 266, evaluated by 3.2.13, p. 251.
    Positive n-k is exactly the printed m=k+1<=n
    range, including the zero-dimensional fibre sphere. *)
Theorem euclidean_forgetful_fibre_gamma_measure (R:realType) k n
    (alpha:Hom (R_n R k) (R_n R k.+1))
    (beta:Hom (R_n R k) (R_n R n)) (hPos:(0<n-k)%N):
  is_orthogonal_map (@euclidean_inner_product R k) (@euclidean_inner_product R k.+1)
    (hom_as_linear alpha) ->
  is_orthogonal_map (@euclidean_inner_product R k) (@euclidean_inner_product R n)
    (hom_as_linear beta) ->
  @hausdorff_measure R (inner_metric_space (@euclidean_hom_inner_productP R k.+1 n)) (n-k-1)
    [set h|is_orthogonal_map (@euclidean_inner_product R k.+1)
      (@euclidean_inner_product R n) (hom_as_linear h) /\hom_comp h alpha=beta]=
    (2*(euler_gamma_half R)^+(n-k)/euler_gamma (@positive_dimension_half R (n-k) hPos))%:E.
Proof.
move=>hA hB.
have hlt:(k<n)%N by move:hPos; rewrite subn_gt0.
have hkn:=ltnW hlt.
rewrite (@euclidean_forgetful_fibre_measure R k n alpha beta hkn hA hB (n-k-1)).
exact:(@hausdorff_unit_sphere_gamma_mass R (n-k) hPos).
Qed.
