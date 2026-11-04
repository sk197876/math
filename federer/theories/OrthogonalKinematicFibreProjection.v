(** Federer (1969), 3.2.48, p. 284: project the
    actual Psi fibre onto Phi inverse(A intersect g(B)).
    This supporting argument preserves the whole original sets;
    it adds no measurability or transversality premise. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp
  classical_sets constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct
  InnerNorm InnerMetric EuclideanHomInnerCharts OrthogonalMaps
  EuclideanRectangularAdjoint SphericalProductPreimageImage OrthogonalKinematicMap
  OrthogonalKinematicFibres ProductInner ProductInnerNormBounds
  RectifiableSetUP FiniteMeasureRectifiableImages LipschitzUP LipschitzBasic HausdorffMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [orthogonal_kinematic_fibre_first_image]: the
    first-coordinate image of the whole fibre is precisely
    Phi inverse(A intersect g(B)), 3.2.48, p. 284.
    This is the exact printed fibre graph, including empty fibres. *)
Lemma orthogonal_kinematic_fibre_first_image (R:realType) N
    (c:R_n R N) (A B:set (R_n R N)) (g:Hom (R_n R N) (R_n R N)):
  is_orthogonal_map (@euclidean_inner_product R N)
    (@euclidean_inner_product R N) (hom_as_linear g) ->
  fst @` [set z:Hom (R_n R N) (R_n R N)*Hom (R_n R N) (R_n R N)|
    (spherical_orthogonal_preimage c A z.1 /\spherical_orthogonal_preimage c B z.2) /\
    orthogonal_kinematic_map z=g]=spherical_orthogonal_preimage c (A `&` (g @` B)).
Proof.
move=>hg.
have hGraph:=@orthogonal_kinematic_fibre_graph R N c A B g hg.
have hAssoc:[set z:Hom (R_n R N) (R_n R N)*Hom (R_n R N) (R_n R N)|
    (spherical_orthogonal_preimage c A z.1 /\spherical_orthogonal_preimage c B z.2) /\
    orthogonal_kinematic_map z=g]=[set z|
    spherical_orthogonal_preimage c A z.1 /\
    spherical_orthogonal_preimage c B z.2 /\orthogonal_kinematic_map z=g].
  apply/seteqP; split=>z.
  - move=>[[hx hy] hPsi]; exact (conj hx (conj hy hPsi)).
  - move=>[hx [hy hPsi]]; exact (conj (conj hx hy) hPsi).
rewrite hAssoc hGraph; apply/seteqP; split=>x.
- by move=>[z [y hy <-] <-].
- move=>hx; exists (x,hom_comp (euclidean_rectangular_adjoint g) x); last reflexivity.
  by exists x.
Qed.

(** Source for [orthogonal_kinematic_fibre_projection_rectifiable]:
    the actual first-coordinate projection transfers finite
    H^(lambda+mu) rectifiability from the whole Psi fibre
    to Phi inverse(A intersect g(B)), supporting the
    first conclusion of 3.2.48, p. 284. The
    contraction bound is derived from the actual product norm. *)
Lemma orthogonal_kinematic_fibre_projection_rectifiable (R:realType) N r
    (c:R_n R N) (A B:set (R_n R N)) (g:Hom (R_n R N) (R_n R N)):
  is_orthogonal_map (@euclidean_inner_product R N)
    (@euclidean_inner_product R N) (hom_as_linear g) ->
  is_measure_m_rectifiable (@hausdorff_measure R
    (inner_metric_space (product_inner_productP
      (@euclidean_hom_inner_productP R N N) (@euclidean_hom_inner_productP R N N))) r) r
    [set z:Hom (R_n R N) (R_n R N)*Hom (R_n R N) (R_n R N)|
      (spherical_orthogonal_preimage c A z.1 /\spherical_orthogonal_preimage c B z.2) /\
      orthogonal_kinematic_map z=g] ->
  is_measure_m_rectifiable (@hausdorff_measure R
    (inner_metric_space (@euclidean_hom_inner_productP R N N)) r) r
    (spherical_orthogonal_preimage c (A `&` (g @` B))).
Proof.
move=>hg hRect.
pose H:=inner_metric_space (@euclidean_hom_inner_productP R N N).
pose P:=inner_metric_space (product_inner_productP
  (@euclidean_hom_inner_productP R N N) (@euclidean_hom_inner_productP R N N)).
have hLip:@is_metric_lipschitz R P H
    [set z:Hom (R_n R N) (R_n R N)*Hom (R_n R N) (R_n R N)|
      (spherical_orthogonal_preimage c A z.1 /\spherical_orthogonal_preimage c B z.2) /\
      orthogonal_kinematic_map z=g] fst.
  apply:metric_lipschitz_of_bound; split; first exact:ler01.
  move=>x y _ _; rewrite !inner_metric_distanceE mul1r.
  exact (product_inner_first_norm_bound (@euclidean_hom_inner_productP R N N)
    (@euclidean_hom_inner_productP R N N) (x-y)).
have hResult:=hausdorff_measure_rectifiable_lipschitz_image hLip hRect.
by rewrite (orthogonal_kinematic_fibre_first_image c A B hg) in hResult.
Qed.
