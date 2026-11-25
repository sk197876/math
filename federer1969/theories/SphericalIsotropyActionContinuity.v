(** Federer (1969), 3.2.48, p. 286: the actual stabilizer family
    and its joint right action are continuous in the original Hilbert
    Hom metric. The sealed transverse extension, fixed conjugacy and
    actual adjoint/composition laws discharge the topology requirements. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets topology.
From Federer Require Import Hom TensorUP GrassmannAbbreviations FiniteCoordinates CoordinateProjection
  EuclideanInnerProduct InnerProductUP InnerNorm InnerMetric EuclideanHomInnerCharts
  HomInner HomSpaceTopology HomCompositionDeterminant LinearBasis HilbertFormCompactness
  NormFiniteLinearBound OrthogonalMaps EuclideanRectangularAdjoint
  EuclideanBlockExtension EuclideanOrthogonalBlockExtension EuclideanOrthogonalInvariantMeasures
  OrthogonalGroupTopology OrthogonalGroupHaarMeasure LinearGroupTopology
  SphericalIsotropyConjugacy SphericalIsotropyTransverseAction InnerCartesianContinuousMaps
  TopologicalProductMaps NormMetricScaleContinuity ProductInner.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [spherical_isotropy_transverse_continuous]: continuity
    of the actual whole transverse orthogonal family used in 3.2.48,
    p. 286. The extension is accessed solely through its sealed laws
    and already proved continuity; no matrix construction is opened. *)
Theorem spherical_isotropy_transverse_continuous (R:realType) d
    (Q:Hom (R_n R (1+d)) (R_n R (1+d))):
  is_orthogonal_map (@euclidean_inner_product R (1+d))
    (@euclidean_inner_product R (1+d)) (hom_as_linear Q) ->
  continuous (fun g:euclidean_orthogonal_group R d=>
    (spherical_isotropy_transverse_operator Q (orthogonal_element_map g):
      inner_metric_space (@euclidean_hom_inner_productP R (1+d) (1+d)))).
Proof.
move=>hQ.
pose H:=inner_metric_space (@euclidean_hom_inner_productP R (1+d) (1+d)).
pose O:=euclidean_orthogonal_group R d.
have hInclusion:continuous (fun g:euclidean_orthogonal_group R (1+d)=>(orthogonal_element_map g:H)).
  rewrite /H (Prop_irrelevance (@euclidean_hom_inner_productP R (1+d) (1+d))
    (hom_inner_productP (@euclidean_inner_productP R (1+d)) (@euclidean_inner_productP R (1+d))
      (@coordinate_basisP R (1+d)))).
  exact (@orthogonal_element_continuous R (R_n R (1+d)) (@euclidean_inner_product R (1+d))
    (@euclidean_inner_productP R (1+d)) (1+d)%N (@coordinate_basis R (1+d)) (@coordinate_basisP R (1+d))).
have hBlock:continuous (fun g:O=>(orthogonal_element_map (@euclidean_orthogonal_block_extension R 1 d g):H)).
  move=>g; exact (continuous_comp (@euclidean_orthogonal_block_extension_continuous R 1 d g)
    (hInclusion (@euclidean_orthogonal_block_extension R 1 d g))).
have hConjugate:continuous (fun h:H=>(spherical_isotropy_conjugate Q h:H)).
  apply:(@metric_fixed_lipschitz_continuous R H H (fun h=>spherical_isotropy_conjugate Q h) 1 ler01).
  move=>x y; rewrite !inner_metric_distanceE mul1r.
  by rewrite (spherical_isotropy_conjugacy_distance x y hQ).
have hBlockMap g:orthogonal_element_map (@euclidean_orthogonal_block_extension R 1 d g)=
    hom_of_linear (@euclidean_block_extension R 1 d (hom_as_linear (orthogonal_element_map g))).
  apply:hom_ext=>v.
  rewrite /euclidean_orthogonal_block_extension.
  exact:orthogonal_element_ofE.
have hFunction:(fun g:O=>(spherical_isotropy_transverse_operator Q (orthogonal_element_map g):H))=
    (fun g=>spherical_isotropy_conjugate Q
      (orthogonal_element_map (@euclidean_orthogonal_block_extension R 1 d g))).
  apply:funext=>g; by rewrite /spherical_isotropy_transverse_operator hBlockMap.
rewrite hFunction=>g; exact (continuous_comp (hBlock g)
  (hConjugate (orthogonal_element_map (@euclidean_orthogonal_block_extension R 1 d g)))).
Qed.

(** Source for [spherical_isotropy_right_inverse_action_continuous]:
    the actual joint map (h,y) to y h inverse in the averaging step
    of 3.2.48, p. 286. Adjoint continuity follows from a finite linear
    bound in the specified Hilbert metric; the ambient action is exact. *)
Theorem spherical_isotropy_right_inverse_action_continuous (R:realType) d
    (Q:Hom (R_n R (1+d)) (R_n R (1+d))):
  is_orthogonal_map (@euclidean_inner_product R (1+d))
    (@euclidean_inner_product R (1+d)) (hom_as_linear Q) ->
  continuous (fun z:euclidean_orthogonal_group R d*
      inner_metric_space (@euclidean_hom_inner_productP R (1+d) (1+d))=>
    (hom_comp z.2 (euclidean_rectangular_adjoint
      (spherical_isotropy_transverse_operator Q (orthogonal_element_map z.1))):
      inner_metric_space (@euclidean_hom_inner_productP R (1+d) (1+d)))).
Proof.
move=>hQ.
pose V:=R_n R (1+d).
pose H0:=Hom V V.
pose hH:=@euclidean_hom_inner_productP R (1+d) (1+d).
pose H:=inner_metric_space hH.
pose O:=euclidean_orthogonal_group R d.
pose A:Hom H0 H0:=hom_of_linear (GRing.Linear.clone _ _ _ _ (@euclidean_rectangular_adjoint R (1+d) (1+d)) _).
pose b:=@hom_rank_one_base R V V (1+d) (1+d) (@coordinate_basis R (1+d))
  (@coordinate_basisP R (1+d)) (@coordinate_basis R (1+d)).
have hb:=@hom_rank_one_baseP R V V (1+d) (1+d) (@coordinate_basis R (1+d))
  (@coordinate_basisP R (1+d)) (@coordinate_basis R (1+d)) (@coordinate_basisP R (1+d)).
have hBound:=@norm_finite_linear_bounded R H0 H0 _ _ (inner_norm_real_norm hH) (inner_norm_real_norm hH) _ b hb A.
have hAdj:=@inner_bounded_linear_continuous R H0 H0 _ _ hH hH A hBound.
have hHat:=spherical_isotropy_transverse_continuous hQ.
have hInverse:continuous (fun g:O=>(euclidean_rectangular_adjoint
    (spherical_isotropy_transverse_operator Q (orthogonal_element_map g)):H)).
  move=>g; exact (continuous_comp (hHat g) (hAdj (spherical_isotropy_transverse_operator Q (orthogonal_element_map g)))).
have hPair:continuous (fun z:O*H=>(z.2,
    euclidean_rectangular_adjoint (spherical_isotropy_transverse_operator Q (orthogonal_element_map z.1))):H*H).
  apply:topological_pair_continuous; first exact:second_projection_continuous.
  move=>z; exact (continuous_comp (@first_projection_continuous O H z) (hInverse z.1)).
have hComposition:continuous (fun z:H*H=>(hom_comp z.1 z.2:H)).
  rewrite /H /hH (Prop_irrelevance (@euclidean_hom_inner_productP R (1+d) (1+d))
    (hom_inner_productP (@euclidean_inner_productP R (1+d)) (@euclidean_inner_productP R (1+d))
      (@coordinate_basisP R (1+d)))).
  exact (@hom_composition_continuous R V (@euclidean_inner_product R (1+d))
    (@euclidean_inner_productP R (1+d)) (1+d)%N (@coordinate_basis R (1+d)) (@coordinate_basisP R (1+d))).
move=>z; exact (continuous_comp (hPair z) (hComposition
  (z.2,euclidean_rectangular_adjoint (spherical_isotropy_transverse_operator Q (orthogonal_element_map z.1))))).
Qed.
