(** Federer (1969), 3.2.47, p. 283: the translated
    section patches cover the actual sphere. Compactness permits
    finitely many compact base cores inside these patches.
    Each translation is fixed before taking its product with I;
    no global Lipschitz bound on an open hemisphere is asserted. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp
  finmap classical_sets topology.
From Federer Require Import Hom TensorUP GrassmannAbbreviations EuclideanInnerProduct
  InnerProductUP InnerNormalization InnerNorm InnerMetric OrthogonalMaps LinearBasis OrthonormalFamilies
  EuclideanHomInnerCharts EuclideanRectangularAdjoint EuclideanOrthogonalAdjointInverse
  PartialFunctionUP SphericalOrthogonalSectionUP SphericalOrthogonalSection
  SphericalOrthogonalSectionValues SphericalFrameCone UnitVectorOrthogonalMap
  UnitSphereSpace MetricClosedBalls CompactOpenCoverClosedCores NormDifferentialUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [spherical_translated_cone_open]: the ambient
    open set underlying e(U) is open, supporting the actual
    finite chart cover in 3.2.47, p. 283. Orthogonal
    inverse translation preserves the actual norm. *)
Lemma spherical_translated_cone_open (R:realType) n
    (e:'I_n.+1->R_n R n.+1) (t:Hom (R_n R n.+1) (R_n R n.+1)):
  is_orthogonal_map (@euclidean_inner_product R n.+1)
    (@euclidean_inner_product R n.+1) (hom_as_linear t) ->
  @open (inner_metric_space (@euclidean_inner_productP R n.+1))
    [set a|spherical_frame_cone e (euclidean_rectangular_adjoint t a)].
Proof.
move=>ht; rewrite openE=>a ha.
have [d [hd hBall]]:=spherical_frame_cone_interior ha.
apply:(proj2 (metricType_numDomainType.nbhs_mdistP a _)); exists d; first exact hd.
move=>x hx.
have hSmall:inner_norm (@euclidean_inner_productP R n.+1)
    (euclidean_rectangular_adjoint t (x-a))<d.
  rewrite (@orthogonal_map_norm R (R_n R n.+1) (R_n R n.+1) _ _
    (@euclidean_inner_productP R n.+1) (@euclidean_inner_productP R n.+1)
    (hom_as_linear (euclidean_rectangular_adjoint t))
    (@euclidean_orthogonal_adjoint_orthogonal R n.+1 t ht)).
  change (is_true (inner_norm (@euclidean_inner_productP R n.+1) (a-x)<d)) in hx.
  by rewrite -[x-a]opprB inner_normN.
have hResult:=hBall (euclidean_rectangular_adjoint t (x-a)) hSmall.
have hSum:euclidean_rectangular_adjoint t a+euclidean_rectangular_adjoint t (x-a)=
    euclidean_rectangular_adjoint t x.
  by rewrite -linearD addrC subrK.
by rewrite hSum in hResult.
Qed.

(** Source for [spherical_finite_base_cores]: finitely many
    actual compact parts of the original sphere cover it and
    stay inside individually fixed translated patches e(U),
    supplying the reduction to one patch in 3.2.47, p. 283. *)
Theorem spherical_finite_base_cores (R:realType) n
    (e:'I_n.+1->R_n R n.+1) (he:is_basis e)
    (hON:orthonormal_family (@euclidean_inner_product R n.+1) e):
  exists F:{fset (Hom (R_n R n.+1) (R_n R n.+1)*(R_n R n.+1*R))%type},
    (forall p,p \in F ->
      is_orthogonal_map (@euclidean_inner_product R n.+1)
        (@euclidean_inner_product R n.+1) (hom_as_linear p.1) /\
      @compact (inner_metric_space (@euclidean_inner_productP R n.+1))
        (@euclidean_unit_sphere_set R n.+1 `&` @metric_closed_ball R (inner_metric_space (@euclidean_inner_productP R n.+1)) p.2.1 p.2.2) /\
      forall a,(@euclidean_unit_sphere_set R n.+1 `&` @metric_closed_ball R (inner_metric_space (@euclidean_inner_productP R n.+1)) p.2.1 p.2.2) a ->
        spherical_frame_patch e (euclidean_rectangular_adjoint p.1 a)) /\
    @euclidean_unit_sphere_set R n.+1 `<=`
      \bigcup_(p in [set` F]) (@euclidean_unit_sphere_set R n.+1 `&`
        @metric_closed_ball R (inner_metric_space (@euclidean_inner_productP R n.+1)) p.2.1 p.2.2).
Proof.
pose V:=R_n R n.+1.
pose X:=inner_metric_space (@euclidean_inner_productP R n.+1).
pose H:=Hom V V.
pose D:set H:=[set t|is_orthogonal_map (@euclidean_inner_product R n.+1)
  (@euclidean_inner_product R n.+1) (hom_as_linear t)].
pose U:=fun t:H=>[set a:X|spherical_frame_cone e (euclidean_rectangular_adjoint t a)].
have hc:inner_norm (@euclidean_inner_productP R n.+1) (e ord0)= 1.
  exact (@orthonormal_norm1 R V (@euclidean_inner_product R n.+1)
    (@euclidean_inner_productP R n.+1) (Finite.clone 'I_n.+1 _) e hON ord0).
have hDomain:partial_function_domain (spherical_orthogonal_section he) (e ord0).
  exists (hom_of_linear (TensorUP.linear_id V)); exact:spherical_section_base_point hON.
rewrite spherical_orthogonal_section_domain in hDomain.
have hCover:(@euclidean_unit_sphere_set R n.+1) `<=` \bigcup_(t in D) U t.
  move=>a ha; have [t [ht hta]]:=@unit_vector_orthogonal_map_exists R n.+1
    (e ord0) a (ltn0Sn n) hc ha.
  pose T:Hom V V:=hom_of_linear t.
  have hT:D T:=ht.
  exists T; first exact hT.
  change (spherical_frame_cone e (euclidean_rectangular_adjoint T a)).
  have hValue:euclidean_rectangular_adjoint T a=e ord0.
    rewrite -hta; exact (@euclidean_orthogonal_adjoint_cancel R n.+1 T hT (e ord0)).
  by rewrite hValue; exact hDomain.2.
have [F [hF hFS]]:=@compact_open_cover_closed_cores R X [the choiceType of H] D U
  (@euclidean_unit_sphere_set R n.+1) (@euclidean_unit_sphere_compact R n.+1)
  (fun t ht=>@spherical_translated_cone_open R n e t ht) hCover.
exists F; split; last exact hFS.
move=>p hp; have [ht [hr [hK hKU]]]:=hF p hp.
split; first exact ht.
split; first exact hK.
move=>a ha; split; last exact:hKU a ha.
rewrite (@orthogonal_map_norm R V V _ _ (@euclidean_inner_productP R n.+1)
  (@euclidean_inner_productP R n.+1) (hom_as_linear (euclidean_rectangular_adjoint p.1))
  (@euclidean_orthogonal_adjoint_orthogonal R n.+1 p.1 ht)).
exact ha.1.
Qed.
