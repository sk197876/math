(** Federer (1969), 3.2.48, p. 284: completed
    measurability of the whole actual coarea fibre descends
    to its Phi preimage and then to the original
    intersection. No independent intersection-measurability premise
    is imposed in the signed integral argument. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp
  classical_sets constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct
  InnerNorm InnerMetric EuclideanHomInnerCharts OrthogonalMaps EuclideanRectangularAdjoint
  ProductInner UnitSphereSpace SphericalProductPreimageImage OrthogonalKinematicMap
  OrthogonalKinematicFibres OrthogonalKinematicFibreScale OrthogonalKinematicFibreProjection
  HausdorffSimilarityRestriction SphericalOrthogonalConverseRectifiability
  SphericalPreimageConverseMeasurable RectifiableSetUP HausdorffMeasure MeasureUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [orthogonal_kinematic_fibre_graph_normalized]: the
    actual whole-fibre graph in 3.2.48, p. 284,
    with the source-product conjunction grouped as in the
    existing coarea theorem. This is an exact set equality. *)
Lemma orthogonal_kinematic_fibre_graph_normalized (R:realType) N
    (c:R_n R N) (A B:set (R_n R N)) (g:Hom (R_n R N) (R_n R N)):
  is_orthogonal_map (@euclidean_inner_product R N)
    (@euclidean_inner_product R N) (hom_as_linear g) ->
  [set z:Hom (R_n R N) (R_n R N)*Hom (R_n R N) (R_n R N)|
    (spherical_orthogonal_preimage c A z.1 /\spherical_orthogonal_preimage c B z.2) /\
    orthogonal_kinematic_map z=g]=
  (fun x:Hom (R_n R N) (R_n R N)=>(x,hom_comp (euclidean_rectangular_adjoint g) x)) @`
    spherical_orthogonal_preimage c (A `&` (g @` B)).
Proof.
move=>hg; rewrite -(@orthogonal_kinematic_fibre_graph R N c A B g hg).
apply/seteqP; split=>z.
- move=>[[hx hy] hPsi]; exact (conj hx (conj hy hPsi)).
- move=>[hx [hy hPsi]]; exact (conj (conj hx hy) hPsi).
Qed.

(** Source for [orthogonal_kinematic_preimage_measurable]: the
    actual whole Phi preimage of A intersect g(B) is
    completed measurable when the whole coarea fibre is,
    supporting 3.2.48, p. 284. Exact similarity
    scaling transfers Caratheodory measurability through the actual graph. *)
Lemma orthogonal_kinematic_preimage_measurable (R:realType) N q
    (c:R_n R N) (A B:set (R_n R N)) (g:Hom (R_n R N) (R_n R N)):
  is_orthogonal_map (@euclidean_inner_product R N)
    (@euclidean_inner_product R N) (hom_as_linear g) ->
  measure_measurable (@hausdorff_measure R
    (inner_metric_space (product_inner_productP
      (@euclidean_hom_inner_productP R N N) (@euclidean_hom_inner_productP R N N))) q)
    [set z:Hom (R_n R N) (R_n R N)*Hom (R_n R N) (R_n R N)|
      (spherical_orthogonal_preimage c A z.1 /\spherical_orthogonal_preimage c B z.2) /\
      orthogonal_kinematic_map z=g] ->
  measure_measurable (@hausdorff_measure R
    (inner_metric_space (@euclidean_hom_inner_productP R N N)) q)
    (spherical_orthogonal_preimage c (A `&` (g @` B))).
Proof.
move=>hg hMeas.
pose X:=inner_metric_space (@euclidean_hom_inner_productP R N N).
pose Y:=inner_metric_space (product_inner_productP
  (@euclidean_hom_inner_productP R N N) (@euclidean_hom_inner_productP R N N)).
pose F:=fun x:X=>((x,hom_comp (euclidean_rectangular_adjoint g) x):Y).
pose S:=spherical_orthogonal_preimage c (A `&` (g @` B)).
have hLeft:cancel F fst by move=>x.
have hDistance x y:@mdist R Y (F x) (F y)=Num.sqrt (2:R)*@mdist R X x y.
  rewrite !inner_metric_distanceE; exact (@orthogonal_kinematic_fibre_distance R N g x y hg).
have hRoot:0<Num.sqrt (2:R) by rewrite sqrtr_gt0 ltr0n.
have hGraph:=@orthogonal_kinematic_fibre_graph_normalized R N c A B g hg.
rewrite hGraph in hMeas.
have hResult:=@hausdorff_similarity_preimage_measurable R X Y F fst (Num.sqrt (2:R))
  hRoot hLeft hDistance q (F @` S) hMeas.
have hPre:F @^-1` (F @` S)=S.
  apply/seteqP; split=>x.
  - move=>[y hy hEq]; have hSame:y=x:=can_inj hLeft hEq.
    by rewrite -hSame.
  - move=>hx; by exists x.
by rewrite hPre in hResult.
Qed.

(** Source for [orthogonal_kinematic_intersection_measurable]: completed
    measurability of the original A intersect g(B),
    supporting both original signed integrals in 3.2.48,
    p. 284. Finite rectifiability and measurability of
    the whole coarea fibre discharge every hypothesis. *)
Lemma orthogonal_kinematic_intersection_measurable (R:realType) d r
    (c:R_n R d.+1) (A B:set (R_n R d.+1))
    (g:Hom (R_n R d.+1) (R_n R d.+1)):
  inner_norm (@euclidean_inner_productP R d.+1) c= 1 ->
  A `<=` @euclidean_unit_sphere_set R d.+1 ->
  is_orthogonal_map (@euclidean_inner_product R d.+1)
    (@euclidean_inner_product R d.+1) (hom_as_linear g) ->
  let P:=inner_metric_space (product_inner_productP
    (@euclidean_hom_inner_productP R d.+1 d.+1) (@euclidean_hom_inner_productP R d.+1 d.+1)) in
  let fibre:=[set z:Hom (R_n R d.+1) (R_n R d.+1)*Hom (R_n R d.+1) (R_n R d.+1)|
    (spherical_orthogonal_preimage c A z.1 /\spherical_orthogonal_preimage c B z.2) /\
    orthogonal_kinematic_map z=g] in
  is_measure_m_rectifiable (@hausdorff_measure R P (r+d*(d-1)%/2)) (r+d*(d-1)%/2)%N fibre ->
  measure_measurable (@hausdorff_measure R P (r+d*(d-1)%/2)) fibre ->
  measure_measurable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R d.+1)) r) (A `&` (g @` B)).
Proof.
move=>hc hA hg P fibre hRect hMeas.
have hPreRect:=@orthogonal_kinematic_fibre_projection_rectifiable R d.+1
  (r+d*(d-1)%/2)%N c A B g hg hRect.
have hSphere:A `&` (g @` B) `<=` @euclidean_unit_sphere_set R d.+1.
  move=>x hx; exact (hA x hx.1).
have hERect:=@spherical_orthogonal_converse_rectifiability R d c (A `&` (g @` B)) r hc hSphere hPreRect.
have hPreMeas:=@orthogonal_kinematic_preimage_measurable R d.+1 (r+d*(d-1)%/2)%N c A B g hg hMeas.
exact (@spherical_preimage_converse_measurable R d r c (A `&` (g @` B)) hc hSphere hERect hPreMeas).
Qed.
