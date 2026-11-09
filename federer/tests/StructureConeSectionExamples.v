(** Federer (1969), 3.3.5, p. 292: actual degree-zero,
    full-rank projection and sharp nonzero graph regressions. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology lra.
From Federer Require Import TensorUP ConcatenatedFamilies GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  EuclideanProjectionSpace CoordinateProjection EuclideanOneCoordinate EuclideanOneNormDifferential
  StructureConeAvoidanceTheorem StructureConeAvoidance StructureGraphSectionUP StructureSharpGraphBound
  StructureCone StructureProjectionKernel StructureZeroPlaneCone StructureConeDensityValues MetricDiameterMaps
  EuclideanBlockCoordinates EuclideanBlockLinear RectifiableSetUP
  SignedSquareRootSealed SignedSquareRootLaws LipschitzUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [structure_section_zero_ambient_infinite_radius_example]: actual R^0
    and infinite-radius endpoint of Federer 3.3.5, p. 292. Its nonempty whole source has
    a global projection section containing its sole point and is
    countably zero rectifiable; no positive-dimension premise is used. *)
Example structure_section_zero_ambient_infinite_radius_example (R:realType):
  exists p:euclidean_projection_space R 0 0,
    (exists f,is_structure_projection_section
      [set (0:inner_metric_space (@euclidean_inner_productP R 0))] p (1/2) f) /\
    is_countably_m_rectifiable 0 (@setT (inner_metric_space (@euclidean_inner_productP R 0))).
Proof.
have hp:O_star (linear_id (R_n R 0)).
  exists (linear_id (R_n R 0)); split; by move=>x y.
have [p hP]:=euclidean_projection_linear_complete hp.
have hs:=@structure_density_positive_half_bounds R 1 ltr01.
have hAvoid:@is_structure_cone_avoiding R 0 0 (leqnn 0) setT p +oo%E (1/2).
  move=>a _; rewrite (structure_zero_plane_cone_empty
    (structure_projection_kernel (leqnn 0) p) a +oo%E (andP hs).1 (ltW (andP hs).2)) setI0.
  exact:erefl.
have [hSections hRect]:=@federer_3_3_5 R 0 0 (leqnn 0) setT p +oo%E (1/2) (@ltry R 0) hs hAvoid.
exists p; split=>//; apply:hSections; first by move=>x _.
by rewrite extended_metric_diameter_singleton; exact:ltry.
Qed.

(** Source for [structure_section_identity_line_example]: actual
    n=m= 1 endpoint of Federer 3.3.5, p. 292. Use the original identity
    projection and noncentral source singleton at coordinate one.
    The complete theorem supplies a global projection section and
    countable rectifiability of the original whole line. *)
Example structure_section_identity_line_example (R:realType):
  exists p:euclidean_projection_space R 1 1,
    (forall x,euclidean_projection_linear p x=x) /\
    (exists f,is_structure_projection_section [set euclidean_one_embed (1:R)] p (1/2) f) /\
    is_countably_m_rectifiable 1 (@setT (inner_metric_space (@euclidean_inner_productP R 1))).
Proof.
have hp:O_star (linear_id (R_n R 1)).
  exists (linear_id (R_n R 1)); split; by move=>x y.
have [p hP]:=euclidean_projection_linear_complete hp.
have hs:=@structure_density_positive_half_bounds R 1 ltr01.
have hAvoid:@is_structure_cone_avoiding R 1 1 (leqnn 1) setT p 1%E (1/2).
  move=>a _.
  rewrite (structure_zero_plane_cone_empty
    (structure_projection_kernel (leqnn 1) p) a 1%E (andP hs).1 (ltW (andP hs).2)) setI0.
  exact:erefl.
have [hSections hRect]:=@federer_3_3_5 R 1 1 (leqnn 1) setT p 1%E (1/2) (ltac:(by rewrite lte_fin)) hs hAvoid.
exists p; split; first exact:hP.
split=>//; apply:hSections; first by move=>x _.
by rewrite extended_metric_diameter_singleton lte_fin ltr01.
Qed.

(** Source for [structure_section_sharp_graph_example]: concrete
    sharp-bound check for the graph construction in Federer 3.3.5,
    p. 292. The actual line graph y maps to (sqrt(3)y,y) is globally
    two Lipschitz and has image-point distance two between base points
    zero and one. Thus the orthogonal sum of squares keeps the actual
    sharp bound instead of weakening it to sqrt(3)+1. *)
Example structure_section_sharp_graph_example (R:realType):
  let C:=@SignedSquareRoot.value R 3 in
  let E:=inner_metric_space (@euclidean_inner_productP R 1) in
  let g:=fun y:E=>C*:y in
  let f:=fun y:E=>@euclidean_block_join R 1 1 (g y,y) in
  @is_metric_lipschitz_bound R E
    (inner_metric_space (@euclidean_inner_productP R 2)) setT f 2 /\
  mdist (f (0:E)) (f (euclidean_one_embed (1:R)))= 2.
Proof.
cbn zeta.
pose C:=@SignedSquareRoot.value R 3.
pose E:=inner_metric_space (@euclidean_inner_productP R 1).
pose g:=fun y:E=>C*:y.
pose f:=fun y:E=>@euclidean_block_join R 1 1 (g y,y).
have hThree:0<=(3:R) by rewrite ler0n.
have hC:0<=C:=(signed_root_sign_bounds (3:R)).1 hThree.
have hSquare:C^+2= 3 by rewrite /C signed_root_square (ger0_norm hThree).
have hG:@is_metric_lipschitz_bound R
    (inner_metric_space (@euclidean_inner_productP R 1))
    (inner_metric_space (@euclidean_inner_productP R 1)) setT g C.
  split=>// x y _ _; rewrite /g !inner_metric_distanceE -scalerBr inner_normZ (ger0_norm hC).
  exact:lexx.
split.
- apply:(@structure_orthogonal_graph_sharp_lipschitz R 1 1 g C 2 hG); [by rewrite ler0n|by nra].
- rewrite /f /g metric_sym inner_metric_distanceE scaler0.
  have hDiff:@euclidean_block_join R 1 1 (C*:euclidean_one_embed (1:R),euclidean_one_embed (1:R))-
      @euclidean_block_join R 1 1 (0,0)=
      @euclidean_block_join R 1 1 (C*:euclidean_one_embed (1:R),euclidean_one_embed (1:R)).
    apply:euclidean_block_vectors_ext.
    - move=>i; rewrite euclidean_block_join_left !ffunE !concatenate_family_l
        /= /euclidean_one_embed !ffunE.
      change (C*1-0=C*1); by rewrite subr0.
    - move=>i; rewrite euclidean_block_join_right !ffunE !concatenate_family_r
        /= /euclidean_one_embed !ffunE.
      change ((1:R)-0= 1); by rewrite subr0.
  rewrite hDiff.
  have hEnergy:=(inner_norm_sqr (@euclidean_inner_productP R 2)
    (@euclidean_block_join R 1 1 (C*:euclidean_one_embed (1:R),euclidean_one_embed (1:R)))).
  rewrite (@euclidean_block_join_inner R 1 1
    (C*:euclidean_one_embed (1:R),euclidean_one_embed (1:R))
    (C*:euclidean_one_embed (1:R),euclidean_one_embed (1:R))) /=
    -(inner_norm_sqr (@euclidean_inner_productP R 1))
    -(inner_norm_sqr (@euclidean_inner_productP R 1)) inner_normZ (ger0_norm hC)
    euclidean_one_norm_coordinate /euclidean_one_embed ffunE normr1 mulr1 hSquare in hEnergy.
  have hN:=inner_norm_nonnegative (@euclidean_inner_productP R 2)
    (@euclidean_block_join R 1 1 (C*:euclidean_one_embed (1:R),euclidean_one_embed (1:R))).
  nra.
Qed.
