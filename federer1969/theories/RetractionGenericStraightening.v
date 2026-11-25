(** Federer (1969), 3.1.20, p. 233: a generic point of a
    class-k retraction has a straightening neighbourhood for B,
    by the constant-rank theorem of 3.1.18. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerNorm
  HilbertFormCompactness NormMetric NormDifferentialUP NormClassOneUP NormRegularity
  NormDiffeomorphismUP NormSectionShearUP RetractionUP NormRankZero LinearRangeProjectionUP
  ConstantRankChartUP ConstantRankTheorem EuclideanProductBox EuclideanSubmanifoldUP
  DiffeomorphismPlaneSection SubmanifoldStraighteningLocalAgreement.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [retraction_generic_straightening]: the final
    normal-form step of the converse proof of Federer 3.1.20,
    p. 233. On U, B agrees with f(U) because f fixes B. No
    openness of f on its entire domain is assumed. *)
Theorem retraction_generic_straightening (R:realType) n mu k
    (A B:set (R_n R n)) (f:R_n R n->R_n R n)
    (D:R_n R n->Hom (R_n R n) (R_n R n)) b :
  (1<=k)%N ->
  is_norm_class_retraction (inner_norm_real_norm (@euclidean_inner_productP R n)) A B f k ->
  is_norm_class_one_field (inner_norm (@euclidean_inner_productP R n))
    (inner_norm (@euclidean_inner_productP R n)) A f D ->
  B b -> norm_generic_rank (inner_norm (@euclidean_inner_productP R n)) A D b mu ->
  exists T C sigma tau Z,@is_submanifold_straightening R n mu k B b T C sigma tau Z.
Proof.
move=>hk hR hD hb hgen.
have hmn: (mu<=n)%N by have hh:=generic_rank_dimension_bounds hgen; rewrite minnn in hh.
have [l hn]:exists l,n=(mu+l)%N by exists (n-mu)%N; rewrite subnKC.
subst n.
pose X:=R_n R (mu+l).
pose NX:=inner_norm (@euclidean_inner_productP R (mu+l)).
pose hNX:=inner_norm_real_norm (@euclidean_inner_productP R (mu+l)).
have [U [e [p [j [g [G [psi hC]]]]]]]:=@federer_3_1_18 R mu l (mu+l) A f D b k hk
  (norm_retraction_class hR) hD hgen.
pose V:=@constant_rank_parameter_domain R mu l g b e.
pose S:=f @` U.
pose h:=@norm_section_shear R X (R_n R mu) (hom_of_linear p) (hom_of_linear j) psi.
pose H:=@norm_section_shear_inverse R X (R_n R mu) (hom_of_linear p) (hom_of_linear j) psi.
have hP:=constant_rank_projection hC.
have hDU:=constant_rank_source_chart hC.
have hUb:U b:=constant_rank_base_member hC.
have hUA:=constant_rank_domain_subset hC.
have hUopen:=norm_diffeomorphism_source_open hDU.
have hSM:S `<=` [set y|V (p y)].
  move=>y [x hx <-].
  have hi:=(@norm_diffeomorphism_maps R X X NX NX hNX hNX U
    (@euclidean_product_box R mu l (g b) e) g G k hDU x hx).1.
  by rewrite (constant_rank_source_prefix hC hx) in hi.
have hrel:@relatively_open_set [the topologicalType of real_norm_metric_space hNX] S S.
  exists setT; split; first exact: openT.
  by rewrite setIT.
have hfb:=@norm_retraction_fixed R X NX hNX A B f k hR b hb.
have hbS:S b by exists b=>//.
have [T [C [sigma [tau [Z hZ]]]]]:=@diffeomorphism_plane_section R (mu+l) mu k
  S S V p j h H b (range_projection_cancel hP) (constant_rank_target_chart hC)
  hSM (constant_rank_image hC) hrel hbS.
have heq x (hx:U x):B x <-> S x.
  split.
  - move=>hBx; exists x=>//; exact (@norm_retraction_fixed R X NX hNX A B f k hR x hBx).
  - move=>[y hy <-]; exact (@norm_retraction_range R X NX hNX A B f k hR y (hUA y hy)).
exact (@submanifold_straightening_local_agreement R (mu+l) mu k B S U T C b sigma tau Z
  hZ hUopen hUb heq).
Qed.
