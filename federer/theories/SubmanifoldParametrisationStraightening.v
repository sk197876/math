(** Federer (1969), 3.1.19, p. 231: (3) implies (1) by 3.1.18.
    Relative openness identifies the parametrised image with an
    ambient neighbourhood section of B. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerNorm
  HilbertFormCompactness NormDifferentialUP NormClassOneUP NormRegularity NormMetric
  NormDiffeomorphismUP NormSectionShearUP LinearRankUP LinearRangeProjectionUP NormRankZero
  ConstantRankChartUP ConstantRankTheorem EuclideanProductBox
  EuclideanSubmanifoldUP SubmanifoldChartsUP DiffeomorphismPlaneSection.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [open_parametrisations_submanifold]: implication
    (3) to (1), Federer 3.1.19, p. 231. The exact image law of
    3.1.18 and relative openness supply a genuine straightening;
    a constant-rank image alone would not identify the whole local B. *)
Theorem open_parametrisations_submanifold (R:realType) n mu k (B:set (R_n R n)) :
  (1<=k)%N -> @has_open_constant_rank_parametrisations R n mu k B ->
  @is_euclidean_submanifold R n mu k B.
Proof.
move=>hk hB b hb.
have [m [Q [f [D [hmm [hf [hD [hinto [hbim [hr hopen]]]]]]]]]]:=hB b hb.
have [l hm]:exists l,m=(mu+l)%N.
  exists (m-mu)%N; by rewrite addnC subnK.
subst m.
have [a ha hab]:=hbim.
pose NX:=inner_norm (@euclidean_inner_productP R (mu+l)).
pose hNX:=inner_norm_real_norm (@euclidean_inner_productP R (mu+l)).
have hgen:norm_generic_rank NX Q D a mu.
  have hc:=norm_class_continuous hf.
  have [r [hr0 hball]]:=(@hc a ha).1.
  exists r; split=>// h hh; split; first exact: hball.
  exact: hr (hball h hh).
have [U [e [p [j [g [G [psi hC]]]]]]]:=@federer_3_1_18 R mu l n Q f D a k hk hf hD hgen.
have hP:=constant_rank_projection hC.
pose V:=@constant_rank_parameter_domain R mu l g a e.
pose H:=@norm_section_shear_inverse R (R_n R n) (R_n R mu)
  (hom_of_linear p) (hom_of_linear j) psi.
pose h:=@norm_section_shear R (R_n R n) (R_n R mu)
  (hom_of_linear p) (hom_of_linear j) psi.
have hDU:=constant_rank_source_chart hC.
have hUA:=constant_rank_domain_subset hC.
have hUopen:=norm_diffeomorphism_source_open hDU.
have hrel:=hopen U hUA hUopen.
have hSM:(f @` U) `<=` [set y|V (p y)].
  move=>y [x hx <-].
  have hi:=( @norm_diffeomorphism_maps R (R_n R (mu+l)) (R_n R (mu+l)) NX NX hNX hNX
    U (@euclidean_product_box R mu l (g a) e) g G k hDU x hx).1.
  by rewrite (constant_rank_source_prefix hC hx) in hi.
have hbS:(f @` U) b by exists a; [exact: constant_rank_base_member hC|exact hab].
exact (@diffeomorphism_plane_section R n mu k B (f @` U) V p j h H b
  (range_projection_cancel hP) (constant_rank_target_chart hC) hSM
  (constant_rank_image hC) hrel hbS).
Qed.
