(** Federer (1969), 3.4.8(11), p. 333:
    an irreducible component has no larger
    dimension than the original variety germ.
    These supporting laws follow from the original
    directional witnesses and reverse ideal inclusion. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric InnerProductUP InnerNorm HilbertFormCompactness
  LinearBasis OrthogonalGroupTopology AnalyticGermRing AnalyticRotatedGermIdeal
  AnalyticReductionLociUP AnalyticReductionActual AnalyticReductionDepthUP
  AnalyticReductionDepthLaws AnalyticDepthSealed SetGermUP SetGermOrder GermVanishingSealed
  GermVanishingMonotonicity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Depth.
Variable R:realType.
Variable X:lmodType R.
Variable B:X->X->R.
Variable hB:is_inner_product B.
Variable n:nat.
Variable e:'I_n->X.
Variable he:is_basis e.
Variable omega:'I_n->Hom X R^o.
Local Notation NX:=(inner_norm hB).
Local Notation hNX:=(inner_norm_real_norm hB).
Local Notation G:=(@analytic_germ_ring R X NX hNX 0).
Local Notation O:=(@orthogonal_group R X B hB n e he).
Local Notation depth:=(@AnalyticDepth.value R X B hB n e he omega).

(** Source for [analytic_rotated_ideal_inclusion]:
    original ideal inclusion is preserved under
    the coordinate change in 3.4.8(11),
    p. 333. This is a supporting law. *)
Lemma analytic_rotated_ideal_inclusion (I J:set G) (g:O):
  I `<=` J ->
  @analytic_rotated_germ_ideal R X B hB n e he I g `<=`
    @analytic_rotated_germ_ideal R X B hB n e he J g.
Proof.
move=>hIJ alpha /analytic_rotated_germ_ideal_membership [beta [hBeta hEqual]].
apply/analytic_rotated_germ_ideal_membership;exists beta;split;[exact:hIJ beta hBeta|exact:hEqual].
Qed.

(** Source for [analytic_reduction_B_ideal_monotone]:
    a directional witness in a smaller ideal
    remains one in a larger ideal, supporting
    3.4.8(11), p. 333. *)
Lemma analytic_reduction_B_ideal_monotone (I J:set G):
  I `<=` J ->forall j g,
  @analytic_reduction_actual_B R X B hB n e he omega I j g ->
  @analytic_reduction_actual_B R X B hB n e he omega J j g.
Proof.
move=>hIJ j g.
have hI:=@analytic_reduction_actual_laws R X B hB n e he omega I.
have hJ:=@analytic_reduction_actual_laws R X B hB n e he omega J.
move/(analytic_reduction_B_membership hI j g)=>[alpha [hAlpha [hQ hDirection]]].
apply/(analytic_reduction_B_membership hJ j g);exists alpha;split.
- exact:(@analytic_rotated_ideal_inclusion I J g hIJ alpha hAlpha).
- by split.
Qed.

(** Source for [analytic_ideal_depth_antitone]:
    a larger original ideal has no larger
    depth, supporting the component reduction in
    3.4.8(11), p. 333. No properness
    or finite-generation premise is needed here. *)
Lemma analytic_ideal_depth_antitone (I J:set G):I `<=` J ->(depth J<=depth I)%N.
Proof.
move=>hIJ;apply:(@analytic_reduction_depth_monotone n O
  (@analytic_reduction_actual_B R X B hB n e he omega I)
  (@analytic_reduction_actual_B R X B hB n e he omega J)
  (depth I) (depth J)).
- exact:analytic_reduction_B_ideal_monotone hIJ.
- exact:AnalyticDepth.laws.
- exact:AnalyticDepth.laws.
Qed.

(** Source for [analytic_variety_ideal_depth_monotone]:
    local containment of variety germs implies
    the corresponding dimension inequality in
    3.4.8(11), p. 333. Dimension is
    expressed by its original defining ideal depth. *)
Lemma analytic_variety_ideal_depth_monotone
  (alpha beta:@set_germ_space (Topological.clone (real_norm_metric_space hNX) _) 0):
  set_germ_subset alpha beta ->
  (depth (@AnalyticSetIdeal.value R X NX hNX 0 alpha)<=
    depth (@AnalyticSetIdeal.value R X NX hNX 0 beta))%N.
Proof.
move=>hAB;apply:analytic_ideal_depth_antitone.
exact:(@analytic_set_ideal_antitone R X NX hNX 0 alpha beta hAB).
Qed.
End Depth.
