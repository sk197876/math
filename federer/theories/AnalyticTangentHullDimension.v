(** Federer (1969), 3.4.11, p. 338:
    the actual analytic hull of the original tangent
    cone has dimension at most the original germ.
    Reuse the proved leading-ideal depth inequality and
    tangent vanishing inclusion, then the original hull
    and ideal-recovery theorems. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric GrassmannAbbreviations FiniteCoordinates
  FiniteDualDimension EuclideanInnerProduct InnerNorm HilbertFormCompactness AnalyticGermRing
  SetGermUP SetGermOrder SetGermBoundary GermVanishingSealed GermVanishingIdeal
  CommutativeIdealUP EuclideanAnalyticGermNoetherian IdealVarietyGermUP IdealVarietyGermSealed
  IdealVarietyVanishingLaws AnalyticVarietyGermUP AnalyticDepthSealed AnalyticIdealDepthMonotonicity
  AnalyticInitialIdealSealed AnalyticInitialIdealDepth AnalyticInitialIdealTangent TangentConeUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Hull.
Variable R:realType.
Variable n:nat.
Local Notation X:=(R_n R n).
Local Notation B:=(@euclidean_inner_product R n).
Local Notation hB:=(@euclidean_inner_productP R n).
Local Notation NX:=(inner_norm hB).
Local Notation hNX:=(inner_norm_real_norm hB).
Local Notation T:=(Topological.clone (real_norm_metric_space hNX) _).
Local Notation G:=[the comNzRingType of (@analytic_germ_ring R X NX hNX 0)].
Local Notation e:=(@coordinate_basis R n).
Local Notation he:=(@coordinate_basisP R n).
Local Notation omega:=(dual_basis he).
Local Notation ideal:=(@AnalyticSetIdeal.value R X NX hNX 0).
Local Notation depth:=(@AnalyticDepth.value R X B hB n e he omega).

(** Source for [analytic_tangent_hull_depth_bound]: the
    original analytic-hull dimension inequality in 3.4.11,
    p. 338, in its defining ideal-depth form.
    The hull uses the actual tangent vanishing ideal;
    its finite generation is proved internally. *)
Theorem analytic_tangent_hull_depth_bound (S:set X):
  @is_analytic_variety_germ R X NX hNX 0 (@set_germ T 0%R S) ->
  @set_germ T 0%R S<>@set_germ T 0%R set0 ->
  exists hJ:@is_finitely_generated_commutative_ideal G (ideal (@set_germ T 0%R (norm_tangent_cone NX S 0))),
    let nu:=@IdealVarietyGerm.value R X NX hNX 0
      (ideal (@set_germ T 0%R (norm_tangent_cone NX S 0))) hJ in
    @is_analytic_variety_germ R X NX hNX 0 nu /\
    set_germ_subset (@set_germ T 0%R (norm_tangent_cone NX S 0)) nu /\
    (depth (ideal nu)<=depth (ideal (@set_germ T 0%R S)))%N.
Proof.
move=>hAnalytic hNonempty.
pose sigma:=@set_germ T 0%R (norm_tangent_cone NX S 0).
have hJ:=@euclidean_analytic_germ_ring_noetherian R n 0 (ideal sigma)
  (@analytic_set_ideal_ring_laws R X NX hNX 0 sigma).
exists hJ=>nu;split.
- exact:(@ideal_variety_germ_is_variety R X NX hNX 0 _ nu
    (@IdealVarietyGerm.laws R X NX hNX 0 _ hJ)).
split;first exact:(@set_germ_in_variety_of_its_ideal R X NX hNX 0 sigma hJ).
rewrite (@vanishing_ideal_variety_recovery R X NX hNX 0 sigma hJ).
apply:(leq_trans _ (@analytic_initial_ideal_depth_bound R n (@set_germ T 0%R S) hAnalytic hNonempty)).
apply:(@analytic_ideal_depth_antitone R X B hB n e he omega).
exact:(@analytic_initial_ideal_tangent_inclusion R X NX hNX S).
Qed.
End Hull.
