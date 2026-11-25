(** Federer (1969), 3.4.8, pp. 326–337:
    actual regressions for the zero ambient dimension,
    a singular planar crossing and the nonempty counting
    atom in the relative-open dimension theorem. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric GrassmannAbbreviations FiniteCoordinates FiniteDualDimension
  EuclideanInnerProduct InnerNorm InnerMetric HilbertFormCompactness SetGermUP SetGermSealed
  SetGermExistence SetGermLaws SetGermOrder SetGermBoundary FiniteAnalyticVarietyUP
  FiniteAnalyticVarietyBoundary AnalyticVarietyGermUP AnalyticVarietyGermBooleanClosure
  GermVanishingSealed AnalyticGermRing CommutativeIdealUP IdealVarietyGermSealed IdealVarietyVanishingLaws
  AnalyticFiniteStratificationUP AnalyticReductionDepthUP AnalyticStratification EuclideanPointAnalyticVariety
  NormAnalyticScalarProducts EuclideanScalarCoordinateAnalytic EuclideanSubmanifoldUP
  HausdorffMeasure HausdorffCountableNull HausdorffCountingMeasure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [analytic_stratification_zero_ambient_regression]: the
    original zero-dimensional endpoint of 3.4.8(11), p. 333.
    In R^0 the whole space is the nonempty point;
    the corrected decomposition retains every boundary law. *)
Example analytic_stratification_zero_ambient_regression (R:realType):
  let X:=R_n R 0 in
  let hN:=inner_norm_real_norm (@euclidean_inner_productP R 0) in
  let T:=Topological.clone (real_norm_metric_space hN) _ in
  exists mu,exists V S G:'I_mu->set X,
    @is_analytic_finite_stratification R 0 (@set_germ T 0 setT) (@set_germ T 0 set0)
      0 setT set0 mu V S G.
Proof.
move=>X hN T.
have hNonempty:@set_germ T 0 setT<>@set_germ T 0 set0.
  move=>h;exact:(@set_germ_empty_not_whole T 0) (esym h).
have hBound:=analytic_reduction_depth_bound
  (@AnalyticDepth.laws R X (@euclidean_inner_product R 0) (@euclidean_inner_productP R 0)
    0 (@coordinate_basis R 0) (@coordinate_basisP R 0) (dual_basis (@coordinate_basisP R 0))
    (@AnalyticSetIdeal.value R X _ hN 0 (@set_germ T 0 setT))).
have hDepth: @AnalyticDepth.value R X (@euclidean_inner_product R 0) (@euclidean_inner_productP R 0)
    0 (@coordinate_basis R 0) (@coordinate_basisP R 0) (dual_basis (@coordinate_basisP R 0))
    (@AnalyticSetIdeal.value R X _ hN 0 (@set_germ T 0 setT))=0%N.
  by apply/eqP;rewrite -leqn0.
exact:(@federer_3_4_8_11 R 0 _ _ 0 setT set0
  (@analytic_variety_germ_whole R X _ hN 0) hNonempty hDepth Logic.I
  (@finite_analytic_variety_domain_empty R X _ hN setT openT) erefl).
Qed.

(** Source for [analytic_stratification_crossing_regression]: actual
    xy=0 in R^2 is a nonempty singular analytic
    variety. The full original theorem 3.4.8(11),
    p. 327, gives all corrected stratum laws with
    the actual ideal depth, bounded by two. *)
Example analytic_stratification_crossing_regression (R:realType):
  let X:=R_n R 2 in
  let NX:=inner_norm (@euclidean_inner_productP R 2) in
  let hN:=inner_norm_real_norm (@euclidean_inner_productP R 2) in
  let T:=Topological.clone (real_norm_metric_space hN) _ in
  let H:set X:=[set x|x ord0*x ord_max=0] in
  let d:=@AnalyticDepth.value R X (@euclidean_inner_product R 2) (@euclidean_inner_productP R 2)
    2 (@coordinate_basis R 2) (@coordinate_basisP R 2) (dual_basis (@coordinate_basisP R 2))
    (@AnalyticSetIdeal.value R X NX hN 0 (@set_germ T 0 H)) in
  (d<=2)%N /\exists mu,exists V S G:'I_mu->set X,
    @is_analytic_finite_stratification R 2 (@set_germ T 0 H) (@set_germ T 0 set0)
      d setT set0 mu V S G.
Proof.
move=>X NX hN T H d;split;first exact:analytic_reduction_depth_bound (@AnalyticDepth.laws _ _ _ _ _ _ _ _ _).
have hH:@is_finite_analytic_variety R X NX hN setT H.
  split;first exact:openT.
  exists (Finite.clone 'I_1 _),(fun (_:'I_1) (x:X)=>x ord0*x ord_max);split.
  - move=>i;exact:norm_analytic_scalar_product
      (@euclidean_scalar_coordinate_analytic R 2 ord0) (@euclidean_scalar_coordinate_analytic R 2 ord_max).
  - move=>x;split;first by move=>hx;split=>// i.
    by move=>[_ h];exact:h ord0.
have hNonempty:@set_germ T 0 H<>@set_germ T 0 set0.
  move/set_germ_equality_original=>[U [hU [hU0 hEqual]]].
  have hMember:(set0 `&` U) (0:X).
    rewrite -hEqual;split;last exact:hU0.
    rewrite /H.
    change ((0:X) ord0*(0:X) ord_max=0).
    by rewrite !ffunE mul0r.
  exact:hMember.1.
have hGerm:@is_analytic_variety_germ R X NX hN 0 (@set_germ T 0 H).
  exists setT,H;split;first exact:Logic.I;by split.
exact:(@federer_3_4_8_11 R 2 _ _ d setT set0 hGerm hNonempty erefl Logic.I
  (@finite_analytic_variety_domain_empty R X NX hN setT openT) erefl).
Qed.

(** Source for [analytic_relative_open_point_regression]: the
    actual origin in R^2 is relatively open in
    itself, has H^1 mass zero and H^0 mass one.
    Conclusion 3.4.8(16), p. 328, gives its
    nonempty analytic hull depth zero; no atom is discarded. *)
Example analytic_relative_open_point_regression (R:realType):
  let X:=R_n R 2 in
  let NX:=inner_norm (@euclidean_inner_productP R 2) in
  let hN:=inner_norm_real_norm (@euclidean_inner_productP R 2) in
  let T:=Topological.clone (real_norm_metric_space hN) _ in
  let ideal:=@AnalyticSetIdeal.value R X NX hN 0 in
  @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R 2)) 0 [set (0:X)]= 1%E /\
  exists hI:@is_finitely_generated_commutative_ideal
      [the comNzRingType of (@analytic_germ_ring R X NX hN 0)] (ideal (@set_germ T 0 [set 0])),
    @AnalyticDepth.value R X (@euclidean_inner_product R 2) (@euclidean_inner_productP R 2)
      2 (@coordinate_basis R 2) (@coordinate_basisP R 2) (dual_basis (@coordinate_basisP R 2))
      (ideal (@IdealVarietyGerm.value R X NX hN 0 _ hI))=0%N.
Proof.
move=>X NX hN T ideal;split;first exact:hausdorff_zero_singleton.
have hOpen:@relatively_open_set T [set (0:X)] [set 0].
  exists setT;split;first exact:openT;by rewrite setIT.
have hNull:=@hausdorff_positive_degree_singleton_zero R
  (inner_metric_space (@euclidean_inner_productP R 2)) 1%N (0:X) (ltn0Sn 0).
have [hI hBound]:=@federer_3_4_8_16 R 2 [set 0] [set 0] 0
  (@euclidean_point_analytic_germ R 2) hOpen hNull.
exists hI.
case:hBound=>hBound;last by apply/eqP;rewrite -leqn0.
exfalso.
have hContained:=@set_germ_in_variety_of_its_ideal R X NX hN 0 (@set_germ T 0 [set 0]) hI.
rewrite hBound in hContained.
have hEmpty:=set_germ_subset_empty hContained.
move:hEmpty=>/set_germ_equality_original [U [hU [hU0 hEqual]]].
have hMember:(set0 `&` U) (0:X) by rewrite -hEqual;split.
exact:hMember.1.
Qed.
