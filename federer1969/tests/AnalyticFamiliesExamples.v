(** Federer (1969), 3.4.9, p. 337:
    actual punctured-line and positive-radius ball regressions,
    retaining the zero ambient dimension and the original
    whole-plane depth in the uniform-ball theorem. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals topology.
From Federer Require Import RealNormUP NormMetric GrassmannAbbreviations FiniteCoordinates FiniteDualDimension
  EuclideanInnerProduct InnerNorm HilbertFormCompactness SetGermUP SetGermBoundary
  FiniteAnalyticVarietyUP FiniteAnalyticVarietyBoundary AnalyticVarietyGermUP
  AnalyticVarietyGermBooleanClosure EuclideanPointAnalyticVariety LocallyFiniteFamilyUP
  FunctionalAnalyticWhole AnalyticFamilies AnalyticFiniteStratificationUP
  AnalyticDepthSealed AnalyticReductionZeroIdeal GermVanishingSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [analytic_punctured_line_family_regression]: the
    difference of the actual whole line and its
    origin has a locally finite component family by
    3.4.9, p. 337. The positive and negative
    coordinate points remain in the difference. *)
Example analytic_punctured_line_family_regression (R:realType):
  let X:=R_n R 1 in
  let NX:=inner_norm (@euclidean_inner_productP R 1) in
  let hN:=inner_norm_real_norm (@euclidean_inner_productP R 1) in
  let T:=Topological.clone (real_norm_metric_space hN) _ in
  let D:set X:=setT `\` [set 0] in
  let v:=@coordinate_basis R 1 ord0 in
  D v /\D (-v) /\
  @is_locally_finite_family_on T [the choiceType of (set T)] setT
    (@connected_component T D @` D) (fun C=>C).
Proof.
move=>X NX hN T D v.
have hV:v<>0.
  move=>hZero;have hAt:=congr1 (fun x:X=>x ord0) hZero.
  rewrite /v /coordinate_basis !ffunE eqxx in hAt.
  by move/eqP:hAt;rewrite oner_eq0.
split;first by split=>//;exact:hV.
split.
- split;first exact:Logic.I.
  move=>hNegative;apply:hV;have h:=congr1 (fun x:X=>-x) hNegative.
  by rewrite opprK oppr0 in h.
- have hWhole:@is_analytic_set_in R X NX hN setT setT.
    move=>a _;exists setT,setT;split;first exact:Logic.I.
    split;last reflexivity;exact:finite_analytic_variety_domain_whole openT.
  have hPoint:@is_analytic_set_in R X NX hN setT [set 0].
    move=>a _;exists setT,[set 0];split;first exact:Logic.I.
    split;last reflexivity;exact:euclidean_point_analytic_variety.
  exact:(@federer_3_4_9_local_finiteness R 1 setT setT [set 0] openT hWhole hPoint).
Qed.

(** Source for [analytic_ball_all_radii_regression]: the actual
    ball in every ambient dimension, including zero,
    has finitely many components for every positive radius.
    This tests the absence of exceptional radii in
    the component argument of 3.4.9, p. 337. *)
Example analytic_ball_all_radii_regression (R:realType) n (r:R):
  0<r ->
  finite_set (@connected_component
    (Topological.clone (real_norm_metric_space (inner_norm_real_norm (@euclidean_inner_productP R n))) _)
    [set x|inner_norm (@euclidean_inner_productP R n) x<r] @`
    [set x|inner_norm (@euclidean_inner_productP R n) x<r]).
Proof.
move=>hR.
have h:=@functional_analytic_ball_finite_components R n n setT setT r
  (@functional_analytic_whole R n) hR (fun _ _=>Logic.I).
by rewrite setTI in h.
Qed.

(** Source for [analytic_whole_plane_uniform_ball_regression]: the
    actual whole plane has depth two and admits
    one original stratification valid after restriction to
    every sufficiently small positive ball, as asserted
    in 3.4.9, p. 337. Every premise is proved. *)
Example analytic_whole_plane_uniform_ball_regression (R:realType):
  let X:=R_n R 2 in
  let NX:=inner_norm (@euclidean_inner_productP R 2) in
  let hN:=inner_norm_real_norm (@euclidean_inner_productP R 2) in
  let T:=Topological.clone (real_norm_metric_space hN) _ in
  exists mu,exists V S G:'I_mu->set X,exists rho:R,
    0<rho /\@is_analytic_finite_stratification R 2 (@set_germ T 0 setT)
      (@set_germ T 0 set0) 2 setT set0 mu V S G /\
    forall r:R,0<r ->r<rho ->
      @is_analytic_finite_stratification R 2 (@set_germ T 0 setT)
        (@set_germ T 0 set0) 2 setT set0 mu
        (fun _=>[set x|NX x<r]) (fun i=>[set x|NX x<r] `&` S i)
        (fun i=>[set x|NX x<r] `&` G i).
Proof.
move=>X NX hN T.
have hNonempty:@set_germ T 0 setT<>@set_germ T 0 set0.
  move=>h;exact:(@set_germ_empty_not_whole T 0) (esym h).
have hDepth:@AnalyticDepth.value R X (@euclidean_inner_product R 2) (@euclidean_inner_productP R 2)
    2 (@coordinate_basis R 2) (@coordinate_basisP R 2) (dual_basis (@coordinate_basisP R 2))
    (@AnalyticSetIdeal.value R X NX hN 0 (@set_germ T 0 setT))= 2%N.
  rewrite (@analytic_whole_germ_ideal_zero R X NX hN 0).
  exact:analytic_depth_zero_ideal.
exact:(@federer_3_4_9_uniform_balls R 2 _ _ 2 setT set0
  (@analytic_variety_germ_whole R X NX hN 0) hNonempty hDepth Logic.I
  (@finite_analytic_variety_domain_empty R X NX hN setT openT) erefl).
Qed.
