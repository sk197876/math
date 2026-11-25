(** Federer (1969), 3.4.11, p. 338:
    an actual finite family of original homogeneous
    polynomials contains the whole tangent cone in its
    global zero set. Its original global dimension is
    at most the original source-germ dimension. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric GrassmannAbbreviations FiniteCoordinates
  FiniteDualDimension EuclideanInnerProduct InnerNorm HilbertFormCompactness AnalyticGermUP AnalyticGermRing
  AnalyticGermRepresentatives SetGermUP GermVanishingUP GermVanishingSealed GermVanishingIdeal
  GermVanishingRepresentative CommutativeIdealUP EuclideanAnalyticGermNoetherian
  AnalyticDepthSealed AnalyticIdealDepthMonotonicity AnalyticVarietyGermUP NormAnalyticUP
  FiniteAnalyticVarietyUP FiniteZeroSetSealed TangentConeUP HomogeneousPolynomialFunctions
  AnalyticInitialFiniteFamily AnalyticInitialPolynomialLaws AnalyticInitialPolynomialGlobalAnalytic
  AnalyticInitialTangentVanishing AnalyticInitialIdealSealed AnalyticInitialIdealDepth
  AnalyticConeDimension AnalyticSetDimension.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Majorant.
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

(** Source for [analytic_finite_homogeneous_majorant_exists]: the
    full finite homogeneous polynomial conclusion of 3.4.11,
    p. 338, in indexed form. All
    original polynomials are retained, and the bound
    concerns their global zero set, rather than only
    its germ at the origin. *)
Theorem analytic_finite_homogeneous_majorant_exists (S:set X):
  @is_analytic_variety_germ R X NX hNX 0 (@set_germ T 0%R S) ->
  @set_germ T 0%R S<>@set_germ T 0%R set0 ->
  exists J:finType,exists k:J->nat,exists P:J->X->R,
    (forall j,(0<k j)%N /\@is_homogeneous_polynomial R X R^o (k j) (P j)) /\
    let V:=@FiniteZeroSet.value [the zmodType of R^o] X setT J P in
    (norm_tangent_cone NX S 0 `<=` V) /\
    (@analytic_set_dimension R n V<=depth (ideal (@set_germ T 0%R S)))%N.
Proof.
move=>hAnalytic hNonempty.
pose I:set G:=ideal (@set_germ T 0%R S).
pose K:set G:=@AnalyticInitialIdeal.value R X NX hNX I.
have [J [a [k [P [f [hFamily hGenerated]]]]]]:=
  @analytic_initial_finite_family_exists R X NX hNX I (@euclidean_analytic_germ_ring_noetherian R n 0).
have hInitial j:AnalyticInitialPolynomialUP.is_initial_analytic_germ_polynomial (a j) (k j) (P j).
  exact:(hFamily j).2.1.
have hProperties j:=@analytic_initial_polynomial_laws R X NX hNX (a j) (k j) (P j) (hInitial j).
have hPolynomial j:@norm_analytic R X R^o NX (fun t:R^o=>`|t|) hNX
    (@scalar_absolute_value_norm R) setT (P j).
  exact:(@analytic_initial_polynomial_global_analytic R X B hB n e he (a j) (k j) (P j) (hInitial j)).
exists J,k,P;split.
- move=>j;split;[exact:(hInitial j).1|exact:(hProperties j).1].
move=>V.
have hEquations:=@FiniteZeroSet.laws [the zmodType of R^o] X setT J P.
have hVAnalytic:@is_analytic_set_in R X NX hNX setT V.
  move=>x _;exists setT,V;split;first done.
  split;last reflexivity.
  split;first exact:openT.
  exists J,P;split;[exact:hPolynomial|exact:original_zero_set_membership hEquations].
have hCone (t:R) (ht:0<t) x (hx:V x):V (t*:x).
  apply/(original_zero_set_membership hEquations).
  split;first done.
  move=>j;by rewrite (hProperties j).2.2.1 ((original_zero_set_membership hEquations x).1 hx).2 // mulr0.
split.
- move=>v hv;apply/(original_zero_set_membership hEquations).
  split;first done.
  move=>j;exact:(@analytic_initial_polynomial_tangent_vanishes R X NX hNX S (a j) (k j) (P j)
    (hFamily j).1 (hInitial j) v hv).
- have hInclusion:K `<=` ideal (@set_germ T 0%R V).
    apply:(generated_commutative_ideal_minimal hGenerated
      (@analytic_set_ideal_ring_laws R X NX hNX 0 (@set_germ T 0%R V))).
    move=>beta [j <-];apply/(@analytic_set_ideal_representative_equation R X NX hNX 0 (f j) V).
    exists setT;split;first exact:openT.
    split;first done.
    move=>x hx _;rewrite (hFamily j).2.2.
    exact:((original_zero_set_membership hEquations x).1 hx).2 j.
  apply:(leq_trans (@analytic_cone_global_dimension_bound R n V hVAnalytic hCone)).
  apply:(leq_trans (@analytic_ideal_depth_antitone R X B hB n e he omega K
    (ideal (@set_germ T 0%R V)) hInclusion)).
  exact:(@analytic_initial_ideal_depth_bound R n (@set_germ T 0%R S) hAnalytic hNonempty).
Qed.
End Majorant.
