(** Federer (1969), 3.4.12, p. 339: the real case
    supplies a neighbourhood with finitely many components of an
    analytic difference. Reuse the proved real stratification and
    its component finiteness after a common ball restriction,
    3.4.8(11) and 3.4.9, pp. 333–337. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals topology lra.
From Federer Require Import SetGermExistence NormDifferentialUP NormOpenDomainLaws NormBoundedLinearTopology FiniteNormCommonClosedBall FunctionalAnalyticBallComponents FiniteComponentCoverAssembly RealNormUP NormMetric GrassmannAbbreviations FiniteCoordinates FiniteDualDimension
  EuclideanInnerProduct InnerNorm HilbertFormCompactness SetGermUP SetGermSealed SetGermLaws SetGermLocality
  FiniteAnalyticVarietyUP FiniteAnalyticVarietyRestriction AnalyticVarietyGermUP
  GermVanishingSealed AnalyticDepthSealed AnalyticGermLocalRepresentative
  AnalyticFiniteStratificationUP AnalyticFiniteStratificationExistence FiniteStrataLocalComponentFiniteness.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section DifferenceComponents.
Variable R:realType.
Variable n:nat.
Local Notation X:=(R_n R n).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation T:=(Topological.clone (real_norm_metric_space hNX) _).
Local Notation germ:=(@set_germ T 0).
Local Notation depth:=(@AnalyticDepth.value R X (@euclidean_inner_product R n)
  (@euclidean_inner_productP R n) n (@coordinate_basis R n) (@coordinate_basisP R n)
  (dual_basis (@coordinate_basisP R n))).
Local Notation ideal:=(@AnalyticSetIdeal.value R X NX hNX 0).

(** Source for [analytic_difference_finite_neighbourhood]: the
    first assertion of 3.4.9, p. 337, at zero.
    Original local representatives provide a common equation
    neighbourhood. The proved strata stay in the original
    difference, so their finite components bound its actual
    components meeting a smaller neighbourhood. *)
Theorem analytic_difference_finite_neighbourhood (S D:set X):
  @is_analytic_variety_germ R X NX hNX 0 (germ S) ->
  @is_analytic_variety_germ R X NX hNX 0 (germ D) ->
  forall N:set X,@open T N ->N 0 ->
    exists O:set X,@open T O /\O 0 /\O `<=` N /\
      finite_set (@connected_component T (O `&` (S `\` D)) @` (O `&` (S `\` D))).
Proof.
move=>hS hD N hN hN0.
have [U [hU0 [_ hUS]]]:=@analytic_germ_local_representative R X NX hNX setT S Logic.I openT hS.
have [W [hW0 [hWU hWD]]]:=@analytic_germ_local_representative R X NX hNX U D hU0 hUS.1 hD.
have hWS:=@finite_analytic_variety_open_restriction R X NX hNX U W (U `&` S) hUS hWD.1 hWU.
have hSame:W `&` (U `&` S)=W `&` S.
  apply/seteqP;split.
  - by move=>x [hx [_ hSx]];split.
  - move=>x [hx hSx];split;first exact:hx.
    split;[exact:hWU x hx|exact:hSx].
rewrite hSame in hWS.
pose d:=depth (ideal (germ (W `&` S))).
have [mu [V [F [G [hLaws hInside]]]]]:=@analytic_finite_stratification_exists_at_bound R d n
  W (W `&` S) W (W `&` D) hW0 hWS hW0 hWD (leqnn d).
have hStratumInside i:F i `<=` S `\` D.
  move=>x hx;have [hxW hxS]:=hInside i x hx.
  split;first exact:hxS.
  move=>hxD;apply:(@analytic_stratification_disjoint R n
    (germ (W `&` S)) (germ (W `&` D)) d W (W `&` D) mu V F G hLaws i x hx).
  left;by split.
have hGerm:=analytic_stratification_germ hLaws.
rewrite (@set_germ_neighbourhood_intersection T 0 W S hWD.1 hW0)
  (@set_germ_neighbourhood_intersection T 0 W D hWD.1 hW0)
  (@set_germ_complement_equation T 0 _ _ _ (@SetGerms.laws T 0))
  (@set_germ_intersection_equation T 0 _ _ _ (@SetGerms.laws T 0)) in hGerm.
pose B:set X:=\bigcup_i F i.
have [E [hE [hE0 hEquality]]]:=(@set_germ_equality_original T 0 B (S `\` D)).1 (esym hGerm).
pose C:set X:=E `&` N.
have hC:@open T C:=openI hE hN.
have hC0:C 0 by split.
have hEach i:@open T (V i) /\V i 0.
  have h:=analytic_stratification_neighbourhoods hLaws i;split;[exact:h.1|exact:h.2.1].
have [rho [hRho hCommon]]:=@finite_norm_common_closed_ball R X NX hNX
  [the finType of 'I_mu] C V hC hC0 hEach.
pose r:=rho/2.
have hR:0<r by rewrite /r;lra.
have hUpper:r<rho by rewrite /r;lra.
pose O:set X:=[set x|NX x<r].
have hInterior x (hx:O x):norm_domain_interior NX O x.
  have hAt:NX (x-0)<r by rewrite subr0.
  have [epsilon [hEpsilon hLocal]]:=@norm_open_ball_domain_interior R X NX hNX 0 r x hAt.
  exists epsilon;split;first exact:hEpsilon.
  move=>u hu;have h:=hLocal u hu;by rewrite subr0 in h.
have hO:@open T O.
  rewrite openE=>x hx;exact:(@norm_domain_interior_neighbourhood R X NX hNX O x).1 (hInterior x hx).
have hO0:O 0.
  change (NX 0<r);rewrite inner_norm0;exact:hR.
have hOC:O `<=` C by move=>x hx;exact:(hCommon r hR hUpper x (ltW hx)).1.
have hFinite i:finite_set (@connected_component T (O `&` F i) @` (O `&` F i)).
  have [dimension [hDimension hFunctional]]:=analytic_stratification_functional hLaws i.
  have hClosed:[set x|NX x<=r] `<=` V i.
    move=>x hx;exact:(hCommon r hR hUpper x hx).2 i.
  have h:=@functional_analytic_ball_finite_components R n dimension (V i) (F i) r hFunctional hR hClosed.
  by rewrite setIC.
have hFiniteAll:finite_set (@connected_component T (O `&` (S `\` D)) @` (O `&` (S `\` D))).
  apply:(@finite_component_cover_assembly T 'I_mu setT (fun i=>O `&` F i) (O `&` (S `\` D))).
  - exact:finite_finset.
  - move=>i _;exact:hFinite i.
  - move=>i _ x [hx hF];split;first exact:hx;exact:hStratumInside i x hF.
  - move=>x [hx hDiff].
    have hBE:(B `&` E) x by rewrite hEquality;split;[exact:hDiff|exact:(hOC x hx).1].
    have [i _ hFi]:=hBE.1;exists i;split;first exact:Logic.I;by split.
exists O;split;first exact:hO.
split;first exact:hO0.
split;first by move=>x hx;exact:(hOC x hx).2.
exact:hFiniteAll.
Qed.
End DifferenceComponents.
