(** Federer (1969), corrected 3.4.8(11), pp. 327, 333–335:
    transport every stratum, neighbourhood and exceptional
    boundary through the original orthogonal coordinates.
    Actual finite equations, independent differentials, components,
    closure containments and ideal depths are preserved
    by the project's existing public interfaces. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals topology.
From Federer Require Import Hom RealNormUP NormMetric GrassmannAbbreviations FiniteCoordinates FiniteDualDimension
  EuclideanInnerProduct InnerNorm HilbertFormCompactness NormFiniteLinearBound NormBoundedLinearTopology
  OrthogonalGroupTopology OrthogonalGroupHaarMeasure LinearBasis SetGermUP SetGermSealed SetGermLaws
  SetGermContinuousPreimage FiniteAnalyticVarietyUP FiniteAnalyticLinearPullback
  FunctionalAnalyticSubmanifoldUP FunctionalAnalyticLinearPullback InverseMapComponentFiniteness
  GermVanishingSealed AnalyticDepthSealed AnalyticRotatedVanishingIdeal AnalyticRotatedIdealDepth
  AnalyticFiniteStratificationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section OrthogonalPullback.
Variable R:realType.
Variable n:nat.
Local Notation X:=(R_n R n).
Local Notation B:=(@euclidean_inner_product R n).
Local Notation hB:=(@euclidean_inner_productP R n).
Local Notation NX:=(inner_norm hB).
Local Notation hNX:=(inner_norm_real_norm hB).
Local Notation T:=(Topological.clone (real_norm_metric_space hNX) _).
Local Notation e:=(@coordinate_basis R n).
Local Notation he:=(@coordinate_basisP R n).
Local Notation omega:=(dual_basis he).
Local Notation O:=(@orthogonal_group R X B hB n e he).
Local Notation germ:=(@set_germ T 0).
Local Notation depth:=(@AnalyticDepth.value R X B hB n e he omega).
Local Notation ideal:=(@AnalyticSetIdeal.value R X NX hNX 0).
Variable g:O.
Local Notation u:=(@orthogonal_element_map R X B hB n e he g).

(** Source for [analytic_stratification_orthogonal_pullback]:
    return the complete corrected stratification from the
    original orthogonal coordinates, 3.4.8(11),
    pp. 327, 333–335. Every input is an
    already proved stratum law; no additional numbered
    theorem premise is introduced by this transport. *)
Theorem analytic_stratification_orthogonal_pullback (H U0 S0:set X) m mu (V S G:'I_mu->set X):
  @is_analytic_finite_stratification R n (germ H) (germ S0) m U0 S0 mu V S G ->
  @is_analytic_finite_stratification R n (germ (u @^-1` H)) (germ (u @^-1` S0))
    m (u @^-1` U0) (u @^-1` S0) mu
    (fun i=>u @^-1` V i) (fun i=>u @^-1` S i) (fun i=>u @^-1` G i).
Proof.
move=>hLaws.
have [mulO [invO [unitO hO]]]:=@orthogonal_group_restriction_exists R X B hB n e he.
pose v:=@orthogonal_element_map R X B hB n e he (invO g).
have [hVU hUV]:=@orthogonal_element_inv R X B hB n e he mulO invO unitO hO g.
have hUBound:=@norm_finite_linear_bounded R X X NX NX hNX hNX n e he u.
have hVBound:=@norm_finite_linear_bounded R X X NX NX hNX hNX n e he v.
have hU:=@norm_bounded_linear_continuous R X X NX NX hNX hNX u hUBound.
have hV:=@norm_bounded_linear_continuous R X X NX NX hNX hNX v hVBound.
have hU0:u 0 = 0:=linear0 u.
have hOnto y:exists x,u x = y by exists (v y);exact:hUV y.
have hDepth E:depth (ideal (germ (u @^-1` E))) = depth (ideal (germ E)).
  rewrite -(@analytic_rotated_vanishing_ideal R X B hB n e he g E).
  exact:(@analytic_rotated_ideal_depth R X B hB n e he omega mulO invO unitO hO (ideal (germ E)) g).
constructor.
- move=>i;have [hOpen [hZero hInside]]:=analytic_stratification_neighbourhoods hLaws i.
  split;first exact:(@open_comp T T u (V i) (fun x _=>hU x) hOpen).
  split;first by change (V i (u 0));rewrite hU0.
  move=>x hx;exact:hInside (u x) hx.
- have hGerm:=analytic_stratification_germ hLaws.
  rewrite (@set_germ_complement_equation T 0 _ _ _ (@SetGerms.laws T 0))
    (@set_germ_intersection_equation T 0 _ _ _ (@SetGerms.laws T 0)) in hGerm.
  have hTransport:=@set_germ_continuous_preimage_equality T T u 0 0
    (H `&` ~` S0) (\bigcup_i S i) hU hU0 hGerm.
  rewrite (@set_germ_complement_equation T 0 _ _ _ (@SetGerms.laws T 0))
    (@set_germ_intersection_equation T 0 _ _ _ (@SetGerms.laws T 0)).
  have hUnion:u @^-1` (\bigcup_i S i) = \bigcup_i (u @^-1` S i).
    apply/seteqP;split.
    + move=>x [i _ hx];by exists i.
    + move=>x [i _ hx];by exists i.
  by rewrite -hUnion.
- move=>i;have [d [hDM hFunctional]]:=analytic_stratification_functional hLaws i.
  exists d;split;first exact:hDM.
  exact:functional_analytic_linear_pullback hUBound hOnto hFunctional.
- move=>i;exact:(@inverse_map_component_finiteness T T u v (S i) hU hV hVU hUV
    (analytic_stratification_components hLaws i)).
- move=>i x hx hEarlierSource.
  have hOriginal:=@analytic_stratification_disjoint R n (germ H) (germ S0) m U0 S0 mu V S G hLaws i.
  apply:(@hOriginal (u x) hx).
  case:hEarlierSource=>[hS0x|[j hEarlier hSx]].
  + by left.
  + right;by exists j.
- move=>i x [hVx hClosure].
  have hPreclosed:@closed T (u @^-1` @closure T (S i)).
    exact:(@preimage_closed T T u (@closure T (S i)) (fun x _=>hU x) (@closed_closure T (S i))).
  have hSub:(u @^-1` S i) `<=` (u @^-1` @closure T (S i)).
    move=>y hy;exact:subset_closure hy.
  have hClosureImage:@closure T (S i) (u x):=hPreclosed x
    (@closureS T _ _ hSub x hClosure).
  have hOriginal:=@analytic_stratification_boundary R n (germ H) (germ S0) m U0 S0 mu V S G hLaws i.
  exact:(@hOriginal (u x) (conj hVx hClosureImage)).
- move=>i;exact:finite_analytic_linear_pullback hUBound (analytic_stratification_boundary_analytic hLaws i).
- move=>i;have [hEmpty|hSmaller]:=analytic_stratification_boundary_dimension hLaws i.
  + left;have h:=@set_germ_continuous_preimage_equality T T u 0 0 (G i) set0 hU hU0 hEmpty.
    by rewrite preimage_set0 in h.
  + right;by rewrite hDepth.
- move=>i x hx.
  have hOriginal:=@analytic_stratification_boundary_earlier R n (germ H) (germ S0) m U0 S0 mu V S G hLaws i.
  have [hS0x|[j hEarlier hSx]]:=@hOriginal (u x) hx.
  + by left.
  + right;by exists j.
Qed.
End OrthogonalPullback.
