(** Federer (1969), corrected 3.4.8(11), pp. 327, 333–335:
    choose actual local representatives of the exceptional
    cut and regular complement. Exact germ equations
    give the required local set identities. Relative
    closedness of the original variety then gives
    the complete corrected boundary containment. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric NormDifferentialUP NormBoundedLinearTopology
  NormAnalyticUP SetGermUP SetGermSealed SetGermExistence SetGermLaws SetGermOrder SetGermLocality
  SetGermCutEquation FiniteAnalyticVarietyUP FiniteAnalyticVarietyBoundary FiniteAnalyticVarietyLaws
  FiniteAnalyticVarietyRestriction FiniteAnalyticSingleEquation FiniteAnalyticVarietyClosure.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section LocalCut.
Variable R:realType.
Variable X:lmodType R.
Variable NX:X->R.
Variable hNX:is_real_norm NX.
Local Notation T:=(Topological.clone (real_norm_metric_space hNX) _).
Local Notation germ:=(@set_germ T 0).

(** Source for [analytic_variety_cut_local_data]:
    the original regular S avoids the exceptional
    G and S0, and its closure lies
    in S union G inside the chosen
    neighbourhood, 3.4.8(11), pp. 333–335,
    with the published p. 327 line 24 correction.
    All asserted containments concern actual sets. *)
Theorem analytic_variety_cut_local_data (U H D S0:set X) (phi:X->R^o)
    (gamma:@set_germ_space T 0):
  U 0 ->@is_finite_analytic_variety R X NX hNX U H ->
  @norm_analytic R X R^o NX (fun z:R^o=>`|z|) hNX (@scalar_absolute_value_norm R) U phi ->
  gamma = @SetGerms.meet T 0 (germ H) (germ [set x|phi x=0]) ->
  germ D = @SetGerms.meet T 0 (germ H) (@SetGerms.neg T 0 gamma) ->
  set_germ_subset (@SetGerms.meet T 0 (germ H) (germ S0)) gamma ->
  exists A E:set X,@open T A /\A 0 /\A `<=` U /\
    @is_finite_analytic_variety R X NX hNX A E /\germ E = gamma /\E `<=` H /\
    (forall x,D x ->A x ->H x /\~S0 x) /\
    (forall x,D x ->~E x) /\
    A `&` @closure T D `<=` D `|` E.
Proof.
move=>hU0 hH hPhi hGamma hD hS0.
have hDRegular:germ D = germ [set x|H x /\phi x<>0].
  rewrite hD hGamma;exact:set_germ_cut_regular_equation.
have [W [hW [hW0 hEqual]]]:=(@set_germ_equality_original T 0 D [set x|H x /\phi x<>0]).1 hDRegular.
have hGammaSet:gamma = germ (H `&` [set x|phi x=0]).
  by rewrite hGamma (@set_germ_intersection_equation T 0 _ _ _ (@SetGerms.laws T 0)).
rewrite (@set_germ_intersection_equation T 0 _ _ _ (@SetGerms.laws T 0)) hGammaSet in hS0.
have [V [hV [hV0 hS0Zero]]]:=(@set_germ_subset_original T 0
  (H `&` S0) (H `&` [set x|phi x=0])).1 hS0.
pose A:set X:=U `&` (W `&` V).
pose E:set X:=A `&` (H `&` [set x|phi x=0]).
have hA:@open T A:=openI hH.1 (openI hW hV).
have hA0:A 0 by split;last split.
have hAU:A `<=` U by move=>x hx;exact:hx.1.
have hHInside:H `<=` U:=finite_analytic_variety_domain_inside hH.
have hEquationVar:=@finite_analytic_single_equation R X NX hNX U phi hPhi.
have hIntersection:=@finite_analytic_variety_intersection R X NX hNX U H
  (U `&` [set x|phi x=0]) hH hEquationVar.
have hSame:H `&` (U `&` [set x|phi x=0]) = H `&` [set x|phi x=0].
  apply/seteqP;split.
  - by move=>x [hx [_ hZero]];split.
  - move=>x [hx hZero];split;first exact:hx.
    split;[exact:hHInside x hx|exact:hZero].
rewrite hSame in hIntersection.
have hE:@is_finite_analytic_variety R X NX hNX A E.
  exact:finite_analytic_variety_open_restriction hIntersection hA hAU.
have hEGerm:germ E = gamma.
  rewrite /E (@set_germ_neighbourhood_intersection T 0 A _ hA hA0);exact:esym hGammaSet.
have hDGood x (hx:D x) (hAx:A x):H x /\phi x<>0.
  have hMember:([set x|H x /\phi x<>0] `&` W) x.
    rewrite -hEqual;split;[exact:hx|exact:hAx.2.1].
  exact:hMember.1.
have hInside x (hx:D x) (hAx:A x):H x /\~S0 x.
  have [hHx hNonzero]:=hDGood x hx hAx;split;first exact:hHx.
  move=>hS0x;exact:hNonzero (hS0Zero x (conj hHx hS0x) hAx.2.2).2.
have hClosureH:A `&` @closure T D `<=` H.
  exact:(@finite_analytic_variety_local_closure R X NX hNX U H A D hH hA hAU
    (fun x hx hAx=>(hDGood x hx hAx).1)).
exists A,E;split;first exact:hA.
split;first exact:hA0.
split;first exact:hAU.
split;first exact:hE.
split;first exact:hEGerm.
split;first by move=>x [_ [hx _]].
split;first exact:hInside.
split.
- move=>x hx [hAx [_ hZero]];exact:(hDGood x hx hAx).2 hZero.
- move=>x [hAx hClosure];have hHx:=hClosureH x (conj hAx hClosure).
  case:(pselect (phi x=0))=>hZero.
  + right;split;first exact:hAx.
    by split.
  + left;have hMember:(D `&` W) x.
      rewrite hEqual;split;first by split.
      exact:hAx.2.1.
    exact:hMember.1.
Qed.
End LocalCut.
