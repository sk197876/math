(** Federer (1969), 3.4.8(11), p. 333:
    an original irreducible component may be represented
    by an actual finite analytic variety inside the
    given representative. Germ containment supplies the
    required common neighbourhood before any strata are chosen. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RealNormUP NormMetric SetGermUP SetGermOrder SetGermLocality
  AnalyticVarietyGermUP FiniteAnalyticVarietyUP FiniteAnalyticVarietyRestriction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [analytic_subgerm_representative_inside]:
    retain actual component strata inside the original
    analytic representative in the finite irreducible
    reduction of 3.4.8(11), p. 333. *)
Theorem analytic_subgerm_representative_inside (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) (U H:set X)
    (alpha:@set_germ_space (Topological.clone (real_norm_metric_space hNX) _) 0):
  U 0 ->@open (real_norm_metric_space hNX) U ->
  @is_analytic_variety_germ R X NX hNX 0 alpha ->
  set_germ_subset alpha (@set_germ (Topological.clone (real_norm_metric_space hNX) _) 0 H) ->
  exists W C:set X,W 0 /\@is_finite_analytic_variety R X NX hNX W C /\
    @set_germ (Topological.clone (real_norm_metric_space hNX) _) 0 C=alpha /\C `<=` H /\W `<=` U.
Proof.
move=>hU0 hU [A [S [hA0 [hS hAlpha]]]] hInside.
pose T:=Topological.clone (real_norm_metric_space hNX) _.
rewrite -hAlpha in hInside.
have [V [hV [hV0 hLocal]]]:=(@set_germ_subset_original T 0 S H).1 hInside.
pose W:set X:=A `&` (U `&` V).
have hW:@open T W:=openI hS.1 (openI hU hV).
have hW0:W 0 by split;last split.
exists W,(W `&` S);split;first exact:hW0.
split;first exact:finite_analytic_variety_open_restriction hS hW (fun x hx=>hx.1).
split.
- rewrite (@set_germ_neighbourhood_intersection T 0 W S hW hW0);exact:hAlpha.
- split.
  + move=>x [hx hSx];exact:hLocal x hSx hx.2.2.
  + move=>x hx;exact:hx.2.1.
Qed.
