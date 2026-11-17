(** Federer (1969), 3.4.8(11), p. 333:
    common zeros of the original triangular
    regular equations have only the point
    germ. This connection combines the actual
    axis theorem, the original vanishing-ideal laws
    and one finite common neighbourhood. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric LinearBasis GrassmannAbbreviations FiniteCoordinates
  AnalyticGermRepresentatives AnalyticGermUP AnalyticGermRing SetGermUP SetGermSealed SetGermLaws SetGermOrder
  GermVanishingUP GermVanishingSealed GermVanishingRepresentative AnalyticPrefixCoordinatesUP
  AnalyticRegularLineIsolatedZero TriangularAnalyticZeroIsolation FiniteCoordinateSmallNeighbourhood
  PointedAnalyticPullbackUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [triangular_germ_point_containment]:
    the zero-dimensional base of the
    induction in 3.4.8(11), p. 333.
    Each actual prefix representative vanishes
    on the original set germ; finite
    directional regularity then isolates its centre. *)
Theorem triangular_germ_point_containment (R:realType) (X:lmodType R)
    (NX:X->R) (hNX:is_real_norm NX) n (e:'I_n->X) (he:is_basis e)
    (omega:'I_n->Hom X R^o) (hDual:forall i j,omega i (e j) = if i==j then 1 else 0)
    (P:forall j:'I_n,Hom X (R_n R (j:nat).+1))
    (f:'I_n->@analytic_representative_type R X NX hNX 0)
    (F:forall j:'I_n,R_n R (j:nat).+1->R^o) (d:'I_n->R)
    (sigma:@set_germ_space (Topological.clone (real_norm_metric_space hNX) _) 0):
  (forall j,is_analytic_prefix_projection omega (ltn_ord j) (P j)) ->
  (forall j,0<d j) ->
  (forall j t,0<`|t|<d j ->F j (t*:@coordinate_basis R (j:nat).+1 ord_max)<>0) ->
  (forall j x,analytic_representative_value (f j) x = F j (P j x)) ->
  (forall j,@AnalyticSetIdeal.value R X NX hNX 0 sigma (analytic_germ (f j))) ->
  set_germ_subset sigma (@set_germ (Topological.clone (real_norm_metric_space hNX) _) 0 [set 0]).
Proof.
move=>hP hPositive hAxis hValues hVanish.
pose T:=Topological.clone (real_norm_metric_space hNX) _.
have [S hS]:=@set_germ_has_representative T 0 sigma.
have hEach j:nbhs (0:T) [set x|S x ->F j (P j x) = 0].
  have hMembership:=hVanish j;rewrite -hS in hMembership.
  have [U [hU [hU0 hZero]]]:=(@analytic_set_ideal_representative_equation R X NX hNX 0 (f j) S).1 hMembership.
  have hNear:nbhs (0:T) U by rewrite openE in hU;exact:hU 0 hU0.
  apply:(filterS _ hNear)=>x hx hSx.
  rewrite -(hValues j x);exact:hZero x hSx hx.
have hCommon:=@filter_forall T 'I_n (fun j x=>S x ->F j (P j x) = 0)
  (nbhs (0:T)) (nbhs_filter (0:T)) hEach.
have hSmall:=@finite_coordinate_small_neighbourhood R X NX hNX n e he omega d hPositive.
have hPoint:nbhs (0:T) [set x|S x ->x = 0].
  apply:(filterS _ (filterI hCommon hSmall))=>x [hEq hBounds] hSx.
  exact:(@triangular_analytic_zero_isolation R X n e he omega hDual P F d hP hAxis x hBounds
    (fun j=>hEq j hSx)).
rewrite -hS;apply/set_germ_subset_original.
rewrite nbhsE in hPoint.
have [U [hU hU0] hSub]:=hPoint.
exists U;split;first exact:hU.
split;first exact:hU0.
move=>x hSx hUx;exact:hSub x hUx hSx.
Qed.
