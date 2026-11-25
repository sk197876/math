(** Federer (1969), 3.4.9, p. 337:
    all corrected stratification laws survive the prescribed
    common ball restriction. The sphere-cut component theorem
    supplies the only additional finiteness argument. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets cardinality reals topology.
From Federer Require Import RealNormUP NormMetric GrassmannAbbreviations FiniteCoordinates FiniteDualDimension
  EuclideanInnerProduct InnerNorm HilbertFormCompactness SetGermUP SetGermSealed SetGermLaws SetGermLocality
  FiniteAnalyticVarietyRestriction FunctionalAnalyticOpenRestriction FunctionalAnalyticBallComponents
  AnalyticFiniteStratificationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section BallRestriction.
Variable R:realType.
Variable n:nat.
Local Notation X:=(R_n R n).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation T:=(Topological.clone (real_norm_metric_space hNX) _).
Local Notation germ:=(@set_germ T 0).

(** Source for [analytic_stratification_ball_restriction]: every
    corrected conclusion of 3.4.8(11) after the simultaneous
    replacements Vi=U(0,r) and Si=Si intersect U(0,r),
    as asserted in 3.4.9, p. 337. The
    boundary varieties are restricted to the same ball. *)
Theorem analytic_stratification_ball_restriction (alpha beta:@set_germ_space T 0)
    m (U0 S0:set X) mu (V S G:'I_mu->set X) r:
  @is_analytic_finite_stratification R n alpha beta m U0 S0 mu V S G ->
  0<r ->@open T [set x|NX x<r] ->
  [set x|NX x<r] `<=` U0 ->
  (forall i,[set x|NX x<=r] `<=` V i) ->
  @is_analytic_finite_stratification R n alpha beta m U0 S0 mu
    (fun _=>[set x|NX x<r])
    (fun i=>[set x|NX x<r] `&` S i)
    (fun i=>[set x|NX x<r] `&` G i).
Proof.
move=>hLaws hR hOpen hInside hClosedInside.
pose O:set X:=[set x|NX x<r].
have hZero:O 0 by change (is_true (NX 0<r));rewrite inner_norm0.
have hOV i:O `<=` V i by move=>x hx;exact:hClosedInside i x (ltW hx).
constructor.
- move=>i;split;first exact:hOpen.
  split;[exact:hZero|exact:hInside].
- have hUnion:(\bigcup_i (O `&` S i)) = O `&` (\bigcup_i S i).
    apply/seteqP;split.
    + move=>x [i _ [hxO hxS]];split;first exact:hxO;by exists i.
    + move=>x [hxO [i _ hxS]];exists i;last by split.
      exact:Logic.I.
  rewrite hUnion (@set_germ_neighbourhood_intersection T 0 O _ hOpen hZero).
  exact:analytic_stratification_germ hLaws.
- move=>i;have [d [hDM hFunctional]]:=analytic_stratification_functional hLaws i.
  exists d;split;first exact:hDM.
  exact:functional_analytic_open_restriction hFunctional hOpen (hOV i).
- move=>i;have [d [hDM hFunctional]]:=analytic_stratification_functional hLaws i.
  have hFinite:=@functional_analytic_ball_finite_components R n d (V i) (S i) r
    hFunctional hR (hClosedInside i).
  have hSame:S i `&` O=O `&` S i:=setIC _ _.
  by rewrite hSame in hFinite.
- move=>i x [hxO hxS] hEarlier.
  apply:(@analytic_stratification_disjoint R n alpha beta m U0 S0 mu V S G hLaws i x hxS).
  case:hEarlier=>[hS0|[j hJI [_ hSj]]];first by left.
  right;by exists j.
- move=>i x [hxO hxClosure].
  have hClosure:@closure T (S i) x.
    exact:(@closureS T (O `&` S i) (S i) (fun y hy=>hy.2) x hxClosure).
  have [hS|hG]:=@analytic_stratification_boundary R n alpha beta m U0 S0 mu V S G hLaws i x (conj (hOV i x hxO) hClosure).
  + left;by split.
  + right;by split.
- move=>i;exact:finite_analytic_variety_open_restriction
    (analytic_stratification_boundary_analytic hLaws i) hOpen (hOV i).
- move=>i.
  have hGerm:germ (O `&` G i)=germ (G i).
    exact:set_germ_neighbourhood_intersection hOpen hZero.
  rewrite hGerm;exact:analytic_stratification_boundary_dimension hLaws i.
- move=>i x [hxO hxG].
  have [hS0|[j hJI hxS]]:=@analytic_stratification_boundary_earlier R n alpha beta m U0 S0 mu V S G hLaws i x hxG.
  + by left.
  + right;exists j;last by split.
    exact:hJI.
Qed.
End BallRestriction.
