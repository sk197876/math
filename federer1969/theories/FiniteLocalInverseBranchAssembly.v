(** Federer (1969), 3.4.8(10), p. 332:
    finite fibres, local inverse charts and
    compact inverse images give local finite
    branch families. The disjoint source
    neighbourhoods are proved to exist by
    finite metric separation. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import RelativeLocalInverseUP FiniteFibreEnumerationUP FiniteDisjointMetricBalls
  MetricClosedBalls FiniteNearbyFibreBranches.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [finite_local_inverse_branch_assembly]:
    every original finite fibre continues to
    exactly the same number of distinct
    local branches, 3.4.8(10), p. 332.
    Compactness rules out additional points;
    finite metric separation supplies disjoint charts.
    Empty initial fibres remain allowed. *)
Theorem finite_local_inverse_branch_assembly (R:realType) (X Y:metricType R)
    (I:finType) (P:X->Y) (Z:set X) (C:set Y) (y:Y) (a:I->X):
  continuous P ->nbhs y C ->compact [set x|Z x /\C (P x)] ->
  is_finite_fibre_enumeration P Z y a ->
  (forall x,Z x ->exists U V psi,is_relative_local_inverse P Z x U V psi) ->
  exists psi:I->Y->X,
    (forall i,psi i y = a i) /\
    (forall i,{for y,continuous (psi i)}) /\
    nbhs y [set z|is_finite_fibre_enumeration P Z z (fun i=>psi i z)].
Proof.
move=>hP hC hCompact hEnumeration hCharts.
have [hPoints [hCover hInjective]]:=hEnumeration.
have hExists i:exists c:(set X*set Y*(Y->X))%type,
    is_relative_local_inverse P Z (a i) c.1.1 c.1.2 c.2.
  have [U [V [psi hChart]]]:=hCharts (a i) (hPoints i).1.
  by exists (U,V,psi).
have [c hChart]:=choice hExists.
pose U0:=fun i:I=>(c i).1.1.
pose V0:=fun i:I=>(c i).1.2.
pose psi:=fun i:I=>(c i).2.
have hAt i:U0 i (a i) /\open (U0 i) /\open (V0 i) /\V0 i (P (a i)) /\
    (forall z,V0 i z ->Z (psi i z) /\U0 i (psi i z) /\P (psi i z) = z) /\
    (forall x,Z x ->U0 i x ->psi i (P x) = x) /\
    forall z,V0 i z ->{for z,continuous (psi i)}:=hChart i.
have hBase i:psi i y = a i.
  rewrite -(hPoints i).2;exact:(hAt i).2.2.2.2.2.1 (a i) (hPoints i).1 (hAt i).1.
have [r [hR hSeparate]]:=@finite_disjoint_metric_balls R X I a hInjective.
pose U:=fun i:I=>U0 i `&` [set x|mdist (a i) x<r].
pose V:=fun i:I=>V0 i `&` (psi i @^-1` U i).
have hU i:open (U i):=openI (hAt i).2.1 (metric_open_ball_open (a i) r).
have hCentre i:U i (a i).
  rewrite /U /=;split;first exact:(hAt i).1.
  by rewrite mdistxx.
have hV i:nbhs y (V i).
  have hVi:V0 i y by rewrite -(hPoints i).2;exact:(hAt i).2.2.2.1.
  have hVNear:nbhs y (V0 i) by have h:=(hAt i).2.2.1;rewrite openE in h;exact:h y hVi.
  have hUNear:nbhs (psi i y) (U i).
    rewrite hBase;have h:=hU i;rewrite openE in h;exact:h (a i) (hCentre i).
  exact:filterI hVNear ((hAt i).2.2.2.2.2.2 y hVi _ hUNear).
have hMaps i z (hz:V i z):Z (psi i z) /\U i (psi i z) /\P (psi i z) = z.
  have h:=(hAt i).2.2.2.2.1 z hz.1;split;first exact:h.1.
  by split;[exact:hz.2|exact:h.2.2].
have hLocalInverse i x:Z x ->U i x ->V i (P x) ->psi i (P x) = x.
  move=>hx hUix _;exact:(hAt i).2.2.2.2.2.1 x hx hUix.1.
have hDisjoint i j:i!=j ->forall x,U i x ->~U j x.
  move=>hIJ x hUI hUJ;exact:hSeparate i j hIJ x hUI.2 hUJ.2.
have hCoverU x:Z x ->P x = y ->exists i,U i x.
  move=>hx hPx;have [i hi]:=hCover x hx hPx;exists i;by rewrite -hi;exact:hCentre i.
exists psi;split;first exact:hBase.
split.
- move=>i;apply:(hAt i).2.2.2.2.2.2;rewrite -(hPoints i).2;exact:(hAt i).2.2.2.1.
- exact:(@finite_nearby_fibre_branches R X Y I P Z C y U V psi hP hC hCompact
    hU hV hMaps hLocalInverse hDisjoint hCoverU).
Qed.
