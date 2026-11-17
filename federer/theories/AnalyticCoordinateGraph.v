(** Federer (1969), 3.4.10, p. 338:
    analytic coordinate graphs used to verify the
    regular part of the cited surface.
    Reuse the independent functional-submanifold laws and
    actual differential calculus of 3.1.24, p. 240. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric GrassmannAbbreviations FiniteCoordinates
  FiniteIndependence EuclideanInnerProduct InnerNorm HilbertFormCompactness
  NormDifferentialUP NormDifferentialLinear NormDifferentialSubtraction NormBoundedLinearTopology
  NormAnalyticUP NormAnalyticOperations NormAnalyticLinear NormAnalyticConstant
  EuclideanScalarCoordinateMaps FunctionalAnalyticSubmanifoldUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [analytic_coordinate_graph_functional]: the
    analytic graph used on the negative-axis part
    of the example cited in 3.4.10,
    p. 338. The graph equation has
    derivative one in the omitted coordinate.
    This is a supporting consequence of the
    original functional-submanifold definition in 3.4.5, p. 321. *)
Theorem analytic_coordinate_graph_functional (R:realType) (U:set (R_n R 3))
    (f:R_n R 3->R) (j:'I_3):
  let X:=R_n R 3 in
  let NX:=inner_norm (@euclidean_inner_productP R 3) in
  let hNX:=inner_norm_real_norm (@euclidean_inner_productP R 3) in
  @open (real_norm_metric_space hNX) U ->
  @norm_analytic R X R^o NX (fun t=>`|t|) hNX (@scalar_absolute_value_norm R) U f ->
  (forall x,U x ->exists L:Hom X R^o,
    has_norm_differential NX (fun t:R^o=>`|t|) U f x L /\L (@coordinate_basis R 3 j)=0) ->
  @is_functional_analytic_submanifold R 3 2 U [set x|U x /\x j=f x].
Proof.
move=>X NX hNX hU hF hVertical.
pose hN:=@scalar_absolute_value_norm R.
pose p:=@euclidean_scalar_coordinate_map R 3 j.
have hP:=@euclidean_scalar_coordinate_bounded R 3 j.
have hOpen x (hx:U x):norm_domain_interior NX U x.
  apply:(@norm_domain_interior_neighbourhood R X NX hNX U x).2.
  have h:=hU;rewrite openE in h;exact:h x hx.
have hCoordinate:=@norm_bounded_linear_analytic R X R^o NX (fun t=>`|t|)
  hNX hN U hOpen p hP.
have hDifference:=norm_analytic_subtract hCoordinate hF.
have hOne:=@norm_constant_analytic R X R^o NX (fun t=>`|t|) hNX hN U hOpen 1.
split;first done.
split;first exact:hU.
exists (fun _:'I_(3-2)=>fun x:X=>x j-f x),(fun _=>1);split.
- by move=>i;exact:hDifference.
split;first exact:hOne.
split.
- move=>x;split.
  + move=>[hx hEquation];split;first exact:hx.
    split;first by move=>i;rewrite hEquation subrr.
    by move/eqP;rewrite oner_eq0.
  + move=>[hx [hEquation _]];split;first exact:hx.
    apply/eqP;rewrite -subr_eq0;apply/eqP;exact:hEquation ord0.
- move=>x [hx hEquation].
  have [L [hL hZero]]:=hVertical x hx.
  have hCoordD:=@norm_differential_linear R X R^o NX (fun t=>`|t|)
    hNX hN U x p (hOpen x hx) hP.
  have hD:=norm_differential_subtract hNX hN hCoordD hL.
  pose D:=fun _:'I_(3-2)=>p-L.
  exists D;split;first by move=>i;exact:hD.
  have hEval:(p-L) (@coordinate_basis R 3 j)= 1.
    change ((@coordinate_basis R 3 j) j-L (@coordinate_basis R 3 j)= 1).
    by rewrite hZero /coordinate_basis ffunE eqxx subr0.
  move=>c hSum i.
  have hAt:=congr1 (fun M:Hom X R^o=>M (@coordinate_basis R 3 j)) hSum.
  rewrite big_ord1 hom_scaleE hom_zeroE hEval in hAt.
  change (c ord0*1=0) in hAt.
  have hI:i=ord0:=ord1 i.
  by rewrite hI mulr1 in hAt *.
Qed.
