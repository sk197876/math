(** Federer (1969), 3.2.22(1), pp. 258–259:
    a nonzero intrinsic approximate Jacobian in actual
    chart coordinates gives the exact mu-dimensional image. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets.
From Federer Require Import Hom ModuleQuotient GrassmannAbbreviations EuclideanInnerProduct InnerNorm
  PartialFunctionUP PartialMetricLipschitz PartialLinearChartImage PartialExteriorNormUP
  PartialExteriorChartSandwich EuclideanLinearJacobian EuclideanLinearRangePlane GrassmannSubspaces
  TopMiddlePositiveJacobian.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [partial_exterior_positive_chart_image]:
    supporting image alternative in Federer 3.2.22(1),
    pp. 258–259. A nonzero actual intrinsic
    Jacobian makes the composite ordinary Jacobian positive.
    The target coordinate differential is onto, and its
    chart factor is injective, so the actual partial
    differential image is an exact mu-dimensional vector
    subspace. No off-tangent values are used. *)
Lemma partial_exterior_positive_chart_image (R:realType) m n k mu
    (Ds:Hom (R_n R m) (R_n R n)) (H:Hom (R_n R m) (R_n R k))
    (L:Hom (R_n R m) (R_n R mu)) (Dt:Hom (R_n R mu) (R_n R k))
    (d:partial_function (R_n R n) (R_n R k)) (lambda J:R):
  injective Ds ->0<lambda ->
  (forall v w,partial_function_graph d v w <->exists x,Ds x=v /\ H x=w) ->
  (forall x,lambda^-1*inner_norm (@euclidean_inner_productP R m) x<=
    inner_norm (@euclidean_inner_productP R n) (Ds x)) ->
  (forall x,inner_norm (@euclidean_inner_productP R n) (Ds x)<=
    lambda*inner_norm (@euclidean_inner_productP R m) x) ->
  H=hom_comp Dt L ->is_partial_exterior_norm mu d J ->J!=0 ->
  partial_function_range d=range Dt /\
    exists P:GrassmannSubspaces.G (R_n R k) mu,range Dt=[set w|grassmann_val P w].
Proof.
move=>hDs hLambda hGraph hLower hUpper hFactor hNorm hNonzero.
have hJPos:0<J.
  have [hp|hp]:=ltP 0 J; first by [].
  have hZero:J=0 by apply/eqP; rewrite eq_le hp (partial_exterior_norm_nonnegative hNorm).
  by rewrite hZero eqxx in hNonzero.
have hPower:0<lambda^+mu:=exprn_gt0 mu hLambda.
have hInv:0<(lambda^+mu)^-1 by rewrite invr_gt0.
have hSandwich:=@partial_exterior_chart_jacobian_sandwich R m n k mu Ds H d lambda J
  hDs hLambda hGraph hLower hUpper hNorm.
have hHPos:0<euclidean_linear_jacobian mu H:=lt_le_trans (mulr_gt0 hInv hJPos) hSandwich.1.
rewrite hFactor in hHPos.
have [hOnto [hInjective hImage]]:=@top_middle_positive_jacobian_image R m mu k L Dt hHPos.
split.
- have hRange:=partial_linear_chart_image hGraph.
  change (partial_function_range d=range H) in hRange.
  by rewrite hRange hFactor hImage.
- exact:(euclidean_injective_range_plane hInjective).
Qed.
