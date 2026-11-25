(** Federer (1969), 3.2.22, p. 259: combine
    the source partial-Jacobian comparison and the exact
    target-chart product into the printed local bounds. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerNorm
  EuclideanLinearJacobian LinearJacobianSandwich TopMiddleJacobianComposition
  PartialFunctionUP PartialExteriorNormUP PartialExteriorChartSandwich PositiveFactorSandwich.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [coarea_target_chart_jacobian_bounds]:
    lambda^(-mu) J_mu(F composed psi_i) <= J_mu phi_ij
    <=lambda^mu J_mu(F composed psi_i), Federer 3.2.22,
    p. 259. The exact middle-top product and
    the target-chart vector bounds prove both inequalities,
    including zero degree and deficient rank. *)
Lemma coarea_target_chart_jacobian_bounds (R:realType) m mu n
    (L:Hom (R_n R m) (R_n R mu)) (D:Hom (R_n R mu) (R_n R n)) (lambda:R):
  0<lambda ->
  (forall v,lambda^-1*inner_norm (@euclidean_inner_productP R mu) v<=
    inner_norm (@euclidean_inner_productP R n) (D v)) ->
  (forall v,inner_norm (@euclidean_inner_productP R n) (D v)<=
    lambda*inner_norm (@euclidean_inner_productP R mu) v) ->
  (lambda^+mu)^-1*euclidean_linear_jacobian mu (hom_comp D L)<=euclidean_linear_jacobian mu L /\
    euclidean_linear_jacobian mu L<=lambda^+mu*euclidean_linear_jacobian mu (hom_comp D L).
Proof.
move=>hLambda hLower hUpper.
have hInv:0<=lambda^-1 by rewrite invr_ge0; exact:ltW hLambda.
have [hDLower hDUpper]:=euclidean_top_jacobian_sandwich hInv (ltW hLambda) hLower hUpper.
rewrite exprVn in hDLower.
have hPositive:0<lambda^+mu:=exprn_gt0 mu hLambda.
exact:(positive_factor_sandwich hPositive (euclidean_linear_jacobian_nonnegative mu L)
  hDLower hDUpper (@euclidean_top_middle_jacobian_compose R m mu n L D)).
Qed.

(** Source for [rectifiable_coarea_pair_jacobian_bounds]:
    the two consecutive exterior inequalities in Federer
    3.2.22, p. 259, give lambda^(-2mu) ap J_mu f
    <=J_mu phi_ij<=lambda^(2mu) ap J_mu f. The
    actual partial source graph, source chart bounds and
    target chart factorization discharge every norm premise. *)
Theorem rectifiable_coarea_pair_jacobian_bounds (R:realType) m n k mu
    (Ds:Hom (R_n R m) (R_n R n)) (H:Hom (R_n R m) (R_n R k))
    (L:Hom (R_n R m) (R_n R mu)) (Dt:Hom (R_n R mu) (R_n R k))
    (d:partial_function (R_n R n) (R_n R k)) (lambda J:R):
  injective Ds ->0<lambda ->
  (forall v w,partial_function_graph d v w <->exists x,Ds x=v /\ H x=w) ->
  (forall x,lambda^-1*inner_norm (@euclidean_inner_productP R m) x<=
    inner_norm (@euclidean_inner_productP R n) (Ds x)) ->
  (forall x,inner_norm (@euclidean_inner_productP R n) (Ds x)<=
    lambda*inner_norm (@euclidean_inner_productP R m) x) ->
  (forall x,lambda^-1*inner_norm (@euclidean_inner_productP R mu) x<=
    inner_norm (@euclidean_inner_productP R k) (Dt x)) ->
  (forall x,inner_norm (@euclidean_inner_productP R k) (Dt x)<=
    lambda*inner_norm (@euclidean_inner_productP R mu) x) ->
  H=hom_comp Dt L ->is_partial_exterior_norm mu d J ->
  (lambda^+(mu+mu))^-1*J<=euclidean_linear_jacobian mu L /\
    euclidean_linear_jacobian mu L<=lambda^+(mu+mu)*J.
Proof.
move=>hDs hLambda hGraph hSL hSU hTL hTU hFactor hNorm.
have hSource:=@partial_exterior_chart_jacobian_sandwich R m n k mu Ds H d lambda J
  hDs hLambda hGraph hSL hSU hNorm.
have hTarget:=@coarea_target_chart_jacobian_bounds R m mu k L Dt lambda hLambda hTL hTU.
rewrite -hFactor in hTarget.
have hPositive:0<lambda^+mu:=exprn_gt0 mu hLambda.
have hResult:=iterated_positive_factor_sandwich hPositive hSource.1 hSource.2 hTarget.1 hTarget.2.
by rewrite -exprD in hResult.
Qed.
