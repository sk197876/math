(** Federer (1969), 3.2.22, p. 259: the
    lambda^mu comparison between the intrinsic approximate
    Jacobian and its actual source-chart composite Jacobian. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerNorm
  EuclideanLinearJacobian PartialFunctionUP PartialExteriorNormUP PartialExteriorNormLaws
  PartialExteriorChartCoordinates EuclideanExteriorComposition.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [partial_exterior_chart_jacobian_sandwich]:
    lambda^(-mu) ap J_mu f <= J_mu(F composed with psi)
    <= lambda^mu ap J_mu f in Federer 3.2.22,
    p. 259. The exact partial chart graph and the
    two vector bounds on Dpsi imply both inequalities.
    This supports every exterior degree, including degree zero;
    no agreement beyond the actual partial domain is assumed. *)
Theorem partial_exterior_chart_jacobian_sandwich (R:realType) m n k q
    (D:Hom (R_n R m) (R_n R n)) (H:Hom (R_n R m) (R_n R k))
    (d:partial_function (R_n R n) (R_n R k)) (lambda J:R):
  injective D ->0<lambda ->
  (forall v w,partial_function_graph d v w <->exists x,D x=v /\ H x=w) ->
  (forall x,lambda^-1*inner_norm (@euclidean_inner_productP R m) x<=
    inner_norm (@euclidean_inner_productP R n) (D x)) ->
  (forall x,inner_norm (@euclidean_inner_productP R n) (D x)<=
    lambda*inner_norm (@euclidean_inner_productP R m) x) ->
  is_partial_exterior_norm q d J ->
  (lambda^+q)^-1*J<=euclidean_linear_jacobian q H /\
  euclidean_linear_jacobian q H<=lambda^+q*J.
Proof.
move=>hD hLambda hGraph hLower hUpper hJ.
have [L [K [Ki [hL [hLK [hNorm [hLeft hRight]]]]]]]:=
  @partial_exterior_chart_coordinates_exists R m n k q D H d hD hGraph.
have hJL:J=euclidean_linear_jacobian q L:=partial_exterior_norm_unique hJ hL.
have hKBound x:inner_norm (@euclidean_inner_productP R m) (K x)<=
    lambda*inner_norm (@euclidean_inner_productP R m) x.
  by rewrite hNorm; exact:hUpper.
have hKiBound x:inner_norm (@euclidean_inner_productP R m) (Ki x)<=
    lambda*inner_norm (@euclidean_inner_productP R m) x.
  have h:=ler_wpM2l (ltW hLambda) (hLower (Ki x)).
  by rewrite -(hNorm (Ki x)) hRight mulrA mulfV ?gt_eqF ?mul1r in h.
have hKJ:=euclidean_exterior_jacobian_vector_bound_power q (ltW hLambda) hKBound.
have hKiJ:=euclidean_exterior_jacobian_vector_bound_power q (ltW hLambda) hKiBound.
have hH:hom_comp L K=H by apply:hom_ext=>x; exact:hLK.
have hLId:hom_comp H Ki=L.
  apply:hom_ext=>x; change (H (Ki x)=L x).
  by rewrite -(hLK (Ki x)) hRight.
have hAbove:euclidean_linear_jacobian q H<=lambda^+q*J.
  rewrite -hH hJL mulrC; apply:(le_trans (@euclidean_exterior_jacobian_compose_bound R m m k q K L) _).
  exact:(ler_wpM2l (euclidean_linear_jacobian_nonnegative q L) hKJ).
have hBelow:J<=euclidean_linear_jacobian q H*lambda^+q.
  rewrite hJL -hLId; apply:(le_trans (@euclidean_exterior_jacobian_compose_bound R m m k q Ki H) _).
  exact:(ler_wpM2l (euclidean_linear_jacobian_nonnegative q H) hKiJ).
split; last exact hAbove.
have hPower:0<lambda^+q:=exprn_gt0 q hLambda.
have hInvPower:0<(lambda^+q)^-1 by rewrite invr_gt0.
have hScaled:=ler_wpM2l (ltW hInvPower) hBelow.
by rewrite mulrCA mulVf ?gt_eqF ?mulr1 in hScaled.
Qed.
