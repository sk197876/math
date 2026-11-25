(** Federer (1969), 3.2.22, p. 259: vanishing
    of the ordinary chart-composite mu-Jacobian forces
    the intrinsic partial approximate Jacobian to vanish. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerNorm
  PartialFunctionUP PartialExteriorNormUP PartialExteriorChartSandwich EuclideanLinearJacobian.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [partial_exterior_chart_jacobian_zero]:
    the zero-Jacobian alternative in Federer 3.2.22,
    p. 259. The source chart lower exterior
    bound has a strictly positive coefficient, so a
    zero ordinary composite Jacobian forces the actual
    nonnegative intrinsic Jacobian to be zero. No
    off-domain value or extra rank assumption is used. *)
Lemma partial_exterior_chart_jacobian_zero (R:realType) m n k q
    (Ds:Hom (R_n R m) (R_n R n)) (H:Hom (R_n R m) (R_n R k))
    (d:partial_function (R_n R n) (R_n R k)) (lambda J:R):
  injective Ds ->0<lambda ->
  (forall v w,partial_function_graph d v w <->exists x,Ds x=v /\ H x=w) ->
  (forall x,lambda^-1*inner_norm (@euclidean_inner_productP R m) x<=
    inner_norm (@euclidean_inner_productP R n) (Ds x)) ->
  (forall x,inner_norm (@euclidean_inner_productP R n) (Ds x)<=
    lambda*inner_norm (@euclidean_inner_productP R m) x) ->
  is_partial_exterior_norm q d J ->euclidean_linear_jacobian q H=0 ->J=0.
Proof.
move=>hDs hLambda hGraph hLower hUpper hNorm hZero.
have hSandwich:=@partial_exterior_chart_jacobian_sandwich R m n k q Ds H d lambda J
  hDs hLambda hGraph hLower hUpper hNorm.
have hPower:0<lambda^+q:=exprn_gt0 q hLambda.
have hPowerNe:lambda^+q!=0 by rewrite (gt_eqF hPower).
have hCancel:(lambda^+q)*((lambda^+q)^-1*J)=J.
  by rewrite mulrA (mulfV hPowerNe) mul1r.
have hScaled:=ler_wpM2l (ltW hPower) hSandwich.1.
rewrite hZero mulr0 hCancel in hScaled.
by apply/eqP; rewrite eq_le hScaled (partial_exterior_norm_nonnegative hNorm).
Qed.
