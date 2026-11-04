(** Federer (1969), 3.2.46, p. 282: changing
    both source and target Riemannian metrics changes
    exterior Jacobians by controlled factors. These
    supporting inequalities use 1.7.6, pp. 33–34,
    and the public unit-ball and homogeneous norm laws. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom InnerProductUP InnerNorm LinearBasis
  OperatorNormUP ExteriorGrading ExteriorMaps ExteriorNorm InnerExteriorPositivity
  ExteriorMetricComparison.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [exterior_operator_source_metric_comparison]:
    the contravariant source-norm comparison for the
    Jacobians of 3.2.46, p. 282. A bound
    |v|_{B'}<=lambda|v|_B gives J_{B,C}<=lambda^k J_{B',C}.
    Every degree, singular map and zero exterior space remains. *)
Lemma exterior_operator_source_metric_comparison (R : realType) (h2 : (1+1 : R)!=0)
    (X Y : lmodType R) (B B' : X -> X -> R) (C : Y -> Y -> R)
    (hB : is_inner_product B) (hB' : is_inner_product B') (hC : is_inner_product C)
    n (e : 'I_n -> X) (he : is_basis e) (F : {linear X -> Y})
    (lambda : R) k jB jB' :
  0<=lambda -> (forall v, inner_norm hB' v<=lambda*inner_norm hB v) ->
  is_operator_norm (exterior_inner_productP h2 hB k) (exterior_inner_productP h2 hC k)
    (exterior_power_map F k) jB ->
  is_operator_norm (exterior_inner_productP h2 hB' k) (exterior_inner_productP h2 hC k)
    (exterior_power_map F k) jB' -> jB<=lambda^+k*jB'.
Proof.
move=> hLambda hBound hJB hJB'.
have [xi [hXi <-]] := operator_norm_attained hJB.
have hSource := @inner_exterior_norm_comparison R h2 X B B' hB hB' n e he lambda k xi hLambda hBound.
have hUnit : exterior_norm h2 hB' xi<=lambda^+k.
  apply: le_trans hSource _.
  have hScale := ler_wpM2l (exprn_ge0 k hLambda) hXi.
  by rewrite mulr1 in hScale.
have hOperator := operator_norm_vector_bound hJB' xi.
apply: le_trans hOperator _.
have hProduct := ler_wpM2l (operator_norm_nonnegative hJB') hUnit.
by rewrite [jB'*lambda^+k]mulrC in hProduct.
Qed.

(** Source for [exterior_operator_two_metric_comparison]:
    combined source and target norm changes in 3.2.46,
    p. 282. Independent vector bounds give the actual
    exterior operator norm estimate without rank or
    differential-field hypotheses. *)
Lemma exterior_operator_two_metric_comparison (R : realType) (h2 : (1+1 : R)!=0)
    (X Y : lmodType R) (B B' : X -> X -> R) (C C' : Y -> Y -> R)
    (hB : is_inner_product B) (hB' : is_inner_product B')
    (hC : is_inner_product C) (hC' : is_inner_product C')
    m (e : 'I_m -> X) (he : is_basis e) n (a : 'I_n -> Y) (ha : is_basis a)
    (F : {linear X -> Y}) (lambda delta : R) k j j' :
  0<=lambda -> 0<=delta ->
  (forall v, inner_norm hB' v<=lambda*inner_norm hB v) ->
  (forall v, inner_norm hC v<=delta*inner_norm hC' v) ->
  is_operator_norm (exterior_inner_productP h2 hB k) (exterior_inner_productP h2 hC k)
    (exterior_power_map F k) j ->
  is_operator_norm (exterior_inner_productP h2 hB' k) (exterior_inner_productP h2 hC' k)
    (exterior_power_map F k) j' -> j<=delta^+k*(lambda^+k*j').
Proof.
move=> hLambda hDelta hSourceBound hTargetBound hJ hJ'.
have [xi [hXi <-]] := operator_norm_attained hJ.
have hSource := @inner_exterior_norm_comparison R h2 X B B' hB hB' m e he lambda k xi
  hLambda hSourceBound.
have hUnit : exterior_norm h2 hB' xi<=lambda^+k.
  apply: le_trans hSource _.
  have hScale := ler_wpM2l (exprn_ge0 k hLambda) hXi.
  by rewrite mulr1 in hScale.
have hTarget := @inner_exterior_norm_comparison R h2 Y C' C hC' hC n a ha delta k
  (exterior_power_map F k xi) hDelta hTargetBound.
have hOperator := operator_norm_vector_bound hJ' xi.
have hNormalized : exterior_norm h2 hC' (exterior_power_map F k xi)<=lambda^+k*j'.
  apply: le_trans hOperator _.
  have hProduct := ler_wpM2l (operator_norm_nonnegative hJ') hUnit.
  by rewrite [j'*lambda^+k]mulrC in hProduct.
apply: le_trans hTarget _.
exact (ler_wpM2l (exprn_ge0 k hDelta) hNormalized).
Qed.
