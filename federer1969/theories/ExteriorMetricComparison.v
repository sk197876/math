(** Federer (1969), 3.2.46, p. 282: computing
    Jacobians in varying inner products uses the local
    metric comparison on exterior powers. These supporting
    inequalities follow from the proved 1.7.6 bounds and
    the public operator-norm laws, in every natural degree. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom TensorUP InnerProductUP InnerNorm LinearBasis
  OperatorNormUP OperatorNorm OperatorNormLaws ExteriorGrading ExteriorMaps
  ExteriorMapScaling ExteriorNorm ExteriorOperatorEstimate InnerExteriorPositivity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [inner_exterior_norm_comparison]: a bound
    |v|_C<=lambda|v|_B gives the actual kth exterior bound
    |xi|_C<=lambda^k|xi|_B, supporting 3.2.46, p. 282,
    by the displayed estimate of 1.7.6, p. 34.
    Zero degree and singular exterior spaces are retained. *)
Lemma inner_exterior_norm_comparison (R : realType) (h2 : (1+1 : R)!=0)
    (V : lmodType R) (B C : V -> V -> R)
    (hB : is_inner_product B) (hC : is_inner_product C)
    n (e : 'I_n -> V) (he : is_basis e) (lambda : R) k
    (xi : exterior_power V k) :
  0<=lambda -> (forall v, inner_norm hC v<=lambda*inner_norm hB v) ->
  exterior_norm h2 hC xi<=lambda^+k*exterior_norm h2 hB xi.
Proof.
move=> hLambda hBound.
pose idV := linear_id V.
pose c := linear_operator_norm hB hC he idV.
have hCNorm := linear_operator_normP hB hC he idV.
have hc0 : 0<=c := operator_norm_nonnegative hCNorm.
have hc : c<=lambda.
  apply: (@operator_norm_le_unit R V V B C hB hC idV c hCNorm lambda).2=> v hv.
  apply: le_trans (hBound v) _.
  have h := ler_wpM2l hLambda hv.
  by rewrite mulr1 in h.
have hExterior := @exterior_operator_pointwise_bound R h2 V V B C hB hC n e he
  idV c hCNorm k xi.
rewrite /idV exterior_power_map_identity in hExterior.
apply: le_trans hExterior _.
exact (ler_wpM2r (exterior_norm_nonnegative h2 hB xi)
  (lerXn2r k hc0 hLambda hc)).
Qed.

(** Source for [exterior_operator_target_metric_comparison]:
    the actual exterior operator norms, hence the Jacobians,
    obey the same lambda^k target-metric comparison, supporting
    3.2.46, p. 282. No rank, positive Jacobian or selected
    derivative is assumed; the original linear map is retained. *)
Lemma exterior_operator_target_metric_comparison (R : realType) (h2 : (1+1 : R)!=0)
    (X Y : lmodType R) (A : X -> X -> R) (B C : Y -> Y -> R)
    (hA : is_inner_product A) (hB : is_inner_product B) (hC : is_inner_product C)
    n (e : 'I_n -> Y) (he : is_basis e) (F : {linear X -> Y})
    (lambda : R) k jB jC :
  0<=lambda -> (forall v, inner_norm hC v<=lambda*inner_norm hB v) ->
  is_operator_norm (exterior_inner_productP h2 hA k) (exterior_inner_productP h2 hB k)
    (exterior_power_map F k) jB ->
  is_operator_norm (exterior_inner_productP h2 hA k) (exterior_inner_productP h2 hC k)
    (exterior_power_map F k) jC -> jC<=lambda^+k*jB.
Proof.
move=> hLambda hBound hJB hJC.
have [xi [hXi <-]] := operator_norm_attained hJC.
have hUpper := @inner_exterior_norm_comparison R h2 Y B C hB hC n e he lambda k
  (exterior_power_map F k xi) hLambda hBound.
apply: le_trans hUpper _.
exact (ler_wpM2l (exprn_ge0 k hLambda) (operator_norm_unit_bound hJB hXi)).
Qed.
