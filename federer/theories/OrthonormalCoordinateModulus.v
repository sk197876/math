(** Federer (1969), 3.2.27, p. 263: replace the
    orthonormal coordinates of T by their absolute values.
    The resulting vector has the same norm. State its
    coordinate laws first; the finite sum proves existence. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals topology.
From Federer Require Import InnerProductUP InnerNorm InnerNormInequalities InnerMetric
  InnerNormedTopology HilbertFormCompactness InnerNormalization OrthonormalFamilies OrthonormalParseval OrthonormalBilinearCoordinates
  LinearBasis FiniteDualDimension RealNormUP NormMetricContinuity NormMetricScaleContinuity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [is_orthonormal_coordinate_modulus]: the
    defining coordinate equation for Xi in 3.2.27,
    p. 263, using an arbitrary finite orthonormal basis.
    These laws are independent of the existence proof. *)
Definition is_orthonormal_coordinate_modulus (R:realType) (V:lmodType R)
    (B:V->V->R) (I:finType) (e:I->V) (A:V->V):Prop:=
  forall x i,B (A x) (e i)=`|B x (e i)|.

(** Source for [orthonormal_coordinate_modulus_exists]: the
    choice of Xi's nonnegative coordinates in 3.2.27,
    p. 263. Basis synthesis establishes existence without
    introducing a global selected map or project axiom. *)
Theorem orthonormal_coordinate_modulus_exists (R:realType) (V:lmodType R)
    (B:V->V->R) (hB:is_inner_product B) (I:finType) (e:I->V):
  orthonormal_family B e ->exists A:V->V,is_orthonormal_coordinate_modulus B e A.
Proof.
move=>he; exists (fun x=>\sum_i `|B x (e i)|*:e i)=>x i.
have h:=@orthonormal_coefficient R V B hB I e he (fun j=>`|B x (e j)|) i.
by rewrite inner_coordinateE in h.
Qed.

(** Source for [orthonormal_coordinate_modulus_norm]: the
    equality |Xi(w)|=|T(w)| in 3.2.27, p. 263.
    Parseval and the equality of squared absolute values
    give the result, including zero-dimensional spaces. *)
Lemma orthonormal_coordinate_modulus_norm (R:realType) (V:lmodType R)
    (B:V->V->R) (hB:is_inner_product B) (I:finType) (e:I->V) (A:V->V):
  orthonormal_family B e ->is_basis e ->is_orthonormal_coordinate_modulus B e A ->
  forall x,inner_norm hB (A x)=inner_norm hB x.
Proof.
move=>he hb hA x.
apply:inner_norm_value; first exact:inner_norm_nonnegative.
rewrite inner_norm_sqr !(@orthonormal_parseval R V B hB I e he hb).
apply:eq_bigr=>i _; rewrite hA -normrX (ger0_norm (sqr_ge0 _)); reflexivity.
Qed.

(** Source for [orthonormal_coordinate_modulus_nonexpanding]:
    measurable coordinate replacement used in 3.2.27,
    p. 263. Absolute value is nonexpanding on each
    real coordinate; summing squares proves contraction
    of the full vector map in the original norm. *)
Lemma orthonormal_coordinate_modulus_nonexpanding (R:realType) (V:lmodType R)
    (B:V->V->R) (hB:is_inner_product B) (I:finType) (e:I->V) (A:V->V):
  orthonormal_family B e ->is_basis e ->is_orthonormal_coordinate_modulus B e A ->
  forall x y,inner_norm hB (A x-A y)<=inner_norm hB (x-y).
Proof.
move=>he hb hA x y.
rewrite -(ler_sqr (inner_norm_nonnegative hB _) (inner_norm_nonnegative hB _))
  !inner_norm_sqr !(@orthonormal_parseval R V B hB I e he hb).
apply:ler_sum=>i _.
rewrite -!inner_coordinateE !linearB !inner_coordinateE !hA.
pose a:R:=B x (e i).
pose b:R:=B y (e i).
pose c:R:=(`|a| - `|b|)%R.
have hBound:=@real_norm_change_bound R R^o (fun z:R=>`|z|)
  (scalar_absolute_value_norm R) a b.
have hSquare:`|c|^+2<=`|a-b|^+2.
  by rewrite (ler_sqr (normr_ge0 _) (normr_ge0 _)).
rewrite -!normrX (ger0_norm (sqr_ge0 c)) (ger0_norm (sqr_ge0 (a-b))) in hSquare.
exact hSquare.
Qed.

(** Source for [orthonormal_coordinate_modulus_continuous]:
    Borel regularity of Xi in the argument of 3.2.27,
    p. 263. The proved contraction supplies continuity
    using only the abstract coordinate laws. *)
Lemma orthonormal_coordinate_modulus_continuous (R:realType) (V:lmodType R)
    (B:V->V->R) (hB:is_inner_product B) (I:finType) (e:I->V) (A:V->V):
  orthonormal_family B e ->is_basis e ->is_orthonormal_coordinate_modulus B e A ->
  continuous (A:inner_metric_space hB->inner_metric_space hB).
Proof.
move=>he hb hA.
apply:(@metric_fixed_lipschitz_continuous R (inner_metric_space hB) (inner_metric_space hB)
  A 1 ler01)=>x y.
rewrite !inner_metric_distanceE mul1r.
exact:(orthonormal_coordinate_modulus_nonexpanding hB he hb hA x y).
Qed.

(** Source for [orthonormal_nonnegative_norm_sum]: the
    pointwise bound |Xi|<=sum Xi_lambda in 3.2.27,
    p. 263. Expand in the actual orthonormal basis
    and apply the finite triangle inequality; nonnegative
    coordinates remove their absolute values. *)
Lemma orthonormal_nonnegative_norm_sum (R:realType) (V:lmodType R)
    (B:V->V->R) (hB:is_inner_product B) (I:finType) (e:I->V) (x:V):
  orthonormal_family B e ->is_basis e ->(forall i,0<=B x (e i)) ->
  inner_norm hB x<=\sum_i B x (e i).
Proof.
move=>he hb hPositive.
have hExpand:x=\sum_i B x (e i)*:e i.
  rewrite {1}(@orthonormal_basis_vector_expansion R V I e hb x).
  apply:eq_bigr=>i _; by rewrite (@orthonormal_basis_inner_coordinate R V B hB I e he hb).
rewrite {1}hExpand.
apply:(le_trans (real_seminorm_sum (inner_norm_real_norm hB).1 _)).
apply:ler_sum=>i _.
rewrite inner_normZ (@InnerNormalization.orthonormal_norm1 R V B hB I e he i)
  mulr1 (ger0_norm (hPositive i)); exact:lexx.
Qed.
