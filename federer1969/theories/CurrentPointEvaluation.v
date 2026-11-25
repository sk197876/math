(** Federer (1969), 4.1.7, pp. 355–356: original
    evaluation at one actual test is linear in the
    current. The proof composes the existing Hom
    evaluation with the actual continuous-dual inclusion. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct CurrentSpaces.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section CurrentPointEvaluation.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Variable U:set (R_n R n).
Hypothesis hU:forall x,U x->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.
Local Notation C := (@current_space R h2 n U hU m).
Local Notation DT := (@current_test_space R h2 n U hU m).
Local Notation action := (@current_value R h2 n U hU m).

(** Source for [current_point_evaluation]: the original
    linear map T to T(psi), supporting Federer
    4.1.7, pp. 355–356. *)
Definition current_point_evaluation (psi:DT):Hom C R^o:=
  hom_comp (@HomMap R (Hom DT R^o) R^o (fun L=>L psi)
    (introT (asboolP _) (@hom_eval_linear R DT R^o psi))) action.

(** Source for [current_point_evaluation_values]: exact
    original test action, supporting Federer 4.1.7,
    pp. 355–356. *)
Lemma current_point_evaluation_values T psi:current_point_evaluation psi T=action T psi.
Proof. by rewrite /current_point_evaluation hom_compE. Qed.

(** Source for [current_value_finite_sum]: evaluation
    of an original finite current sum, supporting
    Federer 4.1.7, p. 356. *)
Lemma current_value_finite_sum (I:finType) (F:I->C) psi:
  action (\sum_i F i) psi=\sum_i action (F i) psi.
Proof.
change (current_point_evaluation psi (\sum_i F i)=\sum_i current_point_evaluation psi (F i)).
exact:linear_sum.
Qed.

(** Source for [current_value_negate]: evaluation of
    the original negative current, supporting
    Federer 4.1.7, p. 356. *)
Lemma current_value_negate T psi:action (-T) psi= -action T psi.
Proof.
change (current_point_evaluation psi (-T)= -current_point_evaluation psi T).
exact:linearN.
Qed.

(** Source for [current_value_scale]: evaluation of
    an original scalar current multiple, supporting
    Federer 4.1.7, p. 356. *)
Lemma current_value_scale c T psi:action (c*:T) psi=c*action T psi.
Proof.
change (current_point_evaluation psi (c*:T)=c*:current_point_evaluation psi T).
exact:linearZ.
Qed.
End CurrentPointEvaluation.
