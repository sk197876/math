(** Federer (1969), 4.1.7, pp. 355–356,
    used in 4.1.12, p. 369:
    evaluation at a point is linear
    in the actual test form. Reuse
    the original pointwise test-space laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct AlternatingForms CurrentSpaces CurrentTestValueLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section CurrentTestPointValues.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Variable U:set (R_n R n).
Hypothesis hU:forall x,U x->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.
Local Notation DT := (@current_test_space R h2 n U hU m).
Local Notation Y := (A_m (R_n R n) R^o m).

(** Source for [current_test_point_value_map]: the
    original linear test evaluation at x,
    supporting the finite sums in Federer
    4.1.12, p. 369. This
    is a map of the existing spaces. *)
Definition current_test_point_value_map (x:R_n R n):Hom DT Y.
Proof.
apply:(@HomMap R DT Y (fun phi=>@current_test_value R h2 n U hU m phi x)).
apply/asboolP=>c phi psi.
by rewrite current_test_add_value current_test_scale_value.
Defined.

(** Source for [current_test_finite_sum_value]: the
    value of a finite original test
    sum is its finite sum of
    covector values, supporting Federer 4.1.12,
    p. 369. *)
Lemma current_test_finite_sum_value (I:finType) (f:I->DT) x:
  @current_test_value R h2 n U hU m (\sum_i f i) x=
    \sum_i @current_test_value R h2 n U hU m (f i) x.
Proof.
change (current_test_point_value_map x (\sum_i f i)=\sum_i current_test_point_value_map x (f i)).
exact:linear_sum.
Qed.
End CurrentTestPointValues.
