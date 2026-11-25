(** Federer (1969), 4.1.9, p. 363: the point multivector
    current used to derive the differential-form homotopy identity.
    The action is specified independently on the actual test
    space; existence is proved separately. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct ExteriorGrading AlternatingForms AlternatingPairing
  CurrentSpaces CurrentEvaluation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section PointMultivectorCurrentUP.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n j:nat.
Local Notation X := (R_n R n).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.
Variable x:X.
Local Notation C := (@current_space R h2 n U hU j).
Local Notation DT := (@current_test_space R h2 n U hU j).
Local Notation value := (@current_test_value R h2 n U hU j).
Local Notation action := (@current_value R h2 n U hU j).

(** Source for [is_point_multivector_current]: the original
    current satisfies T(beta)=<eta,beta(x)>, Federer 4.1.9,
    p. 363. The multivector dependence is linear. No
    existence or homotopy formula is included in the law. *)
Definition is_point_multivector_current (P:Hom (exterior_power X j) C):Prop:=
  forall eta (beta:DT),action (P eta) beta=pairing eta (value beta x).

(** Source for [point_multivector_current_unique]: the original
    point action determines a unique linear current-valued map,
    supporting Federer 4.1.9, p. 363. *)
Theorem point_multivector_current_unique (P Q:Hom (exterior_power X j) C):
  is_point_multivector_current P->is_point_multivector_current Q->P=Q.
Proof.
move=>hP hQ;apply:hom_ext=>eta;apply:(@current_values_extensional R h2 n j U hU)=>beta.
exact:(eq_trans (hP eta beta) (esym (hQ eta beta))).
Qed.
End PointMultivectorCurrentUP.
