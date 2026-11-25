(** Federer (1969), 4.1.8, p. 360: the separated test is
    determined by its actual form values. This supporting uniqueness
    uses the earlier extensionality of genuine compact test functions;
    it assumes no density theorem for Cartesian current products. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct EuclideanCartesianMap
  CurrentSpaces SmoothTestEvaluation CurrentCartesianDomain CurrentCartesianTestProductUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentCartesianTestProductUnique.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables m n:nat.
Variable A:set (R_n R m).
Variable B:set (R_n R n).
Hypothesis hA:forall a,A a->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R m)) A a.
Hypothesis hB:forall b,B b->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) B b.
Local Notation AB := (@euclidean_cartesian_set R m n A B).
Local Notation hAB := (@current_cartesian_domain_open R m n A B hA hB).
Local Notation DA := (fun k=>@current_test_space R h2 m A hA k).
Local Notation DB := (fun k=>@current_test_space R h2 n B hB k).
Local Notation DC := (fun k=>@current_test_space R h2 (m+n) AB hAB k).

(** Source for [current_cartesian_test_product_unique]: the actual
    separated test p#alpha wedge q#beta in Federer 4.1.8, p. 360
    is fixed by its displayed pointwise form. This supporting result
    includes empty domains and every pair of nonnegative degrees. *)
Theorem current_cartesian_test_product_unique k l (F G:DA k->DB l->DC (k+l)):
  @is_current_cartesian_test_product R h2 m n A B hA hB k l F->
  @is_current_cartesian_test_product R h2 m n A B hA hB k l G->F=G.
Proof.
move=>[_ hF] [_ hG].
apply:funext=>alpha;apply:funext=>beta.
apply:(smooth_test_values_extensional
  (@current_smooth_space_laws R h2 (m+n) AB hAB (k+l)))=>z hz.
change (@current_test_value R h2 (m+n) AB hAB (k+l) (F alpha beta) z=
  @current_test_value R h2 (m+n) AB hAB (k+l) (G alpha beta) z).
exact:(eq_trans (@hF alpha beta z hz) (esym (@hG alpha beta z hz))).
Qed.
End CurrentCartesianTestProductUnique.
