(** Federer (1969), 4.1.8, p. 360: the original
    first-variable slice test is determined by its displayed
    values. This supporting uniqueness uses the actual test
    space; it adds no integral representation premise. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  EuclideanCartesianMap ExteriorGrading CurrentSpaces SmoothTestEvaluation
  CurrentCartesianDomain CurrentCartesianSliceTestUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentCartesianSliceTestUnique.
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
Local Notation DC := (fun k=>@current_test_space R h2 (m+n) AB hAB k).

(** Source for [current_cartesian_slice_test_unique]: equal
    original slice values give equal actual tests, supporting
    the construction of phi_S in Federer 4.1.8, p. 360.
    Uniqueness includes independence of domain-membership proofs. *)
Theorem current_cartesian_slice_test_unique i j
    (G H:forall b:R_n R n,B b->exterior_power (R_n R n) j->DC (i+j)->DA i):
  @is_current_cartesian_slice_test R h2 m n A B hA hB i j G->
  @is_current_cartesian_slice_test R h2 m n A B hA hB i j H->G=H.
Proof.
move=>hG hH;apply:functional_extensionality_dep=>b;apply:funext=>hb;
  apply:funext=>eta;apply:funext=>phi.
apply:(smooth_test_values_extensional (@current_smooth_space_laws R h2 m A hA i))=>a ha.
change (@current_test_value R h2 m A hA i (G b hb eta phi) a=
  @current_test_value R h2 m A hA i (H b hb eta phi) a).
exact:(eq_trans ((hG b hb).2 eta phi a ha) (esym ((hH b hb).2 eta phi a ha))).
Qed.

(** Source for [current_cartesian_slice_test_membership_independent]:
    the test in the defining slice of Federer 4.1.8, p. 360,
    depends on the point b, independently of a proof that b
    belongs to B. Equality follows from the original pointwise
    formula and the extensionality of actual tests. *)
Theorem current_cartesian_slice_test_membership_independent i j
    (G:forall b:R_n R n,B b->exterior_power (R_n R n) j->DC (i+j)->DA i):
  @is_current_cartesian_slice_test R h2 m n A B hA hB i j G->
  forall b (u v:B b) eta phi,G b u eta phi=G b v eta phi.
Proof.
move=>hG b u v eta phi.
apply:(smooth_test_values_extensional (@current_smooth_space_laws R h2 m A hA i))=>a ha.
change (@current_test_value R h2 m A hA i (G b u eta phi) a=
  @current_test_value R h2 m A hA i (G b v eta phi) a).
exact:(eq_trans ((hG b u).2 eta phi a ha) (esym ((hG b v).2 eta phi a ha))).
Qed.
End CurrentCartesianSliceTestUnique.
