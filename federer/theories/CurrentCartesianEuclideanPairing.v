(** Federer (1969), 4.1.8, p. 362: the original
    coordinate orientation evaluates separated tests as the
    product of the coordinate factor evaluations. The
    earlier grading law handles every other mixed degree. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct EuclideanBlockCoordinates
  EuclideanBlockLinearMaps EuclideanCartesianMap ExteriorGrading FiniteExteriorPowers
  AlternatingForms AlternatingPairing CurrentSpaces CurrentDegreeTransport CurrentCartesianDomain
  CurrentCartesianTestProductSealed CurrentCartesianTestProductEverywhere
  CurrentCartesianVectorProduct CurrentCartesianVectorPairing CurrentCartesianVectorOffDiagonal
  CurrentCartesianCoordinateOrientation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentCartesianEuclideanPairing.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables m n:nat.
Variable A:set (R_n R m).
Variable B:set (R_n R n).
Hypothesis hA:forall a,A a->norm_domain_interior (inner_norm (@euclidean_inner_productP R m)) A a.
Hypothesis hB:forall b,B b->norm_domain_interior (inner_norm (@euclidean_inner_productP R n)) B b.
Local Notation AB := (@euclidean_cartesian_set R m n A B).
Local Notation hAB := (@current_cartesian_domain_open R m n A B hA hB).
Local Notation Pure := (fun k l=>@CartesianTestProduct.value R h2 m n A B hA hB k l).
Local Notation topm := (e_lambda (@coordinate_basis R m) (ord_tuple m)).
Local Notation topn := (e_lambda (@coordinate_basis R n) (ord_tuple n)).
Local Notation topmn := (e_lambda (@coordinate_basis R (m+n)) (ord_tuple (m+n))).

(** Source for [current_cartesian_euclidean_test_pairing]: every
    original separated top-degree test evaluates on the
    coordinate orientation as the product of its factor
    evaluations, supporting Federer 4.1.8, p. 362.
    Globally normalized test values retain the assertion
    outside the original Cartesian domain. *)
Lemma current_cartesian_euclidean_test_pairing
    (alpha:@current_test_space R h2 m A hA m)
    (beta:@current_test_space R h2 n B hB n) z:
  pairing topmn (@current_test_value R h2 (m+n) AB hAB (m+n) (Pure m n alpha beta) z)=
    pairing topm (@current_test_value R h2 m A hA m alpha (euclidean_block_split z).1)*
    pairing topn (@current_test_value R h2 n B hB n beta (euclidean_block_split z).2).
Proof.
rewrite current_cartesian_test_product_values_all -current_cartesian_coordinate_orientation.
exact:current_cartesian_vector_pairing.
Qed.

(** Source for [current_cartesian_euclidean_test_off_diagonal]: every
    original separated test of another first degree
    has zero coordinate-oriented value, supporting the
    entire product characterization in Federer 4.1.8,
    pp. 360 and 362. Only equal total
    degrees are identified. *)
Lemma current_cartesian_euclidean_test_off_diagonal k l (e:(k+l)%N=(m+n)%N)
    (alpha:@current_test_space R h2 m A hA k)
    (beta:@current_test_space R h2 n B hB l) z:
  k<>m->
  pairing topmn (@current_test_value R h2 (m+n) AB hAB (m+n)
    (@current_test_degree_transport R h2 (m+n) AB hAB (k+l) (m+n) e (Pure k l alpha beta)) z)=0.
Proof.
move=>hkm.
rewrite current_test_degree_transport_values current_cartesian_test_product_values_all
  -current_cartesian_coordinate_orientation.
exact:(@current_cartesian_vector_off_diagonal R h2 m n m n k l e topm topn
  (@current_test_value R h2 m A hA k alpha (@euclidean_first_block_map R m n z))
  (@current_test_value R h2 n B hB l beta (@euclidean_last_block_map R m n z)) hkm).
Qed.
End CurrentCartesianEuclideanPairing.
