(** Federer (1969), 4.1.8, pp. 360–361:
    the original product density has exactly the original
    diagonal and off-diagonal separated-test pairings on
    the actual product domain. No representation hypothesis
    is needed for these pointwise identities. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct EuclideanBlockCoordinates EuclideanBlockLinearMaps
  EuclideanCartesianMap ExteriorGrading AlternatingForms AlternatingPairing
  CurrentDomain CurrentSpaces CurrentDegreeTransport CurrentCartesianDomain
  CurrentCartesianDomainMapsSealed CurrentCartesianDomainMapsLaws
  CurrentCartesianDensityMeasurable CurrentCartesianVectorPairing CurrentCartesianVectorOffDiagonal
  CurrentCartesianTestProductSealed MultivectorDualSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentCartesianDensityTestPairing.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables m n i j:nat.
Local Notation X := (R_n R m).
Local Notation Y := (R_n R n).
Local Notation Z := (R_n R (m+n)).
Variables (A:set X) (B:set Y).
Hypothesis hA:forall a,A a->norm_domain_interior (inner_norm (@euclidean_inner_productP R m)) A a.
Hypothesis hB:forall b,B b->norm_domain_interior (inner_norm (@euclidean_inner_productP R n)) B b.
Local Notation AB := (@euclidean_cartesian_set R m n A B).
Local Notation hAB := (@current_cartesian_domain_open R m n A B hA hB).
Local Notation AT := (current_domain R m A).
Local Notation BT := (current_domain R n B).
Local Notation CT := (current_domain R (m+n) AB).
Local Notation J := (@CartesianCurrentDomain.join R m n A B).
Local Notation p := (@euclidean_first_block_map R m n).
Local Notation q := (@euclidean_last_block_map R m n).
Local Notation Pure := (fun k l=>@CartesianTestProduct.value R h2 m n A B hA hB k l).
Local Notation va := (fun k=>@current_test_value R h2 m A hA k).
Local Notation vb := (fun k=>@current_test_value R h2 n B hB k).
Local Notation vc := (fun k=>@current_test_value R h2 (m+n) AB hAB k).
Variables (xi:AT->exterior_power X i) (eta:BT->exterior_power Y j).
Local Notation zeta := (@current_cartesian_density R m n i j A B xi eta).

(** Source for [current_cartesian_density_test_pairing]:
    the original diagonal density pairing factors into
    the two actual factor-test pairings, supporting Federer
    4.1.8, pp. 360–361. *)
Theorem current_cartesian_density_test_pairing alpha beta (z:AT*BT):
  @MultivectorDual.evaluation R Z (i+j) (zeta (J z))
    (vc (i+j) (Pure i j alpha beta) (set_val (J z)))=
    (@MultivectorDual.evaluation R X i (xi z.1) (va i alpha (set_val z.1)))*
    (@MultivectorDual.evaluation R Y j (eta z.2) (vb j beta (set_val z.2))).
Proof.
have hP:p (set_val (J z))=set_val z.1.
  rewrite current_cartesian_domain_join_value.
  exact:(congr1 fst (@euclidean_block_joinK R m n (set_val z.1,set_val z.2))).
have hQ:q (set_val (J z))=set_val z.2.
  rewrite current_cartesian_domain_join_value.
  exact:(congr1 snd (@euclidean_block_joinK R m n (set_val z.1,set_val z.2))).
rewrite !MultivectorDual.laws current_cartesian_density_join
  ((@CartesianTestProduct.laws R h2 m n A B hA hB i j).2
    alpha beta (set_val (J z)) (set_valP (J z))) hP hQ.
exact:current_cartesian_vector_pairing.
Qed.

(** Source for [current_cartesian_density_test_off_diagonal]:
    the original density pairing vanishes for every valid
    original off-diagonal separated test, supporting Federer
    4.1.8, pp. 360–361. *)
Theorem current_cartesian_density_test_off_diagonal k l (e:(k+l)%N=(i+j)%N)
    alpha beta (z:AT*BT):k<>i ->
  @MultivectorDual.evaluation R Z (i+j) (zeta (J z))
    (vc (i+j) (@current_test_degree_transport R h2 (m+n) AB hAB (k+l) (i+j) e
      (Pure k l alpha beta)) (set_val (J z)))=0.
Proof.
move=>hki.
have hP:p (set_val (J z))=set_val z.1.
  rewrite current_cartesian_domain_join_value.
  exact:(congr1 fst (@euclidean_block_joinK R m n (set_val z.1,set_val z.2))).
have hQ:q (set_val (J z))=set_val z.2.
  rewrite current_cartesian_domain_join_value.
  exact:(congr1 snd (@euclidean_block_joinK R m n (set_val z.1,set_val z.2))).
rewrite MultivectorDual.laws current_cartesian_density_join current_test_degree_transport_values
  ((@CartesianTestProduct.laws R h2 m n A B hA hB k l).2
    alpha beta (set_val (J z)) (set_valP (J z))) hP hQ.
exact:current_cartesian_vector_off_diagonal hki.
Qed.
End CurrentCartesianDensityTestPairing.
