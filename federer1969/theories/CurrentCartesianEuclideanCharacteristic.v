(** Federer (1969), 4.1.8, p. 362: the
    original Euclidean characteristic currents multiply
    to the coordinate-oriented characteristic current of
    the Cartesian set. The proof reuses 2.6.4,
    p. 119, on the original separated tests. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets
  reals constructive_ereal topology.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct EuclideanBlockCoordinates EuclideanCartesianMap
  ExteriorGrading FiniteExteriorPowers AlternatingForms AlternatingPairing CurrentSpaces CurrentDegreeTransport
  CurrentCartesianDomain CurrentCartesianTestProductSealed CurrentCartesianProductUP
  CurrentCartesianProductSealed CurrentCartesianProductUnique CurrentCartesianEuclideanPairing
  OpenEuclideanCharacteristicCurrent EuclideanCartesianSubsetIntegral EuclideanLebesgueDimensions
  MeasureUP MeasureIntegralUP MeasureSubsetIntegral SummableRealFunctionUP MeasureIntegralUniqueness
  RealSubsetIntegralGraph LatticeL1ApproximationLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section CurrentCartesianEuclideanCharacteristic.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables m n:nat.
Variable A:set (R_n R m).
Variable B:set (R_n R n).
Hypothesis hA:forall a,A a->norm_domain_interior (inner_norm (@euclidean_inner_productP R m)) A a.
Hypothesis hB:forall b,B b->norm_domain_interior (inner_norm (@euclidean_inner_productP R n)) B b.
Variable E:set (R_n R m).
Variable F:set (R_n R n).
Hypothesis hE:measure_measurable (@euclidean_lebesgue_measure R m) E.
Hypothesis hF:measure_measurable (@euclidean_lebesgue_measure R n) F.
Hypothesis hEF:measure_measurable (@euclidean_lebesgue_measure R (m+n)) (@euclidean_cartesian_set R m n E F).
Local Notation AB := (@euclidean_cartesian_set R m n A B).
Local Notation hAB := (@current_cartesian_domain_open R m n A B hA hB).
Local Notation EF := (@euclidean_cartesian_set R m n E F).
Local Notation S := (@open_euclidean_characteristic_current R h2 m A hA E hE).
Local Notation T := (@open_euclidean_characteristic_current R h2 n B hB F hF).
Local Notation C := (@open_euclidean_characteristic_current R h2 (m+n) AB hAB EF hEF).
Local Notation Pure := (fun k l=>@CartesianTestProduct.value R h2 m n A B hA hB k l).
Local Notation topm := (e_lambda (@coordinate_basis R m) (ord_tuple m)).
Local Notation topn := (e_lambda (@coordinate_basis R n) (ord_tuple n)).
Local Notation topmn := (e_lambda (@coordinate_basis R (m+n)) (ord_tuple (m+n))).

(** Source for [current_cartesian_euclidean_characteristic_laws]: the
    original Cartesian characteristic current satisfies both
    complete separated-test equations, supporting the ordered
    box identity in Federer 4.1.8, p. 362.
    Every mixed degree and both zero dimensions remain
    included. No finite-mass condition on the sets is added. *)
Theorem current_cartesian_euclidean_characteristic_laws:
  @is_current_cartesian_product R h2 m n A B hA hB Pure m n S T C.
Proof.
split.
- move=>alpha beta.
  have hSI:=@open_euclidean_characteristic_current_action R h2 m A hA E hE alpha.
  have hTI:=@open_euclidean_characteristic_current_action R h2 n B hB F hF beta.
  have hProduct:=@euclidean_separated_subset_integral R m n E F
    (fun x=>pairing topm (@current_test_value R h2 m A hA m alpha x))
    (fun y=>pairing topn (@current_test_value R h2 n B hB n beta y))
    (@current_value R h2 m A hA m S alpha) (@current_value R h2 n B hB n T beta) hSI hTI.
  have hCI:=@open_euclidean_characteristic_current_action R h2 (m+n) AB hAB EF hEF (Pure m n alpha beta).
  have hFunction:(fun z=>pairing topmn (@current_test_value R h2 (m+n) AB hAB (m+n) (Pure m n alpha beta) z))=
      (fun z=>pairing topm (@current_test_value R h2 m A hA m alpha (euclidean_block_split z).1)*
        pairing topn (@current_test_value R h2 n B hB n beta (euclidean_block_split z).2)).
    apply:funext=>z;exact:current_cartesian_euclidean_test_pairing.
  rewrite hFunction in hCI.
  exact:EFin_inj (measure_integral_unique hCI hProduct).
- move=>k l e hkm alpha beta.
  pose phi:=@current_test_degree_transport R h2 (m+n) AB hAB (k+l) (m+n) e (Pure k l alpha beta).
  have hCI:=@open_euclidean_characteristic_current_action R h2 (m+n) AB hAB EF hEF phi.
  have hFunction:(fun z=>pairing topmn (@current_test_value R h2 (m+n) AB hAB (m+n) phi z))=
      (fun _:R_n R (m+n)=>0).
    apply:funext=>z;exact:(@current_cartesian_euclidean_test_off_diagonal R h2 m n A B hA hB k l e alpha beta z hkm).
  rewrite hFunction in hCI.
  have hZero:=@real_total_zero_integral R (R_n R (m+n))
    (@euclidean_lebesgue_measure R (m+n)) (euclidean_lebesgue_is_measure R (m+n)).
  have hSubset:=(@real_subset_integral_total R (R_n R (m+n))
    (@euclidean_lebesgue_measure R (m+n)) EF (fun _=>0) (fun _=>0) (0:R)%:E
    (fun _ _=>erefl) (fun _ _=>erefl)).2 hZero.
  exact:EFin_inj (measure_integral_unique hCI hSubset).
Qed.

(** Source for [current_cartesian_euclidean_characteristic]: the actual
    original product equals the coordinate-oriented characteristic
    current of E times F on the original
    open product, supporting Federer 4.1.8, p. 362.
    It follows from the independent complete mixed-degree
    uniqueness theorem, without an extra density hypothesis. *)
Theorem current_cartesian_euclidean_characteristic:
  @CartesianCurrentProduct.value R h2 m n m n A B hA hB S T=C.
Proof.
exact:(@current_cartesian_product_unique R h2 m n m n A B hA hB S T
  (@CartesianCurrentProduct.value R h2 m n m n A B hA hB S T) C
  (@CartesianCurrentProduct.laws R h2 m n m n A B hA hB S T)
  current_cartesian_euclidean_characteristic_laws).
Qed.
End CurrentCartesianEuclideanCharacteristic.
