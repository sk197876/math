(** Federer (1969), 4.1.12, p. 369: products
    of normal currents are normal, as needed for
    normal-times-flat closure. Reuse the actual
    integral representations, every original boundary
    case and compact Cartesian support from 4.1.8. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct EuclideanCartesianMap CurrentSpaces CurrentCartesianDomain
  CurrentCartesianProductSealed CurrentCartesianOriginalDensity CurrentCartesianBoundaryPositive
  CurrentCartesianBoundaryFirstZero CurrentCartesianBoundarySecondZero CurrentCartesianCompactCurrents
  CurrentBoundary CurrentDegreeTransport CurrentRepresentableDegreeTransport CurrentRepresentableLinear
  CurrentIntegrationCriterion NormalCurrentsUP NormalCurrentDegreeTransport.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section CurrentCartesianNormal.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables m n:nat.
Variables (A:set (R_n R m)) (B:set (R_n R n)).
Hypothesis hA:forall a,A a->norm_domain_interior (inner_norm (@euclidean_inner_productP R m)) A a.
Hypothesis hB:forall b,B b->norm_domain_interior (inner_norm (@euclidean_inner_productP R n)) B b.
Local Notation AB := (@euclidean_cartesian_set R m n A B).
Local Notation hAB := (@current_cartesian_domain_open R m n A B hA hB).
Local Notation CA d := (@current_space R h2 m A hA d).
Local Notation CB d := (@current_space R h2 n B hB d).
Local Notation P i j := (@CartesianCurrentProduct.value R h2 m n i j A B hA hB).
Local Notation bdA d := (@current_boundary R h2 m d A hA).
Local Notation bdB d := (@current_boundary R h2 n d B hB).
Local Notation bdC d := (@current_boundary R h2 (m+n) d AB hAB).
Local Notation Tr a b e := (@current_degree_transport R h2 (m+n) AB hAB a b e).
Local Notation repA d := (@is_integration_representable_current R h2 m d A hA).
Local Notation repB d := (@is_integration_representable_current R h2 n d B hB).
Local Notation repC d := (@is_integration_representable_current R h2 (m+n) d AB hAB).
Local Notation localA d := (@is_locally_normal_current R h2 m A hA d).
Local Notation localB d := (@is_locally_normal_current R h2 n B hB d).
Local Notation localC d := (@is_locally_normal_current R h2 (m+n) AB hAB d).

(** Source for [locally_normal_current_cartesian_product]:
    the original product of locally normal factors
    is locally normal. This supports the normal
    approximants in Federer 4.1.12, p. 369,
    using 4.1.8's original representation and all
    three positive-degree boundary cases on pp. 360–361. *)
Theorem locally_normal_current_cartesian_product i j (S:CA i) (T:CB j):
  localA i S->localB j T->localC (i+j) (P i j S T).
Proof.
case:i S=>[|i] S;case:j T=>[|j] T;move=>hS hT.
- split;last by [].
  exact:(@current_cartesian_original_representable R h2 m n 0%N 0%N A B hA hB S T hS.1 hT.1).
- pose e:=addnS 0%N j.
  apply:(@locally_normal_current_degree_transport R h2 (m+n) AB hAB (0+j.+1) (0+j).+1 e
    (P 0%N j.+1 S T)).2.
  split.
  + exact:(@represented_current_degree_transport R h2 (m+n) AB hAB (0+j.+1) (0+j).+1 e
      (P 0%N j.+1 S T)
      (@current_cartesian_original_representable R h2 m n 0%N j.+1 A B hA hB S T hS.1 hT.1)).
  + change (repC (0+j) (bdC (0+j) (Tr _ _ e (P 0%N j.+1 S T)))).
    rewrite (@current_cartesian_boundary_second_zero R h2 m n A B hA hB j S T).
    exact:(@current_cartesian_original_representable R h2 m n 0%N j A B hA hB S (bdB j T) hS.1 hT.2).
- pose e:=addSn i 0%N.
  apply:(@locally_normal_current_degree_transport R h2 (m+n) AB hAB (i.+1+0) (i+0).+1 e
    (P i.+1 0%N S T)).2.
  split.
  + exact:(@represented_current_degree_transport R h2 (m+n) AB hAB (i.+1+0) (i+0).+1 e
      (P i.+1 0%N S T)
      (@current_cartesian_original_representable R h2 m n i.+1 0%N A B hA hB S T hS.1 hT.1)).
  + change (repC (i+0) (bdC (i+0) (Tr _ _ e (P i.+1 0%N S T)))).
    rewrite (@current_cartesian_boundary_first_zero R h2 m n A B hA hB i S T).
    exact:(@current_cartesian_original_representable R h2 m n i 0%N A B hA hB (bdA i S) T hS.2 hT.1).
- pose e:=addSn i j.+1.
  apply:(@locally_normal_current_degree_transport R h2 (m+n) AB hAB (i.+1+j.+1) (i+j.+1).+1 e
    (P i.+1 j.+1 S T)).2.
  split.
  + exact:(@represented_current_degree_transport R h2 (m+n) AB hAB (i.+1+j.+1) (i+j.+1).+1 e
      (P i.+1 j.+1 S T)
      (@current_cartesian_original_representable R h2 m n i.+1 j.+1 A B hA hB S T hS.1 hT.1)).
  + change (repC (i+j.+1) (bdC (i+j.+1) (Tr _ _ e (P i.+1 j.+1 S T)))).
    rewrite (@current_cartesian_boundary_positive R h2 m n A B hA hB i j S T) addrC.
    apply:(@represented_current_linear R h2 (m+n) (i+j.+1) AB hAB ((-1:R)^+i.+1) _ _).
    * apply:(@represented_current_degree_transport R h2 (m+n) AB hAB (i.+1+j) (i+j.+1)
        (eq_trans (addSn i j) (esym (addnS i j))) (P i.+1 j S (bdB j T))).
      exact:(@current_cartesian_original_representable R h2 m n i.+1 j A B hA hB S (bdB j T) hS.1 hT.2).
    * exact:(@current_cartesian_original_representable R h2 m n i j.+1 A B hA hB (bdA i S) T hS.2 hT.1).
Qed.

(** Source for [normal_current_cartesian_product]:
    normal factors give an original normal product,
    supporting the closure conclusion of Federer
    4.1.12, p. 369. Its compact support follows
    from the exact preceding product support theorem. *)
Theorem normal_current_cartesian_product i j (S:CA i) (T:CB j):
  @is_normal_current R h2 m A hA i S->@is_normal_current R h2 n B hB j T->
    @is_normal_current R h2 (m+n) AB hAB (i+j) (P i j S T).
Proof.
move=>hS hT;split.
- exact:(@locally_normal_current_cartesian_product i j S T hS.1 hT.1).
- exact:(@current_cartesian_compact_currents R h2 m n i j A B hA hB S T hS.2 hT.2).
Qed.
End CurrentCartesianNormal.
