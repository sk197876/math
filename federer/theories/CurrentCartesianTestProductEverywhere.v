(** Federer (1969), 4.1.8, p. 362: the
    original separated-test formula also holds for
    globally normalized values outside the product
    domain. Zero extension in each factor proves
    the outside cases used in Lebesgue Fubini. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom TensorUP Bilinear RealNormUP NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  EuclideanBlockLinearMaps EuclideanCartesianMap AlternatingForms AlternatingDual
  AlternatingProduct ScalarCoefficients CurrentSpaces CurrentCartesianDomain CurrentCartesianTestProductUP CurrentCartesianTestProductSealed CurrentTestOutside.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section CurrentCartesianTestProductEverywhere.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables m n:nat.
Local Notation X := (R_n R m).
Local Notation Y := (R_n R n).
Local Notation Z := (R_n R (m+n)).
Variable A:set X.
Variable B:set Y.
Hypothesis hA:forall a,A a->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R m)) A a.
Hypothesis hB:forall b,B b->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) B b.
Local Notation AB := (@euclidean_cartesian_set R m n A B).
Local Notation hAB := (@current_cartesian_domain_open R m n A B hA hB).
Local Notation DA := (fun k=>@current_test_space R h2 m A hA k).
Local Notation DB := (fun k=>@current_test_space R h2 n B hB k).
Local Notation DC := (fun k=>@current_test_space R h2 (m+n) AB hAB k).
Local Notation va := (fun k=>@current_test_value R h2 m A hA k).
Local Notation vb := (fun k=>@current_test_value R h2 n B hB k).
Local Notation vc := (fun k=>@current_test_value R h2 (m+n) AB hAB k).
Local Notation p := (@euclidean_first_block_map R m n).
Local Notation q := (@euclidean_last_block_map R m n).

Local Notation Pure := (fun k l=>@CartesianTestProduct.value R h2 m n A B hA hB k l).

(** Source for [current_cartesian_test_product_values_all]: the
    original separated form has the printed block
    wedge values at every normalized point, supporting
    the Euclidean-current product in Federer 4.1.8,
    p. 362. Outside the Cartesian domain, at
    least one original factor value is zero. *)
Theorem current_cartesian_test_product_values_all k l (alpha:DA k) (beta:DB l) z:
  vc (k+l) (Pure k l alpha beta) z=
    form_wedge h2 (scalar_bilinear R)
      (A_m_dual (hom_as_linear p) (va k alpha (p z)))
      (A_m_dual (hom_as_linear q) (vb l beta (q z))).
Proof.
case:(pselect (AB z))=>hz.
- exact:((@CartesianTestProduct.laws R h2 m n A B hA hB k l).2 alpha beta z hz).
- rewrite (@current_test_value_outside R h2 (m+n) (k+l) AB hAB (Pure k l alpha beta) z hz).
  have hWedge:=@form_wedge_bilinear R h2 Z R^o (fun a b:R^o=>a*b) (@scalar_bilinear R) k l.
  case:(pselect (A (p z)))=>hAValue.
  + have hBValue:~B (q z).
      move=>h;apply:hz;exact:conj hAValue h.
    rewrite (@current_test_value_outside R h2 n l B hB beta (q z) hBValue) linear0.
    exact:esym (bil0r hWedge (A_m_dual (hom_as_linear p) (va k alpha (p z)))).
  + rewrite (@current_test_value_outside R h2 m k A hA alpha (p z) hAValue) linear0.
    exact:esym (bil0l hWedge (A_m_dual (hom_as_linear q) (vb l beta (q z)))).
Qed.
End CurrentCartesianTestProductEverywhere.
