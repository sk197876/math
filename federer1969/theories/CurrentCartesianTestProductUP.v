(** Federer (1969), 4.1.8, p. 360: independent specification of
    the actual separated test p#alpha wedge q#beta. Each factor test
    retains its original domain and the product uses the canonical
    Euclidean block identification. Existence is a separate obligation. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom TensorUP Bilinear RealNormUP NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  EuclideanBlockLinearMaps EuclideanCartesianMap AlternatingForms AlternatingDual
  AlternatingProduct ScalarCoefficients CurrentSpaces CurrentCartesianDomain.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentCartesianTestProductUP.
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

(** Source for [is_current_cartesian_test_product]: the original pure
    tests in the characterising condition of Federer 4.1.8, p. 360.
    Bilinearity and actual pointwise values specify a map between the
    genuine test spaces. The specification assumes neither its
    existence nor the density or continuity conclusions needed later. *)
Definition is_current_cartesian_test_product k l
    (F:DA k->DB l->DC (k+l)):Prop:=
  bilinear F /\
  forall alpha beta z,AB z->
    vc (k+l) (F alpha beta) z=
      @form_wedge R h2 Z R^o (fun a b:R^o=>a*b) (@scalar_bilinear R) k l
        (A_m_dual (hom_as_linear p) (va k alpha (p z)))
        (A_m_dual (hom_as_linear q) (vb l beta (q z))).
End CurrentCartesianTestProductUP.
