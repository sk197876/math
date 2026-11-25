(** Federer (1969), 4.1.8, p. 360: independent specification
    of the smooth separated form p#alpha wedge q#beta before proving
    compact support. Its values use the original block projections
    and the original pullback and exterior product on covectors. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom TensorUP RealNormUP NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  EuclideanBlockLinearMaps EuclideanCartesianMap AlternatingForms AlternatingDual
  AlternatingProduct ScalarCoefficients CurrentSpaces CurrentCartesianDomain.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentCartesianSmoothProductUP.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables m n:nat.
Variable A:set (R_n R m).
Variable B:set (R_n R n).
Hypothesis hA:forall a,A a->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R m)) A a.
Hypothesis hB:forall b,B b->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) B b.
Local Notation Z := (R_n R (m+n)).
Local Notation AB := (@euclidean_cartesian_set R m n A B).
Local Notation hAB := (@current_cartesian_domain_open R m n A B hA hB).
Local Notation DA := (fun k=>@current_test_space R h2 m A hA k).
Local Notation DB := (fun k=>@current_test_space R h2 n B hB k).
Local Notation EC := (fun k=>@current_smooth_space R h2 (m+n) AB hAB k).
Local Notation va := (fun k=>@current_test_value R h2 m A hA k).
Local Notation vb := (fun k=>@current_test_value R h2 n B hB k).
Local Notation vc := (fun k=>@current_smooth_value R h2 (m+n) AB hAB k).
Local Notation p := (@euclidean_first_block_map R m n).
Local Notation q := (@euclidean_last_block_map R m n).

(** Source for [is_current_cartesian_smooth_product]: the
    separated forms in the characterising equations of Federer
    4.1.8, p. 360, at the smooth-space stage. This independent
    specification includes bilinearity and exact values. It assumes
    no compact support, existence, density or current-product law. *)
Definition is_current_cartesian_smooth_product k l
    (F:DA k->DB l->EC (k+l)):Prop:=
  bilinear F /\
  forall alpha beta z,AB z->
    vc (k+l) (F alpha beta) z=
      @form_wedge R h2 Z R^o (fun a b:R^o=>a*b) (@scalar_bilinear R) k l
        (A_m_dual (hom_as_linear p) (va k alpha (p z)))
        (A_m_dual (hom_as_linear q) (vb l beta (q z))).
End CurrentCartesianSmoothProductUP.
