(** Federer (1969), 4.1.8, p. 360: the test in the
    first variables to which S is applied in the displayed
    definition of phi_S. This specification retains the actual
    first injection P and last injection Q, the original right
    interior and every original point of the open domains. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom TensorUP Bilinear RealNormUP NormDifferentialUP
  InnerNorm HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  EuclideanBlockCoordinates EuclideanBlockLinearMaps EuclideanCartesianMap
  ExteriorGrading ExteriorMaps ExteriorHomogeneousProducts AlternatingForms
  AlternatingDual CurrentSpaces CurrentVectorFormInterior CurrentCartesianDomain.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentCartesianSliceTestUP.
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
Local Notation P := (@euclidean_first_injection_map R m n).
Local Notation Q := (@euclidean_last_injection_map R m n).

(** Source for [is_current_cartesian_slice_test]: the original
    first-variable test has value Lambda^i P applied to the
    interior of Lambda_j Q eta with phi(a,b), in Federer
    4.1.8, p. 360. The equal-degree cast only identifies
    i+j with j+i. This definition assumes no existence,
    parameter smoothness, continuity or product-current theorem. *)
Definition is_current_cartesian_slice_test i j
    (G:forall b:R_n R n,B b->exterior_power (R_n R n) j->DC (i+j)->DA i):Prop:=
  forall b (hb:B b),bilinear (G b hb) /\
    forall eta phi a,A a->
      @current_test_value R h2 m A hA i (G b hb eta phi) a=
        A_m_dual (hom_as_linear P)
          (@current_vector_form_interior R (R_n R (m+n)) j i
            (exterior_power_map (hom_as_linear Q) j eta)
            (form_reindex (addnC i j)
              (@current_test_value R h2 (m+n) AB hAB (i+j) phi
                (@euclidean_block_join R m n (a,b))))).
End CurrentCartesianSliceTestUP.
