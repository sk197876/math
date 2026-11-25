(** Federer (1969), 4.1.19, p. 377:
    the zero measurable form is the
    second density representing a coboundary.
    Its measurability and bound follow from
    the earlier constant-field and actual norm laws. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals constructive_ereal topology.
From Federer Require Import AlternatingForms Hom RealNormUP NormMetric NormDifferentialUP InnerNorm
  HilbertFormCompactness GrassmannAbbreviations EuclideanInnerProduct
  CurrentDomain CurrentCoefficientNorms PartialFunctionBasic
  MeasurableNormedBasic EuclideanOpenDomainMeasure FlatCochainRepresentationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope ring_scope.

(** Source for [bounded_measurable_current_form_zero]:
    the zero form in every natural
    degree is bounded measurable on the
    original U, supporting d alpha=(psi,0)
    in Federer 4.1.19, p. 377.
    Empty U and the zero coefficient space are allowed. *)
Theorem bounded_measurable_current_form_zero (R : realType)
    (h2 : (1+1:R)!=0) n d (U : set (R_n R n))
    (hU : forall x, U x -> norm_domain_interior
      (inner_norm (@euclidean_inner_productP R n)) U x) :
  @is_bounded_measurable_current_form R h2 n U d
    (fun _ : current_domain R n U => 0).
Proof.
split.
- exact: (@measurable_normed_total_constant R (current_domain R n U)
    (A_m (R_n R n) R^o d) (@current_form_comass R h2 n d)
    (@current_form_comass_real_norm R h2 n d)
    (@euclidean_open_domain_measure R n U)
    (proj1 (@euclidean_open_domain_measure_laws R n U hU)) 0).
- exists 0; split; first exact: lexx.
  move=> x; by rewrite (real_seminorm_zero
    (@current_form_comass_real_norm R h2 n d).1).
Qed.
