(** Federer (1969), 4.1.7, pp. 355–356,
    used in 4.1.12, pp. 368–369:
    multiplying an original smooth form by
    a compact scalar test gives an actual
    compact test with exactly those values.
    Keep the original equal-degree transport explicit. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom TensorUP Bilinear RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct AlternatingForms AlternatingZero AlternatingProduct ScalarCoefficients
  ExteriorHomogeneousProducts CurrentSpaces CurrentDegreeTransport CurrentTestFormProduct CurrentScalarFormProduct.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentScalarCutoffFormTest.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Variable U:set (R_n R n).
Hypothesis hU:forall x,U x->norm_domain_interior
  (inner_norm (@euclidean_inner_productP R n)) U x.
Local Notation E := (@current_smooth_space R h2 n U hU m).
Local Notation D0 := (@current_test_space R h2 n U hU 0%N).
Local Notation DT := (@current_test_space R h2 n U hU m).

(** Source for [current_scalar_cutoff_form_test]: the
    original compact scalar multiplication of a
    smooth m-form, supporting Federer 4.1.12,
    pp. 368–369. It aliases the
    already continuous test product and degree map. *)
Definition current_scalar_cutoff_form_test (phi:E) (gamma:D0):DT:=
  @current_test_degree_transport R h2 n U hU (m+0)%N m (addn0 m)
    (@current_test_form_product R h2 n m 0%N U hU phi gamma).

(** Source for [current_scalar_cutoff_form_test_values]:
    the actual test value is gamma(x)
    times the given smooth form value,
    supporting the calibration of the original
    interval sums in Federer 4.1.12,
    pp. 368–369. *)
Lemma current_scalar_cutoff_form_test_values phi gamma x:U x->
  @current_test_value R h2 n U hU m (current_scalar_cutoff_form_test phi gamma) x=
    (zero_form_value (@current_test_value R h2 n U hU 0%N gamma x):R)*:
    @current_smooth_value R h2 n U hU m phi x.
Proof.
move=>hx.
have hTransport:=@current_test_degree_transport_values R h2 n U hU (m+0)%N m (addn0 m)
  (@current_test_form_product R h2 n m 0%N U hU phi gamma) x.
rewrite (@current_test_form_product_values R h2 n m 0%N U hU phi gamma x hx) in hTransport.
have hScalar:form_reindex (addn0 m)
    (form_wedge h2 (scalar_bilinear R) (@current_smooth_value R h2 n U hU m phi x)
      (@current_test_value R h2 n U hU 0%N gamma x))=
    (zero_form_value (@current_test_value R h2 n U hU 0%N gamma x):R)*:
      @current_smooth_value R h2 n U hU m phi x.
  rewrite -{1}(zero_form_valueK (@current_test_value R h2 n U hU 0%N gamma x)).
  exact:current_form_wedge_zero_scalar.
exact:eq_trans hTransport hScalar.
Qed.
End CurrentScalarCutoffFormTest.
