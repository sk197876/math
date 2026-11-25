(** Federer (1969), 4.1.8, p. 362: use the
    original globally normalized test values when
    comparing product integrals. The original zero
    value outside the open test domain is the
    already proved 4.1.1 convention, p. 345. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct AlternatingForms CurrentCoefficientNorms CurrentSpaces
  SmoothFunctionSpaceUP SmoothTestEvaluation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [current_test_value_outside]: every actual
    original test form has its original normalized
    value zero outside its open domain, supporting
    product integration in Federer 4.1.8, p. 362,
    by 4.1.1, p. 345. *)
Lemma current_test_value_outside (R:realType) (h2:(1+1:R)!=0) n k
    (U:set (R_n R n))
    (hU:forall x,U x->norm_domain_interior (inner_norm (@euclidean_inner_productP R n)) U x)
    (phi:@current_test_space R h2 n U hU k) x:
  ~U x->@current_test_value R h2 n U hU k phi x=0.
Proof.
move=>hx.
exact:(@smooth_test_value_outside R (R_n R n) (A_m (R_n R n) R^o k)
  (inner_norm (@euclidean_inner_productP R n)) (@current_form_comass R h2 n k)
  (inner_norm_real_norm (@euclidean_inner_productP R n)) (@current_form_comass_real_norm R h2 n k)
  U (@current_smooth_space R h2 n U hU k) (@current_smooth_value R h2 n U hU k)
  (@current_smooth_space_laws R h2 n U hU k) phi x hx).
Qed.
