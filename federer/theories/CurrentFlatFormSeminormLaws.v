(** Federer (1969), 4.1.12, p. 367: the original
    flat form and test seminorms satisfy the original
    seminorm laws. Reuse the preceding exact compact
    derivative bounds and actual linear exterior derivative. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import RealNormUP NormDifferentialUP InnerNorm HilbertFormCompactness
  GrassmannAbbreviations EuclideanInnerProduct AlternatingForms CurrentCoefficientNorms CurrentSpaces
  Hom RealSeminormOperations RealSeminormMaximum SmoothCompactSet SmoothFunctionTopology
  SmoothDerivativeSeminormLaws SmoothCurrentExteriorDerivative SmoothTestSpaces
  CurrentFlatFormSeminormSealed.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Section CurrentFlatFormSeminormLaws.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables n m:nat.
Local Notation X := (R_n R n).
Local Notation NX := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Variable U:set X.
Hypothesis hU:forall x,U x->norm_domain_interior NX U x.
Arguments hU : clear implicits.
Local Notation E := (@current_smooth_space R h2 n U hU m).
Local Notation Next := (@current_smooth_space R h2 n U hU m.+1).
Local Notation hD := (@current_smooth_derivative_laws R h2 n U hU m).
Local Notation hNextD := (@current_smooth_derivative_laws R h2 n U hU m.+1).
Local Notation nu := (smooth_function_derivative_seminorm hD).
Local Notation nuNext := (smooth_function_derivative_seminorm hNextD).
Local Notation d := (@smooth_current_exterior_derivative R h2 n m U hU).

Local Notation F := (@CurrentFlatFormSeminorm.value R h2 n m U hU).
Local Notation hE := (@current_smooth_space_laws R h2 n U hU m).
Local Notation DT := (@current_test_space R h2 n U hU m).

(** Source for [current_flat_form_seminorm_formula]: the
    sealed F_K has exactly its original maximum formula,
    Federer 4.1.12, p. 367. *)
Lemma current_flat_form_seminorm_formula (K:smooth_compact_set hNX U) phi:
  F K phi=Num.max (nu K 0%N phi) (nuNext K 0%N (d phi)).
Proof. exact:(@CurrentFlatFormSeminorm.laws R h2 n m U hU K phi). Qed.

(** Source for [current_flat_form_is_seminorm]: the
    original F_K is a seminorm on E^m(U),
    Federer 4.1.12, p. 367, including empty K. *)
Theorem current_flat_form_is_seminorm (K:smooth_compact_set hNX U):
  is_real_seminorm (F K).
Proof.
have hFormula:F K=(fun phi=>Num.max (nu K 0%N phi) (nuNext K 0%N (d phi))):=
  funext (current_flat_form_seminorm_formula K).
rewrite hFormula;apply:real_seminorm_maximum.
- exact:(smooth_derivative_seminorm_is_seminorm (smooth_function_derivative_seminorm_laws hD K 0%N)).
- apply:(@real_seminorm_linear_precompose R E Next (nuNext K 0%N));last exact:hom_linear.
  exact:(smooth_derivative_seminorm_is_seminorm (smooth_function_derivative_seminorm_laws hNextD K 0%N)).
Qed.

(** Source for [current_flat_test_seminorm]: the original
    flat seminorm restricted to actual compact tests,
    used for the dual supremum in Federer 4.1.12,
    p. 367. This is restriction of the sealed operation. *)
Definition current_flat_test_seminorm (K:smooth_compact_set hNX U) (phi:DT):R:=
  F K (smooth_test_inclusion hE phi).

(** Source for [current_flat_test_is_seminorm]: the
    actual compact-test restriction retains the seminorm
    laws, supporting Federer 4.1.12, p. 367. *)
Theorem current_flat_test_is_seminorm (K:smooth_compact_set hNX U):
  is_real_seminorm (current_flat_test_seminorm K).
Proof.
exact:(@real_seminorm_linear_precompose R DT E (F K)
  (current_flat_form_is_seminorm K) (smooth_test_inclusion hE)
  (hom_linear (smooth_test_inclusion hE))).
Qed.
End CurrentFlatFormSeminormLaws.
