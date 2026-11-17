(** Recover actual coefficients from finitely many values
    in the polynomial comparison of Federer (1969),
    3.2.45, pp. 279–280. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations FiniteCoordinates EuclideanLinearMaps
  FinitePowerEvaluationUP RealMetricBackground PartialFunctionUP PartialFunctionBasic
  MeasureStepIntegralIdentification MeasureUP MeasureIntegralUP FiniteSignedRealIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [finite_power_evaluation_recovery]: supporting
    recovery of the individual tube coefficients in Federer
    3.2.45, pp. 279–280. The independent evaluation
    equations and a local inverse give an explicit
    finite linear combination of the actual values.
    This is finite linear algebra, 1.7.3, p. 30;
    no order inference about polynomial coefficients occurs. *)
Lemma finite_power_evaluation_recovery (R : realType) N
    (E G : {linear R_n R N.+1 -> R_n R N.+1}) :
  cancel E G -> forall (c : R_n R N.+1) i,
  c i=\sum_(j : 'I_N.+1) E c j*G (@coordinate_basis R N.+1 j) i.
Proof.
move=> hInverse c i; rewrite -{1}(hInverse c) (@euclidean_linear_expansion R N.+1 G (E c)) sum_ffunE.
apply: eq_bigr=> j _; by rewrite !ffunE.
Qed.

(** Source for [finite_power_evaluation_coefficient_integral]: supporting
    section-coefficient integration in Federer 3.2.45,
    pp. 279–280. Original coefficient functions are
    identified pointwise by the actual evaluation map.
    Their integrals follow from proved finite integrals
    of the value functions and the finite inverse
    formula. Negative inverse coefficients and empty
    or zero-volume sections require no extra premise. *)
Theorem finite_power_evaluation_coefficient_integral (R : realType) N (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (E G : {linear R_n R N.+1 -> R_n R N.+1})
    (c : X -> R_n R N.+1) (u : 'I_N.+1 -> X -> real_line_metric R)
    (b : 'I_N.+1 -> R) :
  cancel E G -> (forall x j, E (c x) j=u j x) ->
  (forall j, is_measure_integral mu
    (partial_real_function_embed (partial_function_total (u j))) (b j)%:E) ->
  forall i, is_measure_integral mu
    (partial_real_function_embed (partial_function_total (fun x => (c x i : real_line_metric R))))
    (\sum_(j : 'I_N.+1) b j*G (@coordinate_basis R N.+1 j) i)%:E.
Proof.
move=> hInverse hValues hIntegrals i.
have hFormula : (fun x => (c x i : real_line_metric R))=
    (fun x => (\sum_(j <- index_enum 'I_N.+1) G (@coordinate_basis R N.+1 j) i*u j x)).
  apply: funext=> x; rewrite (finite_power_evaluation_recovery hInverse).
  apply: eq_bigr=> j _; by rewrite hValues mulrC.
have h := @finite_signed_real_combination_integral R X 'I_N.+1 mu hm (index_enum 'I_N.+1) u b
  (fun j => G (@coordinate_basis R N.+1 j) i) (fun j _ => hIntegrals j).
rewrite -hFormula in h.
have hValue : (\sum_(j <- index_enum 'I_N.+1) G (@coordinate_basis R N.+1 j) i*b j)=
    \sum_(j : 'I_N.+1) b j*G (@coordinate_basis R N.+1 j) i.
  apply: eq_bigr=> j _; exact: mulrC.
by rewrite hValue in h.
Qed.
