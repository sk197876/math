(** Federer (1969), 2.4.1, pp. 80–81: a real constant factors out of a sum
    of nonnegative fibre measures, including coefficient zero and infinite
    fibre measures. This supporting specialization of 2.1.1(6),(11), pp.
    52–53, uses the explicit 0 times infinity equals 0 convention. source
    editions: MeasureStepFunctionUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal.
From Federer Require Import NonnegativeSum NonnegativeSumSupport NumericalSum NumericalSumValues NumericalSumScale.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [numerical_sum_real_weight_nonnegative]: supporting
    extraction of a real weight from the fibre sum in Federer
    2.4.1, p. 81; zero weights are included explicitly. *)
Lemma numerical_sum_real_weight_nonnegative (R : realType) (I : choiceType)
    (A : set I) (f : I -> \bar R) (c : R) :
  (forall x, A x -> 0 <= f x) ->
  numerical_sum A (fun x => c%:E * f x) = Some (c%:E * nonnegative_sum A f).
Proof.
move=> hf; case: (eqVneq c 0%R)=> [->|hc].
- have he : numerical_sum A (fun x => (0 : \bar R)*f x) = numerical_sum A (fun _ => 0).
    apply: numerical_sum_ext=> x hx; exact: mul0e.
  rewrite he (numerical_sum_nonnegative (fun x (_ : A x) => lexx (0 : \bar R))).
  by rewrite (nonnegative_sum_zero (fun x (_ : A x) => erefl (0 : \bar R))) mul0e.
- by rewrite (@numerical_sum_scale R I A f c hc) (numerical_sum_nonnegative hf).
Qed.
