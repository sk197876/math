(** Federer (1969), 1.8.2, p. 40: Wirtinger's inequality
    and its complete equality characterisation. Hermitian products
    are specified by their laws, and the ambient complex vector
    space need not be finite-dimensional. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import SimpleVectors ScalarRestriction ComplexScalarSealed
  ComplexPairedVectors HermitianUP HermitianRealImaginary HermitianRotation
  ExteriorNorm TwoFormPowers WirtingerForward WirtingerPairedEquality.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Inequality.
Variable R : realType.
Hypothesis h2 : (1+1 : R) != 0.
Variable V : lmodType (ComplexScalars.C R).
Variable H : V -> V -> ComplexScalars.C R.
Hypothesis hH : is_hermitian_product H.
Local Notation VR := (restricted_space (ComplexScalars.embed R) V).
Local Notation hB := (hermitian_real_inner_product hH).

(** Source for [wirtinger_inequality]: Federer 1.8.2,
    p. 40, first displayed inequality: a simple real 2m-vector
    evaluates on A^m to at most m! times its Euclidean norm. *)
Theorem wirtinger_inequality m (x : exterior_power VR (m+m)) : simple x ->
  pairing x (two_form_power h2 (hermitian_two_form hH) m) <=
    m`!%:R * exterior_norm h2 hB x.
Proof. move=> hs; exact: (proj1 (wirtinger_bound_and_equality_forward h2 hH hs)). Qed.

(** Source for [wirtinger_equality]: Federer 1.8.2,
    p. 40, equality holds exactly for the displayed product of
    real-imaginary pairs. Zero vectors in positive degree and the
    literal empty product in degree zero are both included. *)
Theorem wirtinger_equality m (x : exterior_power VR (m+m)) (hs : simple x) :
  pairing x (two_form_power h2 (hermitian_two_form hH) m) =
    m`!%:R * exterior_norm h2 hB x <->
  exists v : 'I_m -> V, x = paired_complex_vector v.
Proof.
split; first exact: (proj2 (wirtinger_bound_and_equality_forward h2 hH hs)).
move=> [v ->]; exact: wirtinger_paired_equality.
Qed.
End Inequality.
