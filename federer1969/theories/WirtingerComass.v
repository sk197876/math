(** Federer (1969), 1.8.2, p. 40: the comass of A^m
    equals m! when the complex dimension is at least m. The
    dimension condition is expressed by an independent m-frame,
    so even the ambient space may be infinite-dimensional. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import SimpleVectors SimpleElementary SimpleUnitBall
  ScalarRestriction ComplexScalarSealed ComplexPairedVectors ComplexPairedPlanes
  HermitianUP HermitianRealImaginary HermitianRotation ExteriorNorm
  TwoFormPowers WirtingerForward WirtingerPairedEquality WirtingerZeroDegree
  ComassUP FiniteIndependence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section Comass.
Variable R : realType.
Hypothesis h2 : (1+1 : R) != 0.
Variable V : lmodType (ComplexScalars.C R).
Variable H : V -> V -> ComplexScalars.C R.
Hypothesis hH : is_hermitian_product H.
Local Notation VR := (restricted_space (ComplexScalars.embed R) V).
Local Notation hB := (hermitian_real_inner_product hH).

(** Source for [wirtinger_simple_ball_bound]: Federer 1.8.2,
    p. 40, the inequality bounds every evaluation used in the
    defining comass supremum by m!, including m=0. *)
Lemma wirtinger_simple_ball_bound m (x : exterior_power VR (m+m)) :
  simple_unit_ball h2 hB x ->
  pairing x (two_form_power h2 (hermitian_two_form hH) m) <= m`!%:R.
Proof.
move=> [hs hn].
have hb := proj1 (wirtinger_bound_and_equality_forward h2 hH hs).
apply: (le_trans hb); apply: ler_piMr; first exact: ler0n.
exact hn.
Qed.

(** Source for [wirtinger_comass_specification]: Federer 1.8.2,
    p. 40, the concluding formula ||A^m||=m!. An independent
    complex m-frame is the precise dimension hypothesis. This
    supplies the supremum laws directly, without assuming that
    the ambient space has a finite basis. *)
Theorem wirtinger_comass_specification m (v : 'I_m -> V)
    (hv : finite_independent v) :
  is_comass h2 hB (two_form_power h2 (hermitian_two_form hH) m) m`!%:R.
Proof.
case: m v hv => [|k] v hv; first exact: two_form_zeroth_comass.
pose x := paired_complex_vector v.
have hx : x != 0 := independent_paired_vector_nonzero hv.
pose r := exterior_norm h2 hB x.
have hr0 : r != 0 by rewrite /r exterior_norm_eq0.
have hr : 0 < r by rewrite lt_def hr0 exterior_norm_nonnegative.
pose y := r^-1 *: x.
have hs : simple y := simple_scale r^-1 (isT : (0 < k.+1+k.+1)%N)
  (@paired_complex_vector_simple R V k.+1 v).
have hn : exterior_norm h2 hB y = 1.
  by rewrite /y exterior_norm_scale ger0_norm ?invr_ge0 ?(ltW hr) // mulVf.
have hp : pairing y (two_form_power h2 (hermitian_two_form hH) k.+1) = k.+1`!%:R.
  rewrite /y (bilZl (@pairing_bilinear R VR R^o (k.+1+k.+1))).
  rewrite (wirtinger_paired_equality h2 hH v).
  change (r^-1 * (k.+1`!%:R * r) = k.+1`!%:R).
  by rewrite mulrCA mulVf // mulr1.
constructor; first exact: wirtinger_simple_ball_bound.
move=> eps heps; exists y; split.
- split=> //; by rewrite hn.
- by rewrite hp ltrBlDr ltrDl.
Qed.

(** Source for [wirtinger_comass_value]: Federer 1.8.2,
    p. 40, uniqueness identifies any number satisfying the
    abstract comass laws with the computed factorial. *)
Theorem wirtinger_comass_value m (v : 'I_m -> V)
    (hv : finite_independent v) c
    (hc : is_comass h2 hB (two_form_power h2 (hermitian_two_form hH) m) c) :
  c = m`!%:R.
Proof. exact: comass_unique hc (wirtinger_comass_specification hv). Qed.
End Comass.
