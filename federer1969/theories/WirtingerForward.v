(** Federer (1969), 1.8.2, p. 40: Wirtinger's inequality
    and the necessity of its exact paired-product equality criterion.
    Normalisation is used only in positive degree. The literal empty
    product handles degree zero separately. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import SimpleVectors SimpleElementary SimpleZeroDegree
  ScalarRestriction ComplexScalarSealed ComplexPairedVectors
  HermitianUP HermitianRealImaginary HermitianRotation ExteriorNorm
  TwoFormPowers WirtingerUnitForward WirtingerZeroDegree PositivePairedScaling.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section Forward.
Variable R : realType.
Hypothesis h2 : (1+1 : R) != 0.
Variable V : lmodType (ComplexScalars.C R).
Variable H : V -> V -> ComplexScalars.C R.
Hypothesis hH : is_hermitian_product H.
Local Notation VR := (restricted_space (ComplexScalars.embed R) V).
Local Notation hB := (hermitian_real_inner_product hH).

(** Source for [wirtinger_bound_and_equality_forward]: Federer 1.8.2,
    p. 40, the inequality for all simple vectors and the necessity
    of the displayed paired representation in the equality case.
    Includes zero vectors and degree zero, in any ambient dimension. *)
Theorem wirtinger_bound_and_equality_forward m (x : exterior_power VR (m+m))
    (hs : simple x) :
  pairing x (two_form_power h2 (hermitian_two_form hH) m) <=
    m`!%:R * exterior_norm h2 hB x /\
  (pairing x (two_form_power h2 (hermitian_two_form hH) m) =
    m`!%:R * exterior_norm h2 hB x ->
    exists v : 'I_m -> V, x = paired_complex_vector v).
Proof.
case: m x hs => [|k] x hs.
- have hn := two_form_zeroth_simple_norm h2 hB hs.
  have hp := two_form_zeroth_simple_pairing h2 (hermitian_two_form hH) hs.
  rewrite hn hp /= mul1r; split; first exact: lexx.
  move=> _; exists (fun _ : 'I_0 => (0 : V)).
  move/(proj1 (simple_zero_iff x)): hs=> ->.
  symmetry; apply: (proj1 (simple_zero_iff (paired_complex_vector (fun _ : 'I_0 => (0 : V))))).
  exact (@paired_complex_vector_simple R V 0 (fun _ : 'I_0 => (0 : V))).
- case hx0 : (x == 0).
  + move/eqP: hx0=> ->.
    rewrite (bil0l (@pairing_bilinear R VR R^o (k.+1+k.+1))) exterior_norm_zero mulr0.
    split; first exact: lexx.
    move=> _; have [v hv] := @zero_paired_complex_representation R V k.
    exists v; exact: esym hv.
  + have hx : x != 0 by rewrite hx0.
    pose r := exterior_norm h2 hB x.
    have hr0 : r != 0 by rewrite /r exterior_norm_eq0.
    have hr : 0 < r by rewrite lt_def hr0 exterior_norm_nonnegative.
    pose y := r^-1 *: x.
    have hsy : simple y := simple_scale r^-1 (isT : (0 < k.+1+k.+1)%N) hs.
    have hny : exterior_norm h2 hB y = 1.
      by rewrite /y exterior_norm_scale ger0_norm ?invr_ge0 ?(ltW hr) // mulVf.
    have [hy hye] := @wirtinger_unit_bound_and_equality_forward R h2 V H hH k.+1 y hsy hny.
    have hxy : x = r *: y by rewrite /y scalerA mulfV // scale1r.
    have hp : pairing x (two_form_power h2 (hermitian_two_form hH) k.+1) =
      r * pairing y (two_form_power h2 (hermitian_two_form hH) k.+1).
      by rewrite {1}hxy (bilZl (@pairing_bilinear R VR R^o (k.+1+k.+1))).
    split.
    * rewrite hp -/r [k.+1`!%:R * r]mulrC.
      exact (ler_wpM2l (ltW hr) hy).
    * move=> he.
      have hpy : pairing y (two_form_power h2 (hermitian_two_form hH) k.+1) = k.+1`!%:R.
        apply: (mulfI hr0); by rewrite -hp he mulrC.
      have [v hv] := hye hpy.
      have [w hw] := nonnegative_scaled_paired_vector (ltW hr) v.
      exists w; by rewrite hw -hv -hxy.
Qed.
End Forward.
