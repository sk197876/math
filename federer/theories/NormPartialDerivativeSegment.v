(** Federer (1969), 3.1.1, p. 211: apply 2.2.7 to each coordinate
    segment. Derivative bounds imply endpoint increment bounds without
    a completeness or finite-dimensional hypothesis on the target. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals lra.
From Federer Require Import Hom RealNormUP FiniteCoordinates GrassmannAbbreviations
  NormDifferentialUP NormDifferentialScalar NormDifferentialConvexBound
  NormPartialDerivative NormPartialDerivativeCalculus NormedCurveDerivativeUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [normed_curve_derivative_segment_bound]: supporting
    one-dimensional application of 2.2.7 in Federer 3.1.1, p. 211.
    A bound C for every derivative on the parameter interval [0,1]
    bounds the endpoint increment by C. *)
Lemma normed_curve_derivative_segment_bound (R : realType) (Y : lmodType R)
    (NY : Y -> R) (hNY : is_real_norm NY) (q : R -> Y) (C : R) :
  0 <= C ->
  (forall t : R, 0 <= t -> t <= 1 -> exists v : Y,
    has_normed_curve_derivative NY q t v /\ NY v <= C) ->
  NY (q 1-q 0) <= C.
Proof.
move=> hC hq.
have hconv : forall x y : R^o, (0 <= x /\ x <= 1) ->
    (0 <= y /\ y <= 1) -> forall t : R, 0 <= t -> t <= 1 ->
    0 <= (1-t)*:x+t*:y /\ (1-t)*:x+t*:y <= 1.
  move=> x y [hx0 hx1] [hy0 hy1] t ht0 ht1.
  change (0 <= (1-t)*x+t*y /\ (1-t)*x+t*y <= 1).
  split; nra.
have hdiff : forall t : R^o, (0 <= t /\ t <= 1) -> exists L : Hom R^o Y,
    has_norm_differential (fun s : R^o => `|s|) NY (fun _ => True) q t L /\
    forall s : R^o, NY (L s) <= C*`|s|.
  move=> t [ht0 ht1]; have [v [hv hb]] := hq t ht0 ht1.
  have hlin : linear (fun s : R^o => s *: v).
    by move=> c s u; rewrite scalerDl scalerA.
  pose L := @HomMap R R^o Y (fun s => s *: v) (introT (asboolP _) hlin).
  exists L; split.
  - apply: (proj2 (@norm_differential_real_source R Y NY hNY (fun _ => True) q t L)).
    split.
    + exists 1; split; first exact: ltr01.
      by move=> s _.
    + change (has_normed_curve_derivative NY q t (1 *: v)); by rewrite scale1r.
  - move=> s; change (NY (s *: v) <= C*`|s|).
    rewrite (real_seminorm_scale hNY.1) mulrC.
    apply: ler_wpM2r; first exact: normr_ge0.
    exact hb.
have hh := @norm_differential_convex_bound R R^o Y (fun s => `|s|) NY
  (@scalar_absolute_value_norm R) hNY (fun _ => True)
  (fun t => 0 <= t /\ t <= 1) q C hconv hC hdiff 1 0
  (conj ler01 (lexx _)) (conj (lexx _) ler01).
by rewrite subr0 normr1 mulr1 in hh.
Qed.

(** Source for [norm_partial_derivative_segment_bound]: the
    inequality for one coordinate increment in Federer 3.1.1, p. 211.
    A uniform bound C for the corresponding partial derivative along
    the segment bounds the function increment by C times its length. *)
Theorem norm_partial_derivative_segment_bound (R : realType) n
    (Y : lmodType R) (NY : Y -> R) (hNY : is_real_norm NY)
    (f : R_n R n -> Y) (b : R_n R n) (i : 'I_n) (c C : R) :
  0 <= C ->
  (forall t : R, 0 <= t -> t <= 1 -> exists v : Y,
    has_norm_partial_derivative NY f (b+(t*c) *: (@coordinate_basis R n i)) i v /\
    NY v <= C) ->
  NY (f (b+c *: (@coordinate_basis R n i))-f b) <= C*`|c|.
Proof.
move=> hC hf.
have hbound : NY
    (f (b+(1*c) *: (@coordinate_basis R n i))-
     f (b+(0*c) *: (@coordinate_basis R n i))) <= C*`|c|.
  apply: (@normed_curve_derivative_segment_bound R Y NY hNY
    (fun t => f (b+(t*c) *: (@coordinate_basis R n i))) (C*`|c|)).
  - exact: mulr_ge0 hC (normr_ge0 c).
  - move=> t ht0 ht1; have [v [hv hb]] := hf t ht0 ht1.
    exists (c *: v); split.
    + exact: (@norm_partial_scaled_coordinate_curve R n Y NY hNY f b i c t v hv).
    + rewrite (real_seminorm_scale hNY.1) mulrC.
      apply: ler_wpM2r; first exact: normr_ge0.
      exact hb.
by rewrite mul1r mul0r scale0r addr0 in hbound.
Qed.
