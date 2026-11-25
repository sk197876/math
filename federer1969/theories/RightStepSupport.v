(** Federer (1969), 2.9.24, p. 169: the step approximation is used only on
    [a,b] and is zero outside its cells. These supporting laws allow the
    bounded-convergence calculation to use total real functions on the whole
    line. its zero extension is the subset convention of Federer 2.4.10, p.
    85. The local Federer erratum has no entry for this supporting step. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealMetricBackground CurveArcLength StieltjesIntegral
  StieltjesIntegrationByParts TaggedStepFunction TaggedStepBounds RightStepApproximation
  BVRightStepConvergence TotalScalarCutoff MeasureAlmostUP MeasureAlmostBasic
  LebesgueScalarMeasure RestrictedAlmostEverywhere ExtendedRealOrderLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [uniform_right_step_outside]: supporting zero
    extension of f_n in Federer 2.9.24, p. 169. It
    vanishes at and to the left of a, and strictly beyond b. *)
Lemma uniform_right_step_outside (R : realType) (f : R -> R) (a b : R) :
  a<=b -> forall (n : nat) (x : R), x<=a \/ b<x ->
    uniform_right_step_approximation f a b n x=0.
Proof.
move=> hab n x hx.
have hw := @uniform_right_tagged_is R a b n hab.
apply: (@tagged_step_function_outside R f _ hw.1 x).
have hend : a+n.+1%:R*((b-a)/n.+1%:R)=b.
  by rewrite mulrC mulfVK ?pnatr_eq0 // addrC subrK.
by rewrite uniform_right_tagged_head uniform_right_tagged_last hend.
Qed.

(** Source for [uniform_right_step_cutoff_product]: supporting
    identity f_n v=f_n v_[a,b] for Federer 2.9.24,
    p. 169. This is pointwise and requires no regularity
    or summability of the supplied total density v. *)
Lemma uniform_right_step_cutoff_product (R : realType) (f v : R -> R) (a b : R) :
  a<=b -> forall n : nat,
  (fun x => uniform_right_step_approximation f a b n x*v x)=
    (fun x => uniform_right_step_approximation f a b n x*
      total_scalar_cutoff (`[a,b] : set R) v x).
Proof.
move=> hab n; apply: funext=> x; case: (pselect ((`[a,b] : set R) x))=> hx.
- by rewrite (total_scalar_cutoff_on v hx).
- have hout : x<=a \/ b<x.
    case: (leP x a)=> hxa; first by left.
    right; rewrite ltNge; apply/negP=> hxb; apply: hx.
    by rewrite /= in_itv /= (ltW hxa) hxb.
  by rewrite (@uniform_right_step_outside R f a b hab n x hout) !mul0r.
Qed.

(** Source for [bv_right_step_cutoff_almost_limit]: supporting
    almost limit on the nonzero density locus in the bounded-
    convergence proof of Federer 2.9.24, p. 169. The
    density cutoff is zero outside [a,b]; on the interval
    the BV convergence theorem supplies the full sequence limit. *)
Lemma bv_right_step_cutoff_almost_limit (R : realType) (f v : R -> R) (a b : R) :
  curve_locally_finite_variation (f : R -> real_line_metric R) -> a<=b ->
  measure_almost_everywhere (@lebesgue_scalar_measure R)
    [set x | total_scalar_cutoff (`[a,b] : set R) v x=0 \/
      extended_order_limit (fun n => (uniform_right_step_approximation f a b n x)%:E) (f x)%:E].
Proof.
move=> hf hab.
have hl := @bv_right_step_almost_limit R f a b hf hab.
have hglobal := (restricted_almost_everywhere_iff _ _ _).1 hl.
apply: (@measure_almost_everywhere_mono R (real_line_metric R) _
  (lebesgue_scalar_is_measure R) _ _ _ hglobal)=> x hx.
case: (pselect ((`[a,b] : set R) x))=> hxI.
- right; exact: hx hxI.
- left; exact (@total_scalar_cutoff_off R R (`[a,b] : set R) v x hxI).
Qed.
