(** Federer (1969), 3.1.1, p. 211: since im f is separable,
    one may replace Y by a closed separable linear subspace
    containing it. The witness uses the already sealed closed
    linear span of countably many values on a dense domain set. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets cardinality reals topology.
From Federer Require Import ModuleQuotient RealNormUP NormMetric LinearBasis
  FiniteNormMetricPolish MetricSubsetBackground MetricSubsetSeparability
  ClosedLinearSpanUP ClosedLinearSpanSealed NormClassOneUP NormClassZeroTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [norm_class_zero_separable_linear_range]: the
    separable-range reduction in 3.1.1, p. 211. The subspace is
    closed in the original norm and contains every actual value
    of f. No separability of the original target is assumed. *)
Theorem norm_class_zero_separable_linear_range (R : realType)
    (X Y : lmodType R) (NX : X -> R) (NY : Y -> R)
    (hNX : is_real_norm NX) (hNY : is_real_norm NY)
    n (e : 'I_n -> X) (he : is_basis e) (A : set X) (f : X -> Y) :
  norm_class_zero NX NY A f ->
  exists S : subspace Y, is_separable_linear_envelope
    ((fun x : real_norm_metric_space hNX => (f x : real_norm_metric_space hNY)) @` A) S.
Proof.
move=> hf.
pose E := real_norm_metric_space hNX.
pose T := real_norm_metric_space hNY.
have [D [hc hd]] := @metric_subset_separable R E A (finite_norm_metric_separable hNX he).
pose g := fun x : @metric_subset R E A => (f (val x) : T).
have hg : continuous g := @norm_class_zero_restriction_continuous R X Y NX NY hNX hNY A f hf.
pose H := g @` D.
have hH : countable H := sub_countable (card_image_le _ _) hc.
pose S := @ClosedLinearSpan.value R Y NY hNY H.
have hS := @ClosedLinearSpan.laws R Y NY hNY H.
exists S; split; first exact: closed_linear_span_closed hS.
split; last exact: (@ClosedLinearSpan.countable_separable R Y NY hNY H hH).
move=> y [x hx <-].
apply: (closed_linear_span_closed hS).
apply: (@closureS T H (fun y : T => S y) (closed_linear_span_contains hS)).
move=> W hW.
pose a : @metric_subset R E A := @exist E (fun z=>z \in A) x (mem_set hx).
have hn : nbhs a (g @^-1` W) := hg a W hW.
have [U [ho ha] hUW] := hn.
have [b [hb hDb]] := hd U (ex_intro _ a ha) ho.
exists (g b); split; first by exists b.
exact: hUW b hb.
Qed.
