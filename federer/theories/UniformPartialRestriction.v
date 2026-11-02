(** Supporting restriction of the uniform conclusion in Federer (1969),
    2.3.7, pp. 77–78. Source context: Egoroff.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import PartialFunctionUP PartialFunctionLimitUP UniformPartialConvergenceUP
  MeasureUP MeasureFiniteClosure MeasureAlmostUP MeasurableFunctionUP Egoroff.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [uniform_partial_convergence_subset]: supporting restriction
    property for Federer 2.3.7, pp. 77–78 *)
Lemma uniform_partial_convergence_subset (R : realType) (X : Type) (Y : metricType R)
    (B C : set X) (f : nat -> partial_function X Y) (g : partial_function X Y) :
  C `<=` B -> partial_function_uniformly_converges_on B f g ->
  partial_function_uniformly_converges_on C f g.
Proof.
move=> hs hf; constructor.
- move=> x hx; exact: (@uniform_partial_domain R X Y B f g hf x (hs x hx)).
- move=> e he; have [N hN] := @uniform_partial_distance R X Y B f g hf e he.
  exists N=> n hn x y z hx hy hz; exact: hN n hn x y z (hs x hx) hy hz.
Qed.

(** Source for [egoroff_measurable_source_subset]: supporting strengthening
    of Federer 2.3.7, pp. 77–78. *)
Theorem egoroff_measurable_source_subset (R : realType) (X : choiceType)
    (Y : metricType R) (mu : set X -> \bar R) (hm : is_measure mu)
    (D : set Y) (A : set X) (f : nat -> partial_function X Y)
    (g : partial_function X Y) (e : R) : countable D -> dense D ->
  (forall n, is_measure_measurable_function mu (f n)) -> is_measure_measurable_function mu g ->
  measure_measurable mu A -> mu A < +oo ->
  measure_almost_everywhere_on mu A (partial_function_limit_locus f g) ->
  (0 < e)%R -> exists B, measure_measurable mu B /\ B `<=` A /\
    mu (A `\` B) < e%:E /\ partial_function_uniformly_converges_on B f g.
Proof.
move=> hc hd hf hg hA hfin hlim he.
have [B [hB [herr hu]]] := @egoroff_measurable_partial_functions R X Y mu hm D A f g e
  hc hd hf hg hfin hlim he.
exists (A `&` B); split; first exact: (@measure_measurable_intersection R X mu hm A B hA hB).
split; first by move=> x [hx _].
split.
- have heq : A `\` (A `&` B) = A `\` B.
    apply/seteqP; split=> x [hx hn]; split=> //.
    + move=> hb; apply: hn; by split.
    + by move=> [_ hb]; exact: hn hb.
  by rewrite heq.
- apply: (@uniform_partial_convergence_subset R X Y B (A `&` B) f g _ hu).
  by move=> x [_ hx].
Qed.
