(** Federer (1969), 2.3.8, p. 79: characteristic pieces s_j f used in the
    finite convex combination. Source context: MeasurableNormedFunctionUP.v.
    The characteristic scalar is supplied through its laws, with no
    construction unfolded. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import ModuleQuotient RealNormUP NormMetric PartialFunctionUP
  PartialFunctionBasic PartialFunctionPreimages MeasureUP MeasureBasic MeasureAlmostBasic
  CharacteristicFunctionUP MeasurableNormedFunctionUP MeasurableNormedBasic
  MeasurableTotalPiecewise MeasurableTotalBasic MeasureGauge.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [characteristic_vector_piece]: direct pointwise
    product s_j f in Federer 2.3.8, p. 79, for total
    representatives. The abstract characteristic laws are premises
    of its properties. *)
Definition characteristic_vector_piece (R : realType) (X : Type) (V : lmodType R)
    (s : X -> R) (f : X -> V) x := (s x *: f x)%R.

(** Source for [measurable_normed_characteristic_piece]: measurability and
    essential separability of the pieces in Federer 2.3.8, p. 79 *)
Lemma measurable_normed_characteristic_piece (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_norm N)
    (mu : set X -> \bar R) (hm : is_measure mu) (A : set X)
    (s : X -> R) (f : X -> real_norm_metric_space hN) :
  is_characteristic_function A s -> measure_measurable mu A ->
  is_measurable_normed_function mu (partial_function_total f) ->
  is_measurable_normed_function mu (partial_function_total (characteristic_vector_piece s f)).
Proof.
move=> hs hA [hf [Z [hD hz]]]; split.
- have he : characteristic_vector_piece s f = (fun x => if pselect (A x) then f x else 0%R).
    apply: funext=> x; rewrite /characteristic_vector_piece; case: (pselect (A x))=> hx.
    + by rewrite (characteristic_on_set hs hx) scale1r.
    + by rewrite (characteristic_off_set hs hx) scale0r.
  rewrite he; apply: (@measurable_total_piecewise R X
    [the topologicalType of real_norm_metric_space hN] mu hm A f (fun _ => 0%R) hA hf).
  exact: measurable_total_constant.
- exists Z; split=> //.
  rewrite partial_function_total_preimage in hz.
  rewrite partial_function_total_preimage.
  apply: (@measure_null_subset R X mu hm _ _ _ hz).
  move=> x hn hzx.
  have hn' : ~ Z (characteristic_vector_piece s f x) := hn.
  apply: hn'; exact (@subspace_scale R V Z (s x) (f x) hzx).
Qed.

(** Source for [measure_gauge_characteristic_piece_bound]: direct
    support estimate for the summands in Federer 2.3.8,
    p. 79: |s_j f|_mu <= mu(S_j). It remains true
    without measurability or a finite bound on f. *)
Lemma measure_gauge_characteristic_piece_bound (R : realType) (X : choiceType)
    (V : lmodType R) (N : V -> R) (hN : is_real_seminorm N)
    (mu : set X -> \bar R) (hm : is_measure mu) (A : set X)
    (s : X -> R) (f : X -> V) : is_characteristic_function A s ->
  measure_gauge mu N (partial_function_total (characteristic_vector_piece s f)) <= mu A.
Proof.
move=> hs; apply: measure_gauge_bound; split; first exact: measure_nonnegative.
apply: (@measure_mono R X mu hm)=> x [y [<- hy]].
apply: contrapT=> hx.
have hy' : mu A < (N (characteristic_vector_piece s f x))%:E := hy.
by move: hy'; rewrite /characteristic_vector_piece (characteristic_off_set hs hx)
  scale0r (real_seminorm_zero hN) ltNge (measure_nonnegative hm).
Qed.
