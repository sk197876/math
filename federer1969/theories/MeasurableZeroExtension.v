(** Federer (1969), 2.4.10, p. 85: measurability of f_A for measurable A and
    f, supporting integrals over subsets. The proof uses open inverse images
    and the exact zero-extension graph. Source context:
    PartialZeroExtensionUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import PartialFunctionUP PartialZeroExtension PartialZeroExtensionLaws
  MeasureUP MeasureAlmostUP MeasureAlmostBasic MeasureFiniteClosure MeasureSplit MeasurableFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [zero_extension_conull_domain]: supporting domain
    condition for f_A in Federer 2.4.10, p. 85:
    a conull domain remains conull after adjoining zeros outside A. *)
Lemma zero_extension_conull_domain (R : realType) (X : choiceType) (Y : Type)
    (mu : set X -> \bar R) (hm : is_measure mu) (zero : Y)
    (A : set X) (f : partial_function X Y) :
  measure_almost_everywhere mu (partial_function_domain f) ->
  measure_almost_everywhere mu (partial_function_domain (partial_function_zero_extension zero A f)).
Proof.
move=> hd; rewrite partial_function_zero_extension_domain.
apply: (@measure_almost_everywhere_mono R X mu hm _ _ _ hd)=> x hx.
have [ha|ha] := pselect (A x); [left; by split|by right].
Qed.

(** Source for [zero_extension_relative_domain]: the weaker
    domain premise in the first sentence of Federer 2.4.10,
    p. 85, is exactly the conull-domain condition for f_A. *)
Lemma zero_extension_relative_domain (R : realType) (X : choiceType) (Y : Type)
    (mu : set X -> \bar R) (zero : Y)
    (A : set X) (f : partial_function X Y) :
  measure_almost_everywhere_on mu A (partial_function_domain f) <->
  measure_almost_everywhere mu (partial_function_domain (partial_function_zero_extension zero A f)).
Proof.
rewrite /measure_almost_everywhere_on /measure_almost_everywhere partial_function_zero_extension_domain.
have he : ~` ((A `&` partial_function_domain f) `|` (~` A)) = A `\` partial_function_domain f.
  apply/seteqP; split=> x.
  - move=> hn.
    have hA : A x.
      apply: contrapT=> ha; exact (hn (or_intror ha)).
    split=> // hf; exact (hn (or_introl (conj hA hf))).
  - move=> [ha hf] [[_ hx]|hx]; [exact: hf hx|exact: hx ha].
by rewrite he.
Qed.

(** Source for [measurable_zero_extension]: supporting measurable cutoff in
    Federer 2.4.10, p. 85 The distinguished zero formulation also covers the
    real step functions used in the proof. *)
Lemma measurable_zero_extension (R : realType) (X : choiceType) (Y : topologicalType)
    (mu : set X -> \bar R) (hm : is_measure mu) (zero : Y)
    (A : set X) (f : partial_function X Y) :
  measure_measurable mu A -> is_measure_measurable_function mu f ->
  is_measure_measurable_function mu (partial_function_zero_extension zero A f).
Proof.
move=> hA hf; constructor.
- exact (@zero_extension_conull_domain R X Y mu hm zero A f (measurable_function_domain hf)).
- move=> U hU; rewrite partial_zero_extension_preimage.
  apply: (@measure_measurable_union R X mu hm).
  + exact (@measure_measurable_intersection R X mu hm A _ hA (measurable_function_open_preimage hf hU)).
  + have [hz|hz] := pselect (U zero).
    * have he : [set x | ~ A x /\ U zero] = ~` A by apply/seteqP; split=> x; [move=> []|move=> hx; split].
      rewrite he; exact: measure_measurable_complement hA.
    * have he : [set x | ~ A x /\ U zero] = set0.
        apply/seteqP; split=> x; last by move=> [].
        by move=> [_ hx]; exact: hz hx.
      rewrite he; exact: measure_measurable_empty hm.
Qed.
