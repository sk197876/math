(** Federer (1969), 2.3.2, p. 73, second paragraph: changing a function on a
    null exceptional set does not affect measurability. These supporting
    lemmas use completeness from 2.1.3(6), p. 55. *)
From mathcomp Require Import all_boot all_algebra boolp classical_sets
  reals constructive_ereal topology.
From Federer Require Import MeasureUP MeasureFiniteClosure MeasureAlmostUP
  MeasureAlmostBasic MeasureAlmostEquality PartialFunctionUP MeasurableFunctionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [measurable_set_null_modification]: supporting
    null-modification argument in Federer 2.3.2, p. 73, second
    paragraph, using measurable null sets from 2.1.3(6), p. 55.
    Agreement is required only outside the specified null set N. *)
Lemma measurable_set_null_modification (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (A B N : set X) :
  mu N = 0 -> (forall x, ~ N x -> (A x <-> B x)) ->
  measure_measurable mu A -> measure_measurable mu B.
Proof.
move=> hn hab ha.
have hN := @measure_null_measurable R X mu hm N hn.
have hBN : mu (B `&` N) = 0.
  apply: (@measure_null_subset R X mu hm _ N)=> // x [_ hx]; exact hx.
have he : B = (A `\` N) `|` (B `&` N).
  apply/seteqP; split=> x.
  - move=> hb; case: (pselect (N x))=> hx; last first.
    + left; split=> //; exact: (proj2 (hab x hx) hb).
    + by right; split.
  - move=> [[ha' hn']|[hb _]]=> //; exact: (proj1 (hab x hn') ha').
rewrite he; apply: (@measure_measurable_union R X mu hm).
- exact: (@measure_measurable_difference R X mu hm _ _ ha hN).
- exact: (@measure_null_measurable R X mu hm _ hBN).
Qed.

(** Source for [almost_equal_preimage_measurable]: supporting
    invariance of inverse-image measurability under almost equality
    in Federer 2.3.2, p. 73, second paragraph. Single-valued
    graphs ensure identical inverse images at points of agreement. *)
Lemma almost_equal_preimage_measurable (R : realType) (X : choiceType)
    (Y : Type) (mu : set X -> \bar R) (hm : is_measure mu)
    (f g : partial_function X Y) (A : set Y) :
  measure_almost_equal mu f g ->
  measure_measurable mu (partial_function_preimage f A) ->
  measure_measurable mu (partial_function_preimage g A).
Proof.
move=> he hf; apply: (@measurable_set_null_modification R X mu hm
  _ _ (~` partial_function_agreement f g) he _ hf).
move=> x hnn; have [y [hfy hgy]] : partial_function_agreement f g x.
  by apply: contrapT=> hn; exact: hnn.
split=> [[z [hz ha]]|[z [hz ha]]]; exists z; split=> //.
- have ez : y = z := partial_function_single_valued hfy hz.
  by rewrite -ez.
- have ez : y = z := partial_function_single_valued hgy hz.
  by rewrite -ez.
Qed.

(** Source for [measurable_function_almost_equal]: supporting
    precise form of the null-modification remark in Federer 2.3.2,
    p. 73, second paragraph. It applies to partial functions
    without assuming an inhabited target or positive total measure. *)
Theorem measurable_function_almost_equal (R : realType) (X : choiceType)
    (Y : topologicalType) (mu : set X -> \bar R) (hm : is_measure mu)
    (f g : partial_function X Y) :
  is_measure_measurable_function mu f -> measure_almost_equal mu f g ->
  is_measure_measurable_function mu g.
Proof.
move=> hf he; constructor.
- exact (@measure_almost_equal_domain_left R X Y mu hm g f
    (@measure_almost_equal_sym R X Y mu f g he)).
- move=> U ho; exact (@almost_equal_preimage_measurable R X Y mu hm f g U he
    (measurable_function_open_preimage hf ho)).
Qed.
