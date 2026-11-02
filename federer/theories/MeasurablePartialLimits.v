(** Federer (1969), 2.3.2(6), pp. 73–74: the full partial-domain limit
    theorem. Total extensions are used only as intermediate witnesses; the
    conclusion and convergence premise retain the original graphs. *)
From mathcomp Require Import all_boot boolp classical_sets reals constructive_ereal topology.
From Federer Require Import PartialFunctionUP PartialFunctionBasic PartialFunctionLimitUP
  PartialFunctionExtensionUP PartialFunctionExtensionSealed MeasureUP MeasureAlmostUP
  MeasureAlmostBasic MeasureAlmostEquality MeasurableFunctionUP MeasurableFunctionBasic
  MeasurableAlmostModification MeasurableTotalExtension MeasurableTotalLimits.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [partial_limit_locus_domain]: supporting definedness
    of the limit in Federer 2.3.2(6), p. 73, convergence
    display. The limit graph is defined wherever the convergence
    assertion with its specified value holds. *)
Lemma partial_limit_locus_domain (X : Type) (Y : topologicalType)
    (f : nat -> partial_function X Y) (g : partial_function X Y) :
  partial_function_limit_locus f g `<=` partial_function_domain g.
Proof. move=> x [u [z [_ [hz _]]]]; by exists z. Qed.

(** Source for [measurable_partial_functions_almost_limit]: direct Federer
    2.3.2(6), pp. 73–74 Neither separability nor an inhabited target nor a
    positive measure hypothesis is imposed. *)
Theorem measurable_partial_functions_almost_limit (R : realType)
    (X : choiceType) (Y : metricType R) (mu : set X -> \bar R)
    (hm : is_measure mu) (f : nat -> partial_function X Y) (g : partial_function X Y) :
  (forall n, is_measure_measurable_function mu (f n)) ->
  measure_almost_everywhere mu (partial_function_limit_locus f g) ->
  is_measure_measurable_function mu g.
Proof.
move=> hf hl.
have hd : measure_almost_everywhere mu (partial_function_domain g).
  exact (@measure_almost_everywhere_mono R X mu hm _ _
    (@partial_limit_locus_domain X Y f g) hl).
case: (pselect (exists y : Y, True))=> [[y0 _]|hn].
- pose F n := @PartialFunctionExtension.value X Y (f n) y0.
  pose G := @PartialFunctionExtension.value X Y g y0.
  have hF n : is_partial_function_total_extension (f n) (F n).
    exact: PartialFunctionExtension.laws.
  have hG : is_partial_function_total_extension g G.
    exact: PartialFunctionExtension.laws.
  have ha : measure_almost_equal mu g (partial_function_total G).
    exact: (@partial_function_total_extension_almost_equal R X Y mu g G hd hG).
  have hFm n : is_measure_measurable_function mu (partial_function_total (F n)).
    apply: (@measurable_function_almost_equal R X Y mu hm (f n) _ (hf n)).
    exact: (@partial_function_total_extension_almost_equal R X Y mu (f n) (F n)
      (measurable_function_domain (hf n)) (hF n)).
  have hGm : is_measure_measurable_function mu (partial_function_total G).
    apply: (@measurable_total_functions_almost_limit R X Y mu hm F G
      (partial_function_limit_locus f g) hFm hl).
    move=> x [u [z [hu [hz hc]]]].
    have he : (fun n => F n x) = u.
      apply: functional_extensionality_dep=> n; exact: (hF n x (u n) (hu n)).
    have hg : G x = z := hG x z hz.
    by rewrite he hg.
  exact: (@measurable_function_almost_equal R X Y mu hm _ g hGm
    (@measure_almost_equal_sym R X Y mu _ _ ha)).
- apply: (@null_whole_space_measurable_function R X Y mu hm g).
  apply: (proj1 (@measure_almost_everywhere_false R X mu)).
  apply: (@measure_almost_everywhere_mono R X mu hm _ set0 _ hl).
  move=> x [u [z _]]; exfalso; apply: hn; by exists z.
Qed.
