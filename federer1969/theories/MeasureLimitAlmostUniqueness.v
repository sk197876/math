(** Federer (1969), 2.3.9, pp. 79–80: the almost-everywhere limit is
    determined up to almost equality. This supporting uniqueness permits the
    arbitrary almost-everywhere representative. Source context:
    PartialFunctionPointwiseLimitUP.v. *)
From mathcomp Require Import all_boot boolp classical_sets reals constructive_ereal topology.
From Federer Require Import PartialFunctionUP PartialFunctionLimitUP MeasureUP MeasureAlmostUP MeasureAlmostBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [partial_metric_limits_almost_equal]: supporting
    uniqueness of the almost-everywhere limit in Federer 2.3.9,
    pp. 79–80; no measurability or completeness is needed
    when both limits already exist. *)
Lemma partial_metric_limits_almost_equal (R : realType) (X : choiceType) (Y : metricType R)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (f : nat -> partial_function X Y) (g h : partial_function X Y) :
  measure_almost_everywhere mu (partial_function_limit_locus f g) ->
  measure_almost_everywhere mu (partial_function_limit_locus f h) ->
  measure_almost_equal mu g h.
Proof.
move=> hg hh.
apply: (@measure_almost_everywhere_mono R X mu hm _ _ _
  (@measure_almost_everywhere_and R X mu hm _ _ hg hh)).
move=> x [[u [y [hu [hy hlimy]]]] [v [z [hv [hz hlimz]]]]].
have he : u=v by apply: functional_extensionality_dep=> n; exact: partial_function_single_valued (hu n) (hv n).
rewrite -he in hlimz.
have PF0 : ProperFilter (\oo : set_system nat) by typeclasses eauto.
have PF : ProperFilter (u @ \oo) := @fmap_proper_filter nat Y u \oo PF0.
have eyz := @cvg_unique Y (@metric_hausdorff R Y) (u @ \oo) PF y z hlimy hlimz.
exists y; split=> //; by rewrite eyz.
Qed.
