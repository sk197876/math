(** Federer (1969), 2.4.14, p. 88: almost linear dependence of |f|^p sign f
    and |g|^q sign g. The specification includes the cases in which one
    function vanishes. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionUP PartialFunctionBasic
  SignedRealPower PartialSignedPower MeasureUP MeasureAlmostUP MeasureAlmostBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [is_almost_signed_power_dependent]: direct specification of
    the equality condition in Federer 2.4.14, p. 88 A single real
    coefficient and a single orientation are chosen for a conull set;
    neither varies with the point. *)
Definition is_almost_signed_power_dependent (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (p q : R)
    (f g : partial_function X (real_norm_metric_space (scalar_absolute_value_norm R))) :=
  exists c : R,
    measure_almost_everywhere mu (partial_signed_power_dependence_locus p q c f g) \/
    measure_almost_everywhere mu (partial_signed_power_dependence_locus q p c g f).

(** Source for [almost_signed_power_dependent_symmetry]: symmetry of the
    dependence condition in Federer 2.4.14, p. 88, immediate from the
    either-direction formulation. *)
Lemma almost_signed_power_dependent_symmetry (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (p q : R)
    (f g : partial_function X (real_norm_metric_space (scalar_absolute_value_norm R))) :
  is_almost_signed_power_dependent mu p q f g -> is_almost_signed_power_dependent mu q p g f.
Proof. move=> [c [hc|hc]]; exists c; [right|left]; exact hc. Qed.

(** Source for [almost_zero_signed_power_dependent]: the zero-function
    boundary of the equality condition in Federer 2.4.14, p. 88 The other
    factor needs only a conull domain. *)
Lemma almost_zero_signed_power_dependent (R : realType) (X : choiceType)
    (mu : set X -> \bar R) (hm : is_measure mu) (p q : R)
    (f g : partial_function X (real_norm_metric_space (scalar_absolute_value_norm R))) :
  measure_almost_equal mu f (partial_function_total (fun _ : X => (0%R : real_norm_metric_space (scalar_absolute_value_norm R)))) ->
  measure_almost_everywhere mu (partial_function_domain g) ->
  is_almost_signed_power_dependent mu p q f g.
Proof.
move=> hf hg; exists 0; left.
apply: (@measure_almost_everywhere_mono R X mu hm _ _ _
  (@measure_almost_everywhere_and R X mu hm _ _ hf hg)).
move=> x [[a [ha ha0]] [b hb]]; exists a,b; split=> //; split=> //.
have ha0' : 0%R=a := ha0.
by rewrite -ha0' signed_real_power_zero mul0r.
Qed.
