(** Federer (1969), 2.9.24, p. 169: the left-tagged Stieltjes sums of g
    against f converge to integral g df, so the corresponding step integral
    values converge to the boundary products minus that integral. This uses
    2.5.17, pp. 110–111. The local Federer erratum has no entry for this
    limit. *)
From mathcomp Require Import all_boot all_order all_algebra reals
  constructive_ereal topology ring.
From Federer Require Import RealMetricBackground CurveArcLength StieltjesSums StieltjesIntegral
  ExtendedRealOrderLimit RealErrorOrderLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [uniform_stieltjes_sum_error]: supporting sequential
    form of the Stieltjes-sum limit used in Federer 2.9.24,
    p. 169. The integrator f has locally finite variation,
    while only the integrand g is assumed continuous. *)
Lemma uniform_stieltjes_sum_error (R : realType) (f g : R -> R) (a b : R) :
  curve_locally_finite_variation (f : R -> real_line_metric R) ->
  continuous (g : real_line_metric R -> real_line_metric R) -> a<=b ->
  forall e : R, 0<e -> exists N : nat, forall n : nat, (N<=n)%N ->
    `|stieltjes_sum g f (uniform_partition a b n)-stieltjes_integral f g a b|<e.
Proof.
move=> hf hg hab e he.
have [d [hd hlim]] := @stieltjes_integral_limit R f hf g a b e hg hab he.
have [N hN] := @uniform_mesh_small R a b d hab hd.
exists N=> n hn.
exact: hlim _ (uniform_partition_is n hab) (uniform_partition_mesh (hN n hn)).
Qed.

(** Source for [right_step_integral_values_limit]: direct limiting
    right-hand side of the finite identity in Federer 2.9.24,
    p. 169. Its limit is f(b)g(b)-f(a)g(a)-integral g df. *)
Lemma right_step_integral_values_limit (R : realType) (f g : R -> R) (a b : R) :
  curve_locally_finite_variation (f : R -> real_line_metric R) ->
  continuous (g : real_line_metric R -> real_line_metric R) -> a<=b ->
  extended_order_limit
    (fun n => (f b*g b-f a*g a-stieltjes_sum g f (uniform_partition a b n))%:E)
    (f b*g b-f a*g a-stieltjes_integral f g a b)%:E.
Proof.
move=> hf hg hab; apply: real_error_extended_order_limit=> e he.
have [N hN] := @uniform_stieltjes_sum_error R f g a b hf hg hab e he.
exists N=> n hn.
have heq : f b*g b-f a*g a-stieltjes_sum g f (uniform_partition a b n)-
    (f b*g b-f a*g a-stieltjes_integral f g a b)=
    stieltjes_integral f g a b-stieltjes_sum g f (uniform_partition a b n) by ring.
by rewrite heq distrC; exact: hN n hn.
Qed.
