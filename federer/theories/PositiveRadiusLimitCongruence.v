(** Supporting replacements and constant limits for Federer (1969), 2.10.19,
    p. 181. Changes at nonpositive radii therefore do not affect either
    density. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
From Federer Require Import ExtendedRealBounds PositiveRadiusLimits PositiveRadiusLimitBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [positive_radius_values_congr]: supporting replacement on the
    actual positive-radius domain in 2.10.19, p. 181 *)
Lemma positive_radius_values_congr (R : realType) (f g : R -> \bar R) :
  (forall r : R, (0<r)%R -> f r=g r) ->
  forall e, positive_radius_values f e=positive_radius_values g e.
Proof.
move=> h e; apply/seteqP; split=> [y [r [hr ->]]|y [r [hr ->]]]; exists r;
  split=> //; [exact: h r (andP hr).1|exact: esym (h r (andP hr).1)].
Qed.

(** Source for [positive_radius_limits_congr]: supporting
    unchanged upper and lower limits after a
    positive-radius replacement in 2.10.19, p. 181. *)
Lemma positive_radius_limits_congr (R : realType) (f g : R -> \bar R) :
  (forall r : R, (0<r)%R -> f r=g r) ->
  positive_radius_upper_limit f=positive_radius_upper_limit g /\
  positive_radius_lower_limit f=positive_radius_lower_limit g.
Proof.
move=> h; have he e := positive_radius_values_congr h e.
split; rewrite /positive_radius_upper_limit /positive_radius_lower_limit;
  congr (_ _); apply/seteqP; split=> [b [e [he' ->]]|b [e [he' ->]]];
  exists e; split=> //; by rewrite he.
Qed.

(** Source for [positive_radius_limits_constant]: supporting
    constant-radius special case of 2.10.19, p. 181,
    used to check zero measures and degree-zero point
    masses. Infinite constants are retained. *)
Lemma positive_radius_limits_constant (R : realType) (c : \bar R) :
  positive_radius_upper_limit (fun _ : R => c)=c /\
  positive_radius_lower_limit (fun _ : R => c)=c.
Proof.
have hu : positive_radius_upper_limit (fun _ : R => c)<=c.
  apply: (@positive_radius_upper_eventual_bound R (fun _ : R => c) c 1%R (@ltr01 R)).
  by move=> r hr.
have hl : c<=positive_radius_lower_limit (fun _ : R => c).
  apply: le_trans _ (@positive_radius_lower_ge_level R (fun _ : R => c) 1%R (@ltr01 R)).
  apply: extended_real_inf_greatest=> y [r [_ ->]]; exact: lexx.
have ho := @positive_radius_limits_ordered R (fun _ : R => c).
split; apply/eqP; rewrite eq_le; apply/andP; split=> //.
- exact: le_trans hl ho.
- exact: le_trans ho hu.
Qed.
