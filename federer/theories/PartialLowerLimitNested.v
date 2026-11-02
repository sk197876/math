(** Federer (1969), 2.3.2, p. 74: lower limit as supremum of tail infima. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import PartialFunctionUP ExtendedRealOrderTopology PartialFunctionSupremumUP
  PartialFunctionInfimumUP PartialFunctionLimitExtremaUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [partial_lower_limit_nested_value]: direct
    supremum-of-tail-infima formula of Federer 2.3.2, p. 74.
    Starting tail n at n instead of strictly after n does not
    change the family of eventual lower bounds. *)
Lemma partial_lower_limit_nested_value (R : realType) (X : Type)
    (f s : nat -> partial_function X (extended_real_line R))
    (g h : partial_function X (extended_real_line R)) :
  (forall n, is_partial_function_infimum [set i | (n <= i)%N] f (s n)) ->
  is_partial_function_supremum setT s h -> is_partial_function_lower_limit f g ->
  forall x, partial_function_common_domain setT f x ->
  forall y z, partial_function_graph g x y -> partial_function_graph h x z -> y = z.
Proof.
move=> hs hh hg x hx y z hy hz; apply/eqP; rewrite eq_le; apply/andP; split.
- apply: (@partial_function_lower_limit_least R X f g hg x y hy z).
  move=> b [n hn].
  have hsd : partial_function_domain (s n) x.
    rewrite (partial_function_infimum_domain (hs n)); move=> i hi; exact: hx i Logic.I.
  have [c hc] := hsd.
  apply: le_trans _ (@partial_function_supremum_upper R X nat setT s h hh x z hz c _).
  + apply: (@partial_function_infimum_greatest R X nat _ f (s n) (hs n) x c hc b).
    move=> w [i [hi hw]]; exact: hn i hi w hw.
  + by exists n.
- apply: (@partial_function_supremum_least R X nat setT s h hh x z hz y).
  move=> b [n [_ hnb]].
  apply: (@partial_function_lower_limit_upper R X f g hg x y hy b).
  exists n=> i hi w hw.
  apply: (@partial_function_infimum_lower R X nat _ f (s n) (hs n) x b hnb w).
  by exists i.
Qed.

(** Source for [partial_lower_limit_nested_agreement]: supporting
    common-domain agreement for lower-limit measurability in Federer 2.3.2,
    p. 74 *)
Lemma partial_lower_limit_nested_agreement (R : realType) (X : Type)
    (f s : nat -> partial_function X (extended_real_line R))
    (g h : partial_function X (extended_real_line R)) :
  (forall n, is_partial_function_infimum [set i | (n <= i)%N] f (s n)) ->
  is_partial_function_supremum setT s h -> is_partial_function_lower_limit f g ->
  partial_function_common_domain setT f `<=` partial_function_agreement h g.
Proof.
move=> hs hh hg x hx.
have hgd : partial_function_domain g x.
  rewrite (partial_function_lower_limit_domain hg); exists 0%N=> n hn; exact: hx n Logic.I.
have hhd : partial_function_domain h x.
  rewrite (partial_function_supremum_domain hh)=> n _.
  rewrite (partial_function_infimum_domain (hs n))=> i hi; exact: hx i Logic.I.
have [y hy] := hgd; have [z hz] := hhd.
have he := @partial_lower_limit_nested_value R X f s g h hs hh hg x hx y z hy hz.
exists z; split=> //; by rewrite -he.
Qed.
