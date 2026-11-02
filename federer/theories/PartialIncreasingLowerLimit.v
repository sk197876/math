(** Federer (1969), 2.4.7, p. 84: the pointwise limit of an increasing
    numerical sequence. We state convergence in the order-interval form
    already used by the project's scalar limit interface. Exact graph values
    and the common domain remain explicit. Source context:
    ExtendedIncreasingLowerLimit.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import ExtendedRealOrderTopology ExtendedRealBoundsUP ExtendedRealOrderLimit
  PartialFunctionUP PartialFunctionLimitExtremaUP PartialExtendedOrderLoci
  ExtendedLowerLimitUP ExtendedIncreasingLowerLimit.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [partial_extended_increasing_limit_locus]: supporting
    explicit graph formulation of the pointwise increasing limit
    in Federer 2.4.7, p. 84. *)
Definition partial_extended_increasing_limit_locus (R : realType) (X : Type)
    (f : nat -> partial_function X (extended_real_line R))
    (g : partial_function X (extended_real_line R)) :=
  [set x | exists (u : nat -> \bar R) z,
    (forall n, partial_function_graph (f n) x (u n)) /\
    partial_function_graph g x z /\ extended_increases_to u z].

(** Source for [partial_lower_limit_scalar_values]: supporting
    agreement of the scalar and partial-function lower-limit laws
    used in Federer 2.4.7, p. 84. *)
Lemma partial_lower_limit_scalar_values (R : realType) (X : Type)
    (f : nat -> partial_function X (extended_real_line R))
    (g : partial_function X (extended_real_line R)) x (u : nat -> \bar R) z :
  is_partial_function_lower_limit f g ->
  (forall n, partial_function_graph (f n) x (u n)) -> partial_function_graph g x z ->
  is_extended_lower_limit u z.
Proof.
move=> hg hu hz; constructor.
- move=> b [N hN]; apply: (@partial_function_lower_limit_upper R X f g hg x z hz b).
  exists N=> n hn y hy.
  have he := partial_function_single_valued (hu n) hy; rewrite -he; exact: hN n hn.
- move=> b hb; apply: (@partial_function_lower_limit_least R X f g hg x z hz b)=> c [N hN].
  apply: hb; exists N=> n hn; exact: hN n hn (u n) (hu n).
Qed.

(** Source for [partial_increasing_sequence_lower_limit]: the
    pointwise increasing sequence in Federer 2.4.7, p. 84,
    converges to its abstract lower-limit value and every term
    is bounded above by that value. *)
Lemma partial_increasing_sequence_lower_limit (R : realType) (X : Type)
    (f : nat -> partial_function X (extended_real_line R))
    (g : partial_function X (extended_real_line R)) x :
  is_partial_function_lower_limit f g ->
  (forall n, partial_extended_le_locus (f n) (f n.+1) x) ->
  partial_extended_increasing_limit_locus f g x /\
  forall n, partial_extended_le_locus (f n) g x.
Proof.
move=> hg hx.
have hd n : partial_function_domain (f n) x.
  have [a [b [ha _]]] := hx n; by exists a.
pose u n := projT1 (cid (hd n)).
have hu n : partial_function_graph (f n) x (u n) := projT2 (cid (hd n)).
have hs n : u n <= u n.+1.
  have [a [b [ha [hb hab]]]] := hx n.
  have ea := partial_function_single_valued (hu n) ha.
  have eb := partial_function_single_valued (hu n.+1) hb.
  by rewrite ea eb.
have hm : forall n m, (n <= m)%N -> u n <= u m.
  exact (@homo_leq (\bar R) u (fun v w => is_true (v <= w))
    (fun v => lexx v) (fun w v z hvw hwz => le_trans hvw hwz) hs).
have hgd : partial_function_domain g x.
  rewrite (partial_function_lower_limit_domain hg); exists 0%N=> n _; exact: hd.
have [z hz] := hgd.
have hl := @partial_lower_limit_scalar_values R X f g x u z hg hu hz.
have hsup := increasing_lower_limit_supremum hm hl.
split.
- exists u,z; split=> //; split=> //; exact: extended_increasing_lower_limit hm hl.
- move=> n; exists (u n),z; split=> //; split=> //.
  apply: (extended_real_supremum_upper hsup); by exists n.
Qed.
