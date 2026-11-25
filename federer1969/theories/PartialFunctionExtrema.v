(** Federer (1969), 2.3.2, p. 74: consequences of the abstract pointwise
    extremum laws, including the empty-family conventions inherited from
    2.1.1, p. 51. Source context: PartialFunctionSupremumUP.v and
    PartialFunctionInfimumUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import PartialFunctionUP ExtendedRealOrderTopology PartialFunctionSupremumUP
  PartialFunctionInfimumUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [partial_supremum_value_unique]: supporting
    uniqueness of the value prescribed by the supremum in Federer
    2.3.2, p. 74, from the order laws of 2.1.1, p. 51. *)
Lemma partial_supremum_value_unique (R : realType) (X J : Type) (D : set J)
    (f : J -> partial_function X (extended_real_line R))
    (g h : partial_function X (extended_real_line R)) :
  is_partial_function_supremum D f g -> is_partial_function_supremum D f h ->
  forall x y z, partial_function_graph g x y -> partial_function_graph h x z -> y = z.
Proof.
move=> hg hh x y z hy hz; apply/eqP; rewrite eq_le; apply/andP; split.
- apply: (@partial_function_supremum_least R X J D f g hg x y hy z).
  exact: (@partial_function_supremum_upper R X J D f h hh x z hz).
- apply: (@partial_function_supremum_least R X J D f h hh x z hz y).
  exact: (@partial_function_supremum_upper R X J D f g hg x y hy).
Qed.

(** Source for [partial_infimum_value_unique]: supporting
    uniqueness of the infimum value in Federer 2.3.2, p. 74,
    from the greatest-lower-bound laws of 2.1.1, p. 51. *)
Lemma partial_infimum_value_unique (R : realType) (X J : Type) (D : set J)
    (f : J -> partial_function X (extended_real_line R))
    (g h : partial_function X (extended_real_line R)) :
  is_partial_function_infimum D f g -> is_partial_function_infimum D f h ->
  forall x y z, partial_function_graph g x y -> partial_function_graph h x z -> y = z.
Proof.
move=> hg hh x y z hy hz; apply/eqP; rewrite eq_le; apply/andP; split.
- apply: (@partial_function_infimum_greatest R X J D f h hh x z hz y).
  exact: (@partial_function_infimum_lower R X J D f g hg x y hy).
- apply: (@partial_function_infimum_greatest R X J D f g hg x y hy z).
  exact: (@partial_function_infimum_lower R X J D f h hh x z hz).
Qed.

(** Source for [partial_supremum_empty_graph]: supporting empty-
    family convention in Federer 2.3.2, p. 74: the common
    domain is all of X and the supremum is minus infinity by
    2.1.1, p. 51. *)
Lemma partial_supremum_empty_graph (R : realType) (X J : Type)
    (f : J -> partial_function X (extended_real_line R))
    (g : partial_function X (extended_real_line R)) :
  is_partial_function_supremum set0 f g -> forall x, partial_function_graph g x -oo.
Proof.
move=> hg x.
have hx : partial_function_domain g x.
  rewrite (partial_function_supremum_domain hg); by move=> j [].
have [y hy] := hx.
have he : y = -oo.
  apply/eqP; rewrite eq_le leNye andbT.
  apply: (@partial_function_supremum_least R X J set0 f g hg x y hy -oo).
  by move=> z [j [[] _]].
by rewrite he in hy.
Qed.

(** Source for [partial_infimum_empty_graph]: supporting empty-
    family convention in Federer 2.3.2, p. 74: the common
    domain is all of X and the infimum is plus infinity by
    2.1.1, p. 51. *)
Lemma partial_infimum_empty_graph (R : realType) (X J : Type)
    (f : J -> partial_function X (extended_real_line R))
    (g : partial_function X (extended_real_line R)) :
  is_partial_function_infimum set0 f g -> forall x, partial_function_graph g x +oo.
Proof.
move=> hg x.
have hx : partial_function_domain g x.
  rewrite (partial_function_infimum_domain hg); by move=> j [].
have [y hy] := hx.
have he : y = +oo.
  apply/eqP; rewrite eq_le leey /=.
  apply: (@partial_function_infimum_greatest R X J set0 f g hg x y hy +oo).
  by move=> z [j [[] _]].
by rewrite he in hy.
Qed.
