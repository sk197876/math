(** Federer (1969), 2.6.5, p. 120, final sentence: the zero set of a nonzero
    polynomial has Lebesgue measure zero, proved by induction and Fubini.
    This file supplies the one-variable finiteness step using the project's
    own synthetic-division root-count proof from 1.10.4, p. 46. they do not
    state this measure-zero claim. No external polynomial root-counting
    theorem is imported. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp
  classical_sets cardinality reals constructive_ereal.
From Federer Require Import PolynomialCoefficientUniqueness MeasureUP PositiveClosedSubsets.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [coefficient_polynomial_finitely_many_roots]:
    supporting base case for Federer 2.6.5, p. 120,
    from the local root-count proof supporting 1.10.4, p. 46.
    Nonzero means that at least one coefficient is nonzero;
    the statement even permits vector-valued coefficients over
    any field. *)
Lemma coefficient_polynomial_finitely_many_roots (K : fieldType) (W : lmodType K)
    (s : seq W) :
  ~~ all (pred1 0) s -> finite_set [set x : K | coefficient_polynomial_value s x = 0].
Proof.
move=> hn; apply: contrapT=> hi.
have [F hF hsize] := infinite_set_fset (size s) hi.
have hz := @coefficient_polynomial_roots K W (#|` F|) s (F : seq K)
  hsize (erefl _) (fset_uniq F) (fun x hx => hF x hx).
by rewrite hz in hn.
Qed.

(** Source for [coefficient_polynomial_root_set_null]: the
    one-variable measure-zero step used in Federer 2.6.5,
    p. 120. A finite set of roots is null whenever all
    scalar singletons are null, without any extra measurability
    assumption on the function or its coefficients. *)
Lemma coefficient_polynomial_root_set_null (R : realType) (W : lmodType R)
    (mu : set R -> \bar R) (hm : is_measure mu) (s : seq W) :
  (forall x, mu [set x] = 0%:E) -> ~~ all (pred1 0) s ->
  mu [set x : R | coefficient_polynomial_value s x = 0] = 0%:E.
Proof.
move=> hx hn.
apply: (countable_null_singletons_null hm).
- exact: finite_set_countable (coefficient_polynomial_finitely_many_roots hn).
- by move=> x _; exact: hx.
Qed.
