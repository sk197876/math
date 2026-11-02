(** Federer (1969), 2.1.1(11), p. 53: weighted iterated sums, explicitly
    with zero times infinity equal to zero. Source context: NumericalSum.v. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp
  classical_sets reals constructive_ereal.
From Federer Require Import ExtendedRealPartial ExtendedRealPartsScale
  NonnegativeSum NonnegativeSumSupport NonnegativeSumProduct NonnegativeSumScale NumericalSum.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [nonnegative_sum_weighted_product]: Federer
    2.1.1(11), p. 53, supporting case with nonnegative weights.
    The weights are finite real numbers and may vanish. *)
Lemma nonnegative_sum_weighted_product (R : realType) (I J : choiceType)
    (U : set I) (V : set J) (f : I * J -> \bar R) (g : I -> R) :
  (forall u, U u -> (0 <= g u)%R) ->
  (forall p, (U `*` V) p -> 0 <= f p) ->
  nonnegative_sum (U `*` V) (fun p => (g p.1)%:E * f p) =
    nonnegative_sum U (fun u => (g u)%:E * nonnegative_sum V (fun v => f (u,v))).
Proof.
move=> hg hf; rewrite nonnegative_sum_product_first.
- apply: nonnegative_sum_ext=> u hu /=; apply: nonnegative_sum_scale; first exact: hg.
  move=> v hv; apply: hf; by split.
- move=> [u v] [hu hv]; apply: mule_ge0.
  + rewrite lee_fin; exact: hg.
  + apply: hf; by split.
Qed.

(** Source for [numerical_sum_weighted_product]: Federer
    2.1.1(11), p. 53; the weighted product sum equals the
    weighted iterated sum, including simultaneous undefinedness.
    Multiplication here deliberately uses the special convention.
    No finiteness or definedness hypothesis on the total is added. *)
Theorem numerical_sum_weighted_product (R : realType) (I J : choiceType)
    (U : set I) (V : set J) (f : I * J -> \bar R) (g : I -> R) :
  (forall p, (U `*` V) p -> 0 <= f p) ->
  numerical_sum (U `*` V) (fun p => (g p.1)%:E * f p) =
    numerical_sum U (fun u => (g u)%:E * nonnegative_sum V (fun v => f (u,v))).
Proof.
move=> hf; rewrite /numerical_sum.
have hp : nonnegative_sum (U `*` V) (fun p => extended_positive_part ((g p.1)%:E*f p)) =
    nonnegative_sum U (fun u => extended_positive_part
      ((g u)%:E*nonnegative_sum V (fun v => f (u,v)))).
  transitivity (nonnegative_sum (U `*` V) (fun p => (Num.max (g p.1) 0)%:E*f p)).
  - apply: nonnegative_sum_ext=> p h; exact: extended_positive_nonnegative_product (hf p h).
  - rewrite (@nonnegative_sum_weighted_product R I J U V f (fun u => Num.max (g u) 0%R)) //.
    + apply: nonnegative_sum_ext=> u _; symmetry.
      apply: extended_positive_nonnegative_product; exact: nonnegative_sum_nonnegative.
    + by move=> u _; rewrite le_max lexx orbT.
have hn : nonnegative_sum (U `*` V) (fun p => extended_negative_part ((g p.1)%:E*f p)) =
    nonnegative_sum U (fun u => extended_negative_part
      ((g u)%:E*nonnegative_sum V (fun v => f (u,v)))).
  transitivity (nonnegative_sum (U `*` V) (fun p => (Num.max (-g p.1)%R 0)%:E*f p)).
  - apply: nonnegative_sum_ext=> p h; exact: extended_negative_nonnegative_product (hf p h).
  - rewrite (@nonnegative_sum_weighted_product R I J U V f (fun u => Num.max (-g u)%R 0%R)) //.
    + apply: nonnegative_sum_ext=> u _; symmetry.
      apply: extended_negative_nonnegative_product; exact: nonnegative_sum_nonnegative.
    + by move=> u _; rewrite le_max lexx orbT.
by rewrite hp hn.
Qed.
