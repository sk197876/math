(** Federer (1969), 2.6.4, p. 119, corrected final assertion:
    product-measure integrability of finite separated sums from K(X) tensor
    K(Y). This supports the representation formula replacing book p. 119
    line 19 in erratum p. 2. the compact product-functional assertion is not
    stated there. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets reals constructive_ereal topology.
From Federer Require Import CompactSupportFunctionUP CompactProductApproximationUP MeasureUP ProductMeasure
  SummableRealFunctionUP SummableRealFunctionLattice LatticeL1ApproximationLaws DaniellFiniteSums
  SeparatedProductIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [finite_compact_separated_sum_summable]: supporting
    finite-sum integrability for the corrected last assertion of
    Federer 2.6.4, p. 119, erratum p. 2. Only
    summability of the factor K-spaces is required here. *)
Lemma finite_compact_separated_sum_summable (R : realType) (X Y : topologicalType)
    (alpha : set X -> \bar R) (beta : set Y -> \bar R)
    (ha : is_measure alpha) (hb : is_measure beta) :
  (forall f, compactly_supported_continuous_functions f -> summable_real_functions alpha f) ->
  (forall g, compactly_supported_continuous_functions g -> summable_real_functions beta g) ->
  forall h, is_finite_compact_separated_sum h -> summable_real_functions (product_measure ha hb) h.
Proof.
move=> hX hY h [F [a [b [hab he]]]].
have hfun : h=(fun p => \sum_(j <- F) a j p.1*b j p.2) by apply: funext=> p; exact: he.
rewrite hfun; apply: (@function_lattice_sequence_sum R (X*Y)%type Y _
  (@summable_real_functions_lattice R (Choice.clone (X*Y)%type _) _ (product_measure_is_measure ha hb)) F _).
- exists 0; exact: real_total_zero_integral (product_measure_is_measure ha hb).
- move=> j hj; exact (@separated_product_summable R X Y alpha beta ha hb (a j) (b j)
    (@hX (a j) (hab j hj).1) (@hY (b j) (hab j hj).2)).
Qed.
