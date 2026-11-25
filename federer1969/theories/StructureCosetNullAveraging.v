(** Federer (1969), 3.3.4, pp. 289–290:
    zero measure on every actual subgroup
    coset forces zero original Haar measure.
    This supporting set-Fubini implication keeps
    the actual translated exceptional sets. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets reals constructive_ereal topology.
From Federer Require Import MeasureUP CountablyMeasurableUP ProductMeasure ProductSections
  ProductNullFubini HomogeneousMetricDensity StructureNullSectionProduct.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [structure_coset_null_average]: the
    Haar/Fubini zero-exception argument of
    Federer 3.3.4, pp. 289–290. All
    actual coset sections have zero inner
    mass; right-translation invariance identifies
    every horizontal mass with the original
    bad-set mass. Product Fubini and the
    positive inner total mass finish without
    selecting a global subgroup element. *)
Theorem structure_coset_null_average (R:realType) (X Y:choiceType)
    (mu:set X->\bar R) (nu:set Y->\bar R)
    (hMu:is_measure mu) (hNu:is_measure nu)
    (T:X->Y->X) (B:set X):
  (0<nu setT)%E ->
  measure_countably_measurable (product_measure hMu hNu)
    [set z:X*Y|B (T z.1 z.2)] ->
  (forall x,nu [set y|B (T x y)]=0%E) ->
  (forall y,mu [set x|B (T x y)]=mu B) ->mu B=0%E.
Proof.
move=>hPositive hMeasurable hCosets hInvariant.
pose S:set (X*Y):=[set z|B (T z.1 z.2)].
have hProduct:product_measure hMu hNu S=0%E.
  apply:structure_null_sections_product_null=>// x; exact:hCosets x.
have hAlmost:=@product_null_horizontal_sections R X Y mu nu hMu hNu S hProduct.
have [y hy]:=positive_measure_almost_truth_point hPositive hAlmost.
rewrite -(hInvariant y).
exact:hy.
Qed.
