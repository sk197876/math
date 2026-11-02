(** Federer (1969), 3.2.33, p. 270: outside
    f inverse(Y), the original fibre has zero complementary
    Hausdorff measure, using exactly the Y of 3.2.32. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric PartialFunctionUP
  PartialFunctionBasic PartialFunctionSourceRestriction RectifiablePositiveFibreCoareaUP
  HausdorffMeasure MeasureUP MeasureBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.

(** Source for [restricted_positive_fibre_complement_null]:
    the original-domain fibre outside f inverse(Y) in
    Federer 3.2.33, p. 270. Nonnegativity and
    failure of strict positivity force zero mass, including
    zero-dimensional and infinite-mass alternatives. The
    exact original partial preimage is retained. *)
Lemma restricted_positive_fibre_complement_null (R:realType) n v m mu
    (W:set (R_n R n)) (F:R_n R n->R_n R v) x:
  W x ->
  let f:=partial_function_source_restrict W (partial_function_total F) in
  ~partial_function_preimage f (positive_partial_fibre_locus m mu f) x ->
  @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) (m-mu)
    [set z|W z /\F z=F x]=0%E.
Proof.
move=>hx f hNot.
pose H:=@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) (m-mu).
pose hH:=@hausdorff_measure_is_measure R (inner_metric_space (@euclidean_inner_productP R n)) (m-mu).
have hFibre:partial_function_preimage f [set F x]=[set z|W z /\F z=F x].
  apply/seteqP; split=>z.
  - move=>[y [[hz hFy] hy]]; split; first exact hz.
    exact:(eq_trans hFy hy).
  - move=>[hz hEq]; exists (F x); split; last reflexivity; by split.
have hNoPositive:~(0<H [set z|W z /\F z=F x])%E.
  move=>hp; apply:hNot; exists (F x); split; first by split.
  change (is_true ((0<H (partial_function_preimage f [set F x]))%E)).
  by rewrite hFibre.
apply/eqP; rewrite eq_le (measure_nonnegative hH) andbT leNgt.
by apply/negP.
Qed.
