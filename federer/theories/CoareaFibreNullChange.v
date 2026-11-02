(** Federer (1969), 3.2.12, pp. 249–250: null
    changes of the original partial integrand preserve the
    iterated fibre integral. The null-fibre theorem supplies
    the necessary inner almost equalities. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric EuclideanLebesgueDimensions
  CoareaFibreIntegral CoareaNullSourceAgreement HausdorffMeasure MappingMultiplicity LipschitzUP
  PartialFunctionUP PartialZeroExtension MeasureUP MeasureAlmostUP MeasureAlmostBasic
  MeasureIntegralUP ParameterizedIntegralAlmostEquality ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [coarea_fibre_integral_null_change]: the
    partial-domain reduction in the approximation proof of
    Federer 3.2.12, p. 250. Original undefined
    points may remain in exceptional fibres, but they have
    zero inner Hausdorff mass for almost every target point. *)
Theorem coarea_fibre_integral_null_change (R:realType) m n
    (f:inner_metric_space (@euclidean_inner_productP R m)->
      inner_metric_space (@euclidean_inner_productP R n))
    (u v:partial_function (R_n R m) (extended_real_line R)) a:
  (n<=m)%N ->is_metric_lipschitz setT f ->
  measure_almost_equal (@euclidean_lebesgue_measure R m) u v ->
  is_measure_integral (@euclidean_lebesgue_measure R n) (coarea_fibre_integral f u) a ->
  is_measure_integral (@euclidean_lebesgue_measure R n) (coarea_fibre_integral f v) a.
Proof.
move=>hnm hf hEqual hI.
pose X:=inner_metric_space (@euclidean_inner_productP R m).
pose Y:=inner_metric_space (@euclidean_inner_productP R n).
pose alpha:=@euclidean_lebesgue_measure R n.
pose ha:=euclidean_lebesgue_is_measure R n.
pose beta:=@hausdorff_measure R X (m-n).
pose hb:=@hausdorff_measure_is_measure R X (m-n).
pose N:=~`partial_function_agreement u v.
have hNull:euclidean_lebesgue_measure m N=0:=hEqual.
have hFibre:=coarea_null_source_fibres_zero hnm hf hNull.
apply:(parameterized_integral_almost_equal_family ha hb _ hI).
apply:(@measure_almost_everywhere_mono R [the choiceType of Y] alpha ha _ _ _ hFibre)=>y hy.
have hOff:measure_almost_everywhere beta (~`mapping_fibre f N y).
  by rewrite /measure_almost_everywhere setCK.
apply:(@measure_almost_everywhere_mono R [the choiceType of X] beta hb _ _ _ hOff)=>x hx.
case:(pselect (f x=y))=>hxy.
- have hAgree:partial_function_agreement u v x.
    apply:contrapT=>hn; exact (hx (conj hn hxy)).
  have [z [hu hv]]:=hAgree; exists z; split.
  + exact ((@partial_function_zero_extension_on _ _ 0 [set x|f x=y] u x z hxy).2 hu).
  + exact ((@partial_function_zero_extension_on _ _ 0 [set x|f x=y] v x z hxy).2 hv).
- exists 0; split.
  + exact ((@partial_function_zero_extension_off _ _ 0 [set x|f x=y] u x 0 hxy).2 (erefl _)).
  + exact ((@partial_function_zero_extension_off _ _ 0 [set x|f x=y] v x 0 hxy).2 (erefl _)).
Qed.
