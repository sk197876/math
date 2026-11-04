(** Federer (1969), 3.2.46, p. 282, extending 3.2.12, pp. 249–250: null
    changes of the original partial integrand preserve the
    iterated fibre integral. The null-fibre theorem supplies
    the necessary inner almost equalities. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import RiemannianTensorUP RiemannianMetricCarrier RiemannianHausdorff
  RiemannianPathLipschitz RiemannianCoareaFibreIntegral RiemannianCoareaNullFibres MappingMultiplicity
  PartialFunctionUP PartialZeroExtension MeasureUP MeasureAlmostUP MeasureAlmostBasic
  MeasureIntegralUP ParameterizedIntegralAlmostEquality ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [riemannian_coarea_fibre_integral_null_change]: the
    partial-domain reduction for 3.2.46, p. 282, in the approximation proof of
    Federer 3.2.12, p. 250. Original undefined
    points may remain in exceptional fibres, but they have
    zero inner Hausdorff mass for almost every target point. *)
Theorem riemannian_coarea_fibre_integral_null_change (R:realType) m n A B g h
    (hg : @is_continuous_riemannian_tensor R m A g)
    (hh : @is_continuous_riemannian_tensor R n B h)
    (f : riemannian_metric_space hg -> riemannian_metric_space hh)
    (hpSource : (0<=m%:R :> R)%R) (hpTarget : (0<=n%:R :> R)%R)
    (hpFibre : (0<=(m-n)%:R :> R)%R)
    (u v : partial_function (riemannian_metric_space hg) (extended_real_line R)) a :
  (n<=m)%N -> is_riemannian_path_lipschitz f ->
  measure_almost_equal (riemannian_hausdorff_measure hg m%:R hpSource) u v ->
  is_measure_integral (riemannian_hausdorff_measure hh n%:R hpTarget)
    (riemannian_coarea_fibre_integral f hpFibre u) a ->
  is_measure_integral (riemannian_hausdorff_measure hh n%:R hpTarget)
    (riemannian_coarea_fibre_integral f hpFibre v) a.
Proof.
move=>hnm hf hEqual hI.
pose X:=[the choiceType of riemannian_metric_space hg].
pose Y:=[the choiceType of riemannian_metric_space hh].
pose alpha:=riemannian_hausdorff_measure hh n%:R hpTarget.
pose ha:=@riemannian_hausdorff_is_measure R n B h hh n%:R hpTarget.
pose beta:=riemannian_hausdorff_measure hg (m-n)%:R hpFibre.
pose hb:=@riemannian_hausdorff_is_measure R m A g hg (m-n)%:R hpFibre.
pose N:=~`partial_function_agreement u v.
have hNull:riemannian_hausdorff_measure hg m%:R hpSource N=0:=hEqual.
have hFibre:=@riemannian_coarea_null_source_fibres R m n A B g h hg hh f
  hpSource hpTarget hpFibre hnm hf N hNull.
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
