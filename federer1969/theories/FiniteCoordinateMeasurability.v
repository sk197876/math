(** Federer (1969), 4.1.7, p. 359:
    scalar coordinates prove measurability of
    the finite exterior image density.
    This supporting adapter uses the original
    basis expansion of 1.6.3, p. 25,
    and the measurable operations of 2.3.8,
    pp. 78–79. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions classical_sets reals constructive_ereal topology.
From Federer Require Import RealMetricBackground Hom RealNormUP NormMetric NormMetricScaleContinuity LinearBasis FiniteDualDimension
  Annihilator FiniteNormMetricPolish PartialFunctionBasic MeasureUP MeasurableFunctionUP
  MeasurableTotalBasic BorelFunctionBasic MeasurableNormedFunctionUP MeasurableNormedBasic
  MeasurableTotalNormedArithmetic SeparableTargetNormedMeasurability.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [finite_coordinate_field_measurable]:
    a field in a finite normed space
    is measurable when each original basis
    coordinate is measurable, supporting Federer
    4.1.7, p. 359. The zero-dimensional
    space is included. *)
Theorem finite_coordinate_field_measurable (R:realType) (X:choiceType)
    (V:lmodType R) (N:V->R) (hN:is_real_norm N)
    d (b:'I_d->V) (hb:is_basis b)
    (mu:set X->\bar R) (hm:is_measure mu) (f:X->V):
  (forall i,is_measure_measurable_function mu
    (partial_function_total (fun x=>((dual_basis hb i (f x):R):real_line_metric R))))->
  is_measure_measurable_function mu (partial_function_total (fun x=>(f x:real_norm_metric_space hN))).
Proof.
move=>hCoordinates.
have [C [hCount hDense]]:=@finite_norm_metric_separable R V N hN d b hb.
have hTerm i:is_measurable_normed_function mu
    (partial_function_total (fun x=>((dual_basis hb i (f x):R)*:b i:real_norm_metric_space hN))).
  apply:(@separable_target_measurable_normed R X V N hN C mu hm _ hCount hDense).
  exact:(@measurable_total_borel_postcomposition R X (real_line_metric R) (real_norm_metric_space hN)
    mu hm (fun x=>(dual_basis hb i (f x):R)) (fun c=>c*:b i) (hCoordinates i)
    (continuous_borel_function (@real_norm_metric_scalar_orbit_continuous R V N hN (b i)))).
have hSum (s:seq 'I_d):is_measurable_normed_function mu
    (partial_function_total (fun x=>(\sum_(i<-s) (dual_basis hb i (f x):R)*:b i:real_norm_metric_space hN))).
  elim:s=>[|i s ih].
  - have hZero:(fun x:X=>(\sum_(i<-([::]:seq 'I_d)) (dual_basis hb i (f x):R)*:b i:V))=
        (fun _:X=>(0:V)).
      apply:funext=>x;exact:big_nil.
    rewrite hZero;exact:(@measurable_normed_total_constant R X V N hN mu hm 0).
  - have hCons:(fun x:X=>(\sum_(j<-i::s) (dual_basis hb j (f x):R)*:b j:V))=
        (fun x=>(dual_basis hb i (f x):R)*:b i+\sum_(j<-s) (dual_basis hb j (f x):R)*:b j).
      apply:funext=>x;exact:big_cons.
    rewrite hCons;exact:(@measurable_normed_total_add R X V N hN mu hm _ _ (hTerm i) ih).
have hExpansion:(fun x=>(f x:real_norm_metric_space hN))=
    (fun x=>(\sum_i (dual_basis hb i (f x):R)*:b i:real_norm_metric_space hN)).
  apply:funext=>x;exact:(@basis_vector_expansion R V d b hb (f x)).
rewrite hExpansion;exact:(hSum (index_enum 'I_d)).1.
Qed.

(** Source for [finite_coordinate_field_bound]:
    bounds for the original finite coordinates
    give a finite norm bound, supporting
    local integrability in Federer 4.1.7,
    p. 359. This estimate does not replace
    the actual norm in the final measure. *)
Lemma finite_coordinate_field_bound (R:realType) (X:Type)
    (V:lmodType R) (N:V->R) (hN:is_real_norm N)
    d (b:'I_d->V) (hb:is_basis b) (f:X->V) (K:set X)
    (M:'I_d->R):
  (forall i,0<=M i)->
  (forall i x,K x->`|(dual_basis hb i (f x):R)|<=M i)->
  forall x,K x->N (f x)<=\sum_i M i*N (b i).
Proof.
move=>hM hBound x hx.
rewrite {1}(@basis_vector_expansion R V d b hb (f x)).
apply:le_trans (real_seminorm_sum hN.1 _) _.
apply:ler_sum=>i _;rewrite (real_seminorm_scale hN.1).
exact:(ler_wpM2r (real_seminorm_nonnegative hN.1 (b i)) (hBound i x hx)).
Qed.
