(** Federer (1969), 2.5.10, p. 101: the representing density must have
    incompatible horizontal and vertical threshold sets. We spell out the
    characteristic-test inequalities implicit in the final geometric
    paragraph. The threshold may be any c strictly between zero and one.
    Source context and integral ingredients: RepresentingDensitySetBounds.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import EuclideanInnerProduct InnerMetric MeasureUP HausdorffLength
  PlaneProjectionMeasure PlaneProjectionFunctional PlaneProjectionCharacteristic
  CharacteristicFunctionUP CharacteristicFunctionSealed RepresentingDensitySetBounds
  TotalScalarLpUP RealLatticeDensityUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

Section ThresholdBounds.
Variable R : realType.
Local Notation X := [the metricType R of inner_metric_space (@euclidean_inner_productP R 2)].
Local Notation H := (@hausdorff_length R X).

(** Source for [plane_density_vertical_threshold_null]:
    supporting vertical test in Federer 2.5.10,
    p. 101. A finite H^1 measurable set with
    zero projected-counting measure cannot support a
    representing density bounded below by c>0 except
    on an H^1 null set. *)
Lemma plane_density_vertical_threshold_null (k : X -> R) E (c : R) :
  is_real_lattice_density H (total_scalar_lp H 1) (@plane_projection_functional R) k ->
  measure_measurable H E -> H E < +oo -> plane_projection_measure E=0 ->
  (0<c)%R -> (forall x, E x -> (c<=k x)%R) -> H E=0.
Proof.
move=> hk hE hf hz hc hck.
pose s := @CharacteristicFunction.value R X E; have hs := @CharacteristicFunction.laws R X E.
have hb := @representing_density_set_lower_bound R X H (@hausdorff_length_is_measure R X)
  (@plane_projection_functional R) k E s c hk hs hE hf hck.
rewrite (@plane_projection_characteristic_value R E s hs hE hf) hz in hb.
have hnon := @measure_nonnegative R X H (@hausdorff_length_is_measure R X) E.
have hfin : H E \is a fin_num by rewrite (ge0_fin_numE hnon).
rewrite -[H E](fineK hfin) -EFinM lee_fin in hb.
have he0 : (fine (H E)<=0)%R.
  have h : (c*fine (H E)<=c*0)%R by rewrite mulr0.
  by move: h; rewrite (ler_pM2l hc).
have hepos : (0<=fine (H E))%R by move: hnon; rewrite -(fineK hfin) lee_fin.
have he : fine (H E)=0%R by apply/eqP; rewrite eq_le he0 hepos.
by rewrite -(fineK hfin) he.
Qed.

(** Source for [plane_density_horizontal_threshold_null]:
    supporting horizontal test in Federer 2.5.10,
    p. 101. Where projected-counting measure equals
    finite H^1 measure, a representing density bounded
    above by c<1 forces that test set to be null. *)
Lemma plane_density_horizontal_threshold_null (k : X -> R) E (c : R) :
  is_real_lattice_density H (total_scalar_lp H 1) (@plane_projection_functional R) k ->
  measure_measurable H E -> H E < +oo -> plane_projection_measure E=H E ->
  (c<1)%R -> (forall x, E x -> (k x<=c)%R) -> H E=0.
Proof.
move=> hk hE hf hz hc hkc.
pose s := @CharacteristicFunction.value R X E; have hs := @CharacteristicFunction.laws R X E.
have hb := @representing_density_set_upper_bound R X H (@hausdorff_length_is_measure R X)
  (@plane_projection_functional R) k E s c hk hs hE hf hkc.
rewrite (@plane_projection_characteristic_value R E s hs hE hf) hz in hb.
have hnon := @measure_nonnegative R X H (@hausdorff_length_is_measure R X) E.
have hfin : H E \is a fin_num by rewrite (ge0_fin_numE hnon).
rewrite -[H E](fineK hfin) -EFinM lee_fin in hb.
have hepos : (0<=fine (H E))%R by move: hnon; rewrite -(fineK hfin) lee_fin.
have he : fine (H E)=0%R.
  case: (eqVneq (fine (H E)) 0%R)=> // hne.
  have hp : (0<fine (H E))%R by rewrite lt_neqAle eq_sym hne hepos.
  have hlt : (c*fine (H E)<fine (H E))%R by rewrite -{2}[fine (H E)]mul1r (ltr_pM2r hp).
  by move: hlt; rewrite ltNge hb.
by rewrite -(fineK hfin) he.
Qed.
End ThresholdBounds.
