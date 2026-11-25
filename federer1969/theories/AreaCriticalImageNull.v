(** Federer (1969), 3.2.3, p. 244: let epsilon
    tend to zero in the finite-measure critical image
    estimate. The Jacobian measure of every critical set
    is zero by its exact vanishing graph. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology lra.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric LipschitzUP
  ExtendedRealOrderTopology ExtendedScaledErrorBound EuclideanLebesgueDimensions
  MeasureUP MeasureBasic MeasureAlmostUP MeasureAlmostBasic MeasureIntegralUP MeasureIntegralBounds
  MeasureIntegralUniqueness MeasureSubsetIntegral MeasureConullZeroIntegral
  PartialFunctionUP PartialZeroExtension EuclideanJacobianMeasurable EuclideanJacobianRank
  JacobianDensityMeasure MeasureDensityUP TopologicalBorel HausdorffMeasure AreaCriticalGraphBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [finite_borel_critical_image_null]: the
    conclusion H^m[f(A)]=0 in the second case of
    Federer 3.2.3, p. 244. Finite L^m(A)
    makes the epsilon coefficient finite. *)
Theorem finite_borel_critical_image_null (R:realType) m n
    (f:inner_metric_space (@euclidean_inner_productP R m)->
      inner_metric_space (@euclidean_inner_productP R n)) (A:set (R_n R m)) M:
  is_metric_lipschitz_bound setT f M ->
  @borel_set [the topologicalType of inner_metric_space (@euclidean_inner_productP R m)] A ->
  A `<=` singular_differential_locus f -> euclidean_lebesgue_measure m A< +oo ->
  @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m (f @` A)=0.
Proof.
move=>hM hA hCritical hFinite.
pose mu:=@euclidean_lebesgue_measure R m.
pose beta:=@hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m.
have hMassPos:0<=mu A:=measure_nonnegative (euclidean_lebesgue_is_measure R m) A.
have hFin:mu A \is a fin_num by rewrite ge0_fin_numE //.
pose a:=fine (mu A).
have hMass:mu A=a%:E by rewrite /a fineK.
have ha:(0<=a)%R by move:hMassPos; rewrite hMass lee_fin.
rewrite /mu in hMass.
pose C:=((M+1)^+m.-1*a)%R.
have hM1:(0<=M+1)%R:=addr_ge0 hM.1 ler01.
have hC:(0<=C)%R:=mulr_ge0 (exprn_ge0 m.-1 hM1) ha.
have hError (r:R):(0<r)%R -> beta (f @` A)<=(0+C*r)%R%:E.
  move=>hr; pose e:=Num.min r (1/2)%R.
  have he:(0<e)%R by rewrite /e lt_min hr; nra.
  have her:(e<=r)%R by rewrite /e ge_min lexx.
  have heHalf:(e<=1/2)%R by rewrite /e ge_min lexx orbT.
  have he1:(e<=1)%R by nra.
  have hMe:(0<=M+e)%R:=addr_ge0 hM.1 (ltW he).
  have hPow:((M+e)^+m.-1<=(M+1)^+m.-1)%R.
    exact (lerXn2r m.-1 hMe hM1 (lerD (lexx M) he1)).
  have hGraph:=critical_set_graph_image_bound hM hA hCritical he.
  rewrite hMass -EFinM in hGraph.
  refine (le_trans hGraph _); rewrite lee_fin add0r.
  have hh:=ler_wpM2r ha (ler_wpM2l (ltW he) hPow).
  apply:le_trans hh _; rewrite -mulrA (mulrC C r).
  exact (ler_wpM2r hC her).
have hz:beta (f @` A)<=0.
  exact (@extended_upper_bound_from_scaled_errors R (beta (f @` A)) 0%R C hC hError).
by apply/eqP; rewrite eq_le hz (measure_nonnegative (@hausdorff_measure_is_measure R _ m)).
Qed.

(** Source for [critical_jacobian_measure_zero]: the zero
    left-hand integral in the singular case of Federer
    3.2.3, pp. 243–244. Every actual Jacobian
    value on A is zero, so the exact zero extension
    has integral zero without a finite-mass hypothesis. *)
Lemma critical_jacobian_measure_zero (R:realType) m n
    (f:R_n R m->R_n R n) (A:set (R_n R m)):
  A `<=` singular_differential_locus f -> euclidean_jacobian_measure f A=0.
Proof.
move=>hA.
pose mu:=@euclidean_lebesgue_measure R m.
pose hm:=euclidean_lebesgue_is_measure R m.
pose u:=extended_euclidean_jacobian f.
pose cut:=partial_function_zero_extension (0:extended_real_line R) A u.
have hZero x:partial_function_graph cut x 0.
  case:(pselect (A x))=>hx.
  - apply:(@partial_function_zero_extension_on _ (extended_real_line R) 0 A u x 0 hx).2.
    exists 0%R; split; last by [].
    exact ((singular_differential_locus_jacobian f x).1 (hA x hx)).
  - exact ((@partial_function_zero_extension_off _ (extended_real_line R) 0 A u x 0 hx).2 (erefl _)).
have hIntegral:is_measure_integral mu cut 0.
  apply:(measure_almost_zero_integral hm).
  apply:(@measure_almost_everywhere_mono R _ mu hm setT _ _ (measure_almost_everywhere_true hm))=>x _.
  exact (hZero x).
have hLaw:=euclidean_jacobian_measure_laws f.
rewrite (hLaw A) /measure_subset_upper_integral.
exact (measure_upper_integral_unique (measure_upper_integral_specification mu cut) hIntegral.2.1).
Qed.
