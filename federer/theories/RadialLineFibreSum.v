(** Federer (1969), 3.2.13, p. 250: the
    weighted area fibre sum for the one-dimensional
    norm map is the two-point sphere integral.
    Positive and negative radii are treated separately;
    the zero target is removed only by null invariance. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology lra.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  EuclideanOneCoordinate EuclideanRadialDifferential RadialLineSphere RadialSphereIntegral RadialPolarFirstHigh
  NumericalSumPair NumericalSum NumericalSumValues PartialFibreNumericalSum PartialFunctionUP
  PartialFunctionBasic PartialFunctionPrecomposition SummableRealFunctionUP ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [radial_line_fibre_set]: the level
    sets of the one-dimensional norm map, supporting
    the m=1 case of Federer 3.2.13, p. 250.
    The scalar identification is exact for every target. *)
Lemma radial_line_fibre_set (R:realType)
    (y:inner_metric_space (@euclidean_inner_productP R 1)):
  [set x:R_n R 1|euclidean_radial_norm x=y]=
    [set x:R_n R 1|inner_norm (@euclidean_inner_productP R 1) x=euclidean_one_project y].
Proof.
apply/seteqP; split=>x hx.
- have hh:=congr1 (@euclidean_one_project R) hx.
  by rewrite /euclidean_radial_norm euclidean_one_embedK in hh.
- exact (eq_trans (congr1 (@euclidean_one_embed R) hx) (euclidean_one_projectK y)).
Qed.

(** Source for [radial_line_fibre_sum_positive]: the
    actual finite weighted area sum on a positive
    sphere, Federer 3.2.13, p. 250. *)
Lemma radial_line_fibre_sum_positive (R:realType) (g:R_n R 1->R)
    (y:inner_metric_space (@euclidean_inner_productP R 1)):
  (0<euclidean_one_project y)%R ->
  partial_function_graph (partial_fibre_numerical_sum (@euclidean_radial_norm R 1)
    (real_total_integrand g)) y
    (g (euclidean_one_embed (euclidean_one_project y))+
      g (euclidean_one_embed (-euclidean_one_project y)%R))%R%:E.
Proof.
move=>hr; apply/partial_fibre_numerical_sum_graph.
exists (fun x=>(g x)%:E); split; first by move=>x _; apply/real_total_integrand_graph.
rewrite radial_line_fibre_set radial_line_sphere_pair //.
apply:numerical_sum_real_pair.
apply/eqP=>he; have hh:=congr1 (@euclidean_one_project R) he.
rewrite !euclidean_one_embedK in hh.
have hNe:(euclidean_one_project y!=0)%R:=lt0r_neq0 hr.
have hZero:euclidean_one_project y=0%R by lra.
by rewrite hZero eqxx in hNe.
Qed.

(** Source for [radial_line_fibre_sum_negative]: empty
    negative-radius fibres have numerical sum zero,
    supporting the one-dimensional polar integral in
    Federer 3.2.13, p. 250. *)
Lemma radial_line_fibre_sum_negative (R:realType) (g:R_n R 1->R)
    (y:inner_metric_space (@euclidean_inner_productP R 1)):
  (euclidean_one_project y<0)%R ->
  partial_function_graph (partial_fibre_numerical_sum (@euclidean_radial_norm R 1)
    (real_total_integrand g)) y 0.
Proof.
move=>hr; apply/partial_fibre_numerical_sum_graph.
exists (fun x=>(g x)%:E); split; first by move=>x _; apply/real_total_integrand_graph.
have hEmpty:[set x:R_n R 1|euclidean_radial_norm x=y]=set0.
  rewrite radial_line_fibre_set; apply/seteqP; split=>x; last by [].
  move=>hx; have hNorm:=inner_norm_nonnegative (@euclidean_inner_productP R 1) x.
  rewrite hx in hNorm; by move:hr; rewrite ltNge hNorm.
rewrite hEmpty; exact:numerical_sum_empty.
Qed.
