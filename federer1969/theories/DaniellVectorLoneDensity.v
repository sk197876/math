(** Federer (1969), 2.5.12, printed pp. 105–106: approximation in integral
    norm by finite sums h_i y_i. We combine the finite-image approximation
    from 2.4.12, p. 87, with the scalar lattice density from 2.5.3, p. 94.
    This proves the approximation globally for L1 functions, replacing the
    printed finite-support step followed by truncation. No completeness of E
    is required. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets
  reals constructive_ereal topology.
From Federer Require Import RealNormUP NormMetric PartialFunctionBasic
  PartialNormedArithmetic MeasureUP MeasureIntegralUP SummableRealFunctionUP
  MeasurableNormedFunctionUP MeasurableNormedDifference
  FunctionLatticeUP FunctionLatticeRegularityUP RealIntegralFunctionalUP
  MeasureLpNorm MeasureLpMembershipUP MeasureLpConvergence ExtendedRealOrderLimit
  VectorDaniellRationalSpan DenseFiniteLpApproximation SeparableVectorLone
  VectorLoneApproximation DaniellVectorFiniteDensity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [daniell_vector_lone_density]: the density of
    finite sums h_i y_i used to prove G = Q in Federer
    2.5.12, pp. 105–106. This stronger intermediate
    statement applies to every total L1 function with separable
    target, not just members of Q. *)
Theorem daniell_vector_lone_density (R : realType) (X : choiceType)
    (E : lmodType R) (N : E -> R) (hN : is_real_norm N)
    (phi : set X -> \bar R) (hphi : is_measure phi)
    (L : set (X -> R)) (F : (X -> R) -> R)
    (hL : is_function_lattice L)
    (hF : is_real_integral_functional phi (positive_function_lattice L) F)
    (hreg : is_function_lattice_regular (positive_function_lattice L) phi)
    (D : set E) (hD : is_rational_dense_subspace hN D)
    (G : set (X -> E))
    (hG0 : G (fun _ => 0))
    (hGadd : forall u v, G u -> G v -> G (fun x => u x+v x))
    (hGA : forall u, G u -> is_measurable_normed_function phi
      (partial_function_total (u : X -> real_norm_metric_space hN)))
    (hGelem : forall f y, positive_function_lattice L f -> D y ->
      G (fun x => f x *: y))
    (f : X -> real_norm_metric_space hN) :
  is_measure_lp_function phi 1 (partial_function_total f) ->
  is_vector_lone_approximable N phi G f.
Proof.
move=> hf e he.
have he2 : 0 < e/2 by rewrite divr_gt0 // ltr0n.
have [g [hg [hfin [hDg hlim]]]] :=
  @dense_finite_lp_approximation R X E N hN D hD phi hphi 1 f hf.
have he2E : (0 < (e/2)%:E)%E by rewrite lte_fin.
have [m hm] := hlim.2 _ he2E.
have hsmall := hm m (leqnn m).
have hsub := @measurable_normed_function_subtract R X E N hN phi hphi
  (partial_function_total f) (partial_function_total (g m)) hf.2.1 (hg m).2.1.
have hd0 := @measure_lp_norm_nonnegative R X E N hN phi 1 _ hphi (lexx _) hsub.1.
pose d := measure_lp_distance phi N 1 (partial_function_total f) (partial_function_total (g m)).
have hdfin : d \is a fin_num.
  rewrite (ge0_fin_numE hd0); exact: lt_trans hsmall (ltry _).
have hi : is_measure_integral phi (real_total_integrand (fun x => N (f x-g m x)))
    (fine d)%:E.
  rewrite fineK //; exact (@total_vector_lone_distance_integral R X E N hN phi hphi
    f (g m) hf.2.1 (hg m).2.1).
have ha : fine d < e/2.
  have hdlt : (d < (e/2)%:E)%E := hsmall.
  by rewrite -(fineK hdfin) lte_fin in hdlt.
have hga := @daniell_vector_finite_image_density R X E N hN phi hphi L F
  hL hF hreg D G hG0 hGadd hGA hGelem (g m) (hg m) (hfin m) (hDg m).
have [v [b [hv [hj hb]]]] := hga _ he2.
have [c [hc hcb]] := @vector_norm_error_transfer_integral R X E N hN phi hphi
  f (g m) v (fine d) b hf.2.1 (hGA v hv) hi hj.
exists v,c; split=> //; split=> //.
have hab := ltrD ha hb; rewrite -splitr in hab; exact: le_lt_trans hcb hab.
Qed.
