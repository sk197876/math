(** Federer (1969), 3.2.13, p. 250: the finite-coordinate
    Fubini identity used for the product of Gamma integrals.
    The empty product uses the existing unit mass convention. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal.
From Federer Require Import RealMetricBackground GrassmannAbbreviations EuclideanInnerProduct InnerMetric EuclideanOneCoordinate
  EuclideanLebesgueDimensions ScalarEuclideanApproximateLimits EuclideanLebesgueBoxes EuclideanBlockCoordinates EuclideanSeparatedIntegral
  LebesgueScalarMeasure PointMassIntegral PartialFunctionUP PartialFunctionPrecomposition
  MeasureUP MeasurePushforward MeasureIntegralUP MeasureIntegralGraphEquivalence
  SummableRealFunctionUP InjectivePushforwardIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_scalar_function_integral]: the scalar
    factor of Cartesian Fubini in Federer 3.2.13, p. 250,
    transported through the measure-preserving one-coordinate identification
    of 2.6.5, pp. 119–120. *)
Lemma euclidean_scalar_function_integral (R:realType) (f:R->R) (a:R):
  is_measure_integral (@lebesgue_scalar_measure R) (real_total_integrand f) a%:E ->
  is_measure_integral (@euclidean_lebesgue_measure R 1)
    (real_total_integrand (fun x=>f (euclidean_one_project x))) a%:E.
Proof.
move=>hi.
have hInj:injective (@euclidean_one_project R):=can_inj (@euclidean_one_projectK R).
have hPush:measure_pushforward (@euclidean_one_project R) (@euclidean_lebesgue_measure R 1)=
    @lebesgue_scalar_measure R.
  apply:funext=>A; exact:Logic.eq_sym (euclidean_one_project_measure_preimage A).
have hIff:=@injective_pushforward_integral_iff R
  [the choiceType of inner_metric_space (@euclidean_inner_productP R 1)] R
  (@euclidean_lebesgue_measure R 1) (euclidean_lebesgue_is_measure R 1)
  (@euclidean_one_project R) (real_total_integrand f) hInj a%:E.
rewrite hPush in hIff.
exact:(measure_integral_graph_equivalent (fun x z=>iff_refl _) (hIff.2 hi)).
Qed.

(** Source for [euclidean_finite_product_integral]: the finite
    Cartesian Fubini identity used to multiply Gamma integrals,
    Federer 3.2.13, p. 250. Every factor is an actual finite
    integral; no product-integrability premise is added. *)
Theorem euclidean_finite_product_integral (R:realType) m
    (f:'I_m->R->R) (a:'I_m->R):
  (forall j,is_measure_integral (@lebesgue_scalar_measure R) (real_total_integrand (f j)) (a j)%:E) ->
  is_measure_integral (@euclidean_lebesgue_measure R m)
    (real_total_integrand (fun x:R_n R m=>\prod_j f j (x j))) (\prod_j a j)%:E.
Proof.
elim:m f a=>[|m ih] f a hi.
- have h:=@point_mass_real_integral R [the choiceType of inner_metric_space (@euclidean_inner_productP R 0)]
    0 (fun x:R_n R 0=>\prod_j f j (x j)).
  by rewrite !big_ord0 in h *.
- move:f a hi; rewrite -addn1=>f a hi.
  have hL:=ih (fun j=>f (lshift 1 j)) (fun j=>a (lshift 1 j)) (fun j=>hi (lshift 1 j)).
  have hR:=euclidean_scalar_function_integral (hi (rshift m ord0)).
  have hProduct:=euclidean_separated_integral hL hR.
  have hValue:(\prod_j a j)=(\prod_j a (lshift 1 j))*a (rshift m ord0).
    by rewrite big_split_ord big_ord1.
  rewrite hValue.
  apply:(measure_integral_graph_equivalent _ hProduct)=>x z.
  rewrite !real_total_integrand_graph.
  have hFun:(\prod_j f j (x j))=
      (\prod_j f (lshift 1 j) ((euclidean_block_split x).1 j))*
      f (rshift m ord0) (euclidean_one_project (euclidean_block_split x).2).
    rewrite big_split_ord big_ord1; congr (_*_).
    + apply:eq_bigr=>j _; by rewrite /euclidean_block_split ffunE.
    + by rewrite /euclidean_one_project /euclidean_block_split ffunE.
  by rewrite -hFun.
Qed.
