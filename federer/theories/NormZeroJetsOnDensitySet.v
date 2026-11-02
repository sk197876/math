(** Federer (1969), 3.1.24, p. 240: successive
    approximate differentiation makes every jet vanish on a
    density-one subset of the zero set. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerNormInequalities HilbertFormCompactness InnerMetric
  RealNormUP EuclideanLebesgueDimensions CenteredBallRelations PartialFunctionUP MeasureSetDensity
  NormDifferentialUP ContinuousMultilinearUP ContinuousMultilinearNorm ContinuousMultilinearZero
  MultilinearSuccessorArguments NormHigherDifferentialUP NormHigherDifferentialFields
  NormDifferentialZeroOnDensitySet.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [norm_zero_jets_on_density_set]: the inclusion
    Z contained in W in Federer 3.1.24, p. 240.
    On a subset S of the zero set which has density one
    at every one of its own points, all actual higher
    differential fields vanish. The proof inducts on the
    recursive differential graph; the first-order density lemma
    applies to arbitrary normed multilinear target spaces. *)
Theorem norm_zero_jets_on_density_set (R:realType) n
    (Y:lmodType R) (NY:Y->R) (hNY:is_real_norm NY)
    (Z:nat->lmodType R)
    (ev:forall i,{ffun 'I_i->R_n R n.+1}->Hom (Z i) Y)
    (ZN:forall i,Z i->R)
    (hZ:forall i,is_continuous_multilinear_space
      (inner_norm (@euclidean_inner_productP R n.+1)) NY (@ev i) (@ZN i))
    (A S:set (R_n R n.+1)) (f:R_n R n.+1->Y) (D:forall i,R_n R n.+1->Z i) :
  (forall x,S x -> A x) -> (forall x,S x -> f x=0) ->
  (forall x,S x -> partial_function_graph
    (measure_set_density (@euclidean_lebesgue_measure R n.+1)
      (@centered_closed_ball_relation R
        [the metricType R of inner_metric_space (@euclidean_inner_productP R n.+1)])
      (~` S)) x 0%E) ->
  (forall i x,A x -> has_norm_higher_differential
    (inner_norm (@euclidean_inner_productP R n.+1)) ev ZN A f i x (D i x)) ->
  forall i x,S x -> D i x=0.
Proof.
move=>hSA hzero hden hD.
pose NX:=inner_norm (@euclidean_inner_productP R n.+1).
have hNX:=inner_norm_real_norm (@euclidean_inner_productP R n.+1).
elim=>[|i ih] x hx.
- apply: (continuous_multilinear_zero_injective (@hZ 0%N)).
  rewrite linear0; exact (eq_trans ((hD 0%N x (hSA x hx)).2) (hzero x hx)).
- have [L [hL hLe]]:=@norm_higher_differential_field_step_elim R (R_n R n.+1) Y NX hNX
    Z ev ZN A f i (D i) x (D i.+1 x) (hD i) (hD i.+1 x (hSA x hx)).
  have hN:=continuous_multilinear_norm_is_norm hNY (hZ i).
  have hL0:=@norm_differential_zero_on_density_set R n (Z i) (@ZN i) hN A S (D i) x L
    hx ih (hden x hx) hL.
  apply: (continuous_multilinear_extensional (hZ i.+1))=>u.
  have [v [t ->]]:=multilinear_successor_arguments_surjective u.
  rewrite -hLe hL0 hom_zeroE !linear0; reflexivity.
Qed.
