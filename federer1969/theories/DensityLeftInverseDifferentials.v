(** Federer (1969), 3.2.8, p. 247: the
    chain differential equals the identity at
    density-one points of the left-inverse set.
    Reuse the first-order density uniqueness argument
    already proved for 3.1.24, p. 240. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import Hom TensorUP GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerNorm InnerMetric
  HilbertFormCompactness RealNormUP PartialFunctionUP EuclideanLebesgueDimensions CenteredBallRelations MeasureSetDensity
  NormDifferentialUP NormDifferentialLinear NormDifferentialLocal NormDifferentialChain NormDifferentialSubtraction
  NormDifferentialZeroOnDensitySet.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [density_left_inverse_differential_identity]:
    the last paragraph of the proof of
    Federer 3.2.8, p. 247. Ordinary
    differentiation and density-one agreement with identity
    determine the composed linear map. Dimension zero
    is proved directly, preserving the project's
    punctured approximate-differential convention. *)
Theorem density_left_inverse_differential_identity (R:realType) m
    (u v:R_n R m->R_n R m) (C:set (R_n R m))
    a (L M:Hom (R_n R m) (R_n R m)):
  C a -> (forall x,C x -> v (u x)=x) ->
  partial_function_graph
    (measure_set_density (@euclidean_lebesgue_measure R m)
      (@centered_closed_ball_relation R
        [the metricType R of inner_metric_space (@euclidean_inner_productP R m)])
      (~` C)) a 0%E ->
  has_norm_differential (inner_norm (@euclidean_inner_productP R m))
    (inner_norm (@euclidean_inner_productP R m)) setT u a L ->
  has_norm_differential (inner_norm (@euclidean_inner_productP R m))
    (inner_norm (@euclidean_inner_productP R m)) setT v (u a) M ->
  hom_comp M L=hom_of_linear (linear_id (R_n R m)).
Proof.
case:m u v C a L M=>[|m] u v C a L M ha hEq hDensity hU hV.
- apply:hom_ext=>h; rewrite (coordinate_zero h) hom_compE !linear0 ?hom_of_linearE; exact:erefl.
- pose X:=R_n R m.+1.
  pose N:=inner_norm (@euclidean_inner_productP R m.+1).
  have hN:=inner_norm_real_norm (@euclidean_inner_productP R m.+1).
  have hChain:=norm_differential_chain hN hN hN hU hV.
  have hWhole:norm_domain_interior N setT a.
    exists 1; split; first exact:ltr01; by move=>h hh.
  have hComp:has_norm_differential N N setT (fun x=>v (u x)) a (hom_comp M L).
    exact (norm_differential_restrict (fun x _=>conj Logic.I Logic.I) hWhole hChain).
  have hIdBound:norm_bounded_linear N N (hom_of_linear (linear_id X)).
    exists 1; split; first exact:ler01.
    by move=>h; rewrite hom_of_linearE /= mul1r.
  have hId:=norm_differential_linear hN hN hWhole hIdBound.
  have hDiff:=norm_differential_subtract hN hN hComp hId.
  have hZero:(hom_comp M L-hom_of_linear (linear_id X))=0.
    apply:(@norm_differential_zero_on_density_set R m X N hN setT C
      (fun x=>v (u x)-hom_of_linear (linear_id X) x) a _ ha _ hDensity hDiff).
    move=>x hx; by rewrite (hEq x hx) hom_of_linearE /= subrr.
  move/eqP:hZero; by rewrite subr_eq0=>/eqP.
Qed.
