(** Federer (1969), 3.2.5, p. 245: changing
    a weight on a Hausdorff-null target set changes the
    source only on a null positive-Jacobian preimage.
    Points outside that rank locus have zero actual Jacobian. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerMetric EuclideanLebesgueDimensions
  LipschitzUP MeasureUP MeasureAlmostBasic HausdorffMeasure BorelAreaSelection
  InjectiveDifferentialPieceUP InjectiveDifferentialCover EuclideanLipschitzClassZero InjectivePieceNullPreimage.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [positive_jacobian_null_preimage]: the null-set
    reduction used for alternatives (1) and (2) in Federer
    3.2.5, p. 245. No target measurability premise
    is needed for a null set. *)
Theorem positive_jacobian_null_preimage (R:realType) m n
    (f:inner_metric_space (@euclidean_inner_productP R m)->
      inner_metric_space (@euclidean_inner_productP R n)) N:
  is_metric_lipschitz setT f ->
  @hausdorff_measure R (inner_metric_space (@euclidean_inner_productP R n)) m N=0 ->
  euclidean_lebesgue_measure m
    (positive_euclidean_jacobian_locus f `&` (f @^-1` N))=0.
Proof.
move=>hLip hN.
have [G hG]:=injective_differential_borel_cover_exists
  (euclidean_lipschitz_norm_class_zero hLip) (ltr1n R 2).
have hEq:positive_euclidean_jacobian_locus f `&` (f @^-1` N)=
    \bigcup_(E in G) (E `&` (f @^-1` N)).
  rewrite positive_jacobian_injective_locus -hG.2.1.
  apply/seteqP; split=>x.
  - move=>[[E hE hx] hNx]; exists E=>//; by split.
  - move=>[E hE [hx hNx]]; split=>//; by exists E.
rewrite hEq; apply:(measure_null_countable_union (euclidean_lebesgue_is_measure R m) hG.1)=>E hE.
exact (injective_differential_piece_null_preimage (hG.2.2 E hE) hN).
Qed.
