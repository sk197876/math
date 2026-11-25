(** Federer (1969), 3.2.21, p. 257: the
    differential of a Lipschitz Euclidean map has rank less
    than mu almost everywhere above a purely mu-unrectifiable
    Borel target. No upper bound on mu is assumed. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct InnerNorm InnerMetric
  NormDifferentialUP EuclideanLebesgueDimensions LipschitzUP RectifiableSetUP HausdorffMeasure
  TopologicalBorel MeasureUP MeasureBasic MeasureAlmostUP MeasureAlmostBasic
  LinearRankUP LinearRankAtLeast Rademacher PureUnrectifiableRankLocusNull.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [pure_unrectifiable_bad_rank_null]: the null
    exceptional set in Federer 3.2.21, p. 257, for
    arbitrary source and target dimensions. If mu exceeds the
    source dimension, finite-dimensional rank bounds make the
    locus empty. Otherwise the orthogonal slice proof applies.
    Erratum p. 5 corrects the final slice mass to L^mu(B). *)
Lemma pure_unrectifiable_bad_rank_null (R:realType) m n mu
    (v:inner_metric_space (@euclidean_inner_productP R m)->
      inner_metric_space (@euclidean_inner_productP R n))
    (T:set (inner_metric_space (@euclidean_inner_productP R n))):
  is_metric_lipschitz setT v ->borel_set T ->
  is_purely_measure_m_unrectifiable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) mu) mu T ->
  @euclidean_lebesgue_measure R m [set x|T (v x) /\ exists D,
    has_norm_differential (inner_norm (@euclidean_inner_productP R m))
      (inner_norm (@euclidean_inner_productP R n)) setT v x D /\
    linear_rank_at_least D mu]=0%E.
Proof.
move=>hLip hT hPure; have [hDim|hDim]:=leqP mu m.
- move:(@pure_unrectifiable_rank_locus_null R (m-mu) mu n).
  rewrite (subnK hDim)=>h; exact:(h v T hLip hT hPure).
- apply:(measure_null_subset (euclidean_lebesgue_is_measure R m) _
    (measure_empty (euclidean_lebesgue_is_measure R m)))=>x [_ [D [_ hRank]]].
  have [r [hr _]]:=linear_rank_exists D (@coordinate_basisP R n).
  have hLower:=(linear_rank_at_leastP mu hr).1 hRank.
  have hUpper:=linear_rank_domain_bound (@coordinate_basisP R m) hr.
  have hFalse:=leq_ltn_trans (leq_trans hLower hUpper) hDim.
  by rewrite ltnn in hFalse.
Qed.

(** Source for [federer_3_2_21]: the complete lemma,
    Federer 3.2.21, p. 257. For L^m almost all
    x in v inverse T, an actual differential exists and
    its image has dimension strictly less than the positive
    integer mu. Rademacher supplies actual differentiability;
    no derivative field or extra rank, mass or dimension
    hypothesis is assumed. The orthogonal slicing proof uses
    L^mu(B), as corrected by erratum p. 5, book p. 257 line 26. *)
Theorem federer_3_2_21 (R:realType) m n mu
    (v:inner_metric_space (@euclidean_inner_productP R m)->
      inner_metric_space (@euclidean_inner_productP R n))
    (T:set (inner_metric_space (@euclidean_inner_productP R n))):
  (0<mu)%N ->is_metric_lipschitz setT v ->borel_set T ->
  is_purely_measure_m_unrectifiable (@hausdorff_measure R
    (inner_metric_space (@euclidean_inner_productP R n)) mu) mu T ->
  measure_almost_everywhere_on (@euclidean_lebesgue_measure R m) (v @^-1` T)
    [set x|exists D r,
      has_norm_differential (inner_norm (@euclidean_inner_productP R m))
        (inner_norm (@euclidean_inner_productP R n)) setT v x D /\
      has_linear_rank D r /\ (r<mu)%N].
Proof.
move=>hMu hLip hT hPure.
pose hm:=euclidean_lebesgue_is_measure R m.
pose Bad:= [set x:R_n R m|T (v x) /\ exists D,
  has_norm_differential (inner_norm (@euclidean_inner_productP R m))
    (inner_norm (@euclidean_inner_productP R n)) setT v x D /\ linear_rank_at_least D mu].
have hNull:@euclidean_lebesgue_measure R m Bad=0%E:=
  pure_unrectifiable_bad_rank_null hLip hT hPure.
have hGood:measure_almost_everywhere (@euclidean_lebesgue_measure R m) (~` Bad).
  by rewrite /measure_almost_everywhere setCK.
have hBoth:=measure_almost_everywhere_and hm (federer_3_1_6 hLip) hGood.
apply:(measure_almost_everywhere_on_implication _ _ _).2.
apply:(measure_almost_everywhere_mono hm _ hBoth)=>x [[D hD] hNot] hTx.
have [r [hr _]]:=linear_rank_exists D (@coordinate_basisP R n).
exists D,r; split; first exact hD; split; first exact hr.
rewrite ltnNge; apply/negP=>hAtLeast.
apply:hNot; split; first exact hTx; exists D; split; first exact hD.
exact:(linear_rank_at_leastP mu hr).2 hAtLeast.
Qed.
