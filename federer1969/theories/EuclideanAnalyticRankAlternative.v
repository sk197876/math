(** Federer (1969), 3.2.33, p. 270: the analytic
    rank stratum on a connected open coordinate domain is
    either null or open and conull. Erratum p. 5,
    book p. 270 line 25, supplies the reference 3.1.24. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets
  constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  HilbertFormCompactness InnerNormTopologyAdapters RealNormUP NormDifferentialUP NormRegularity
  NormAnalyticUP NormAnalyticLocal NormAnalyticOperations NormClassZeroNonzeroLocus
  EuclideanHomOperator EuclideanAnalyticDifferentialField EuclideanExteriorGramRank
  EuclideanExteriorGramAnalytic EuclideanAnalyticRoots EuclideanLebesgueDimensions
  LinearRankUP MeasureUP MeasureBasic MeasureAlmostBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [euclidean_analytic_rank_stratum_alternative]: the
    rank-set alternative in Federer 3.2.33, p. 270,
    in actual Euclidean coordinates. Analyticity of both actual
    exterior Hilbert Gram functions and 3.1.24 prove it;
    no rank alternative is assumed. All natural dimensions,
    degree zero and empty domains are retained. *)
Theorem euclidean_analytic_rank_stratum_alternative (R:realType) m n mu
    (A:set (R_n R m)) (D:R_n R m->Hom (R_n R m) (R_n R n)):
  @connected (inner_metric_space (@euclidean_inner_productP R m)) A ->
  @norm_analytic R (R_n R m) (Hom (R_n R m) (R_n R n))
    (inner_norm (@euclidean_inner_productP R m)) (@euclidean_operator_norm R m n)
    (inner_norm_real_norm (@euclidean_inner_productP R m))
    (@euclidean_operator_norm_is_norm R m n) A D ->
  let S:=fun x=>A x /\has_linear_rank (D x) mu in
  euclidean_lebesgue_measure m S=0%E \/
  (@open (inner_metric_space (@euclidean_inner_productP R m)) S /\
    euclidean_lebesgue_measure m (A `\` S)=0%E).
Proof.
move=>hConnected hD S.
pose NX:=inner_norm (@euclidean_inner_productP R m).
pose hNX:=inner_norm_real_norm (@euclidean_inner_productP R m).
pose NS:=fun t:R^o=>`|t|.
pose hNS:=@scalar_absolute_value_norm R.
pose h q x:=euclidean_exterior_gram q (D x).
have hAnalytic q:@norm_analytic R (R_n R m) R^o NX NS hNX hNS A (h q).
  exact:(@norm_analytic_compose_on R (R_n R m) (Hom (R_n R m) (R_n R n)) R^o
    NX (@euclidean_operator_norm R m n) NS hNX (@euclidean_operator_norm_is_norm R m n)
    hNS A setT D (@euclidean_exterior_gram R m n q) (fun x hx=>Logic.I)
    hD (@euclidean_exterior_gram_analytic R m n q)).
have hRoots q:=@euclidean_analytic_roots R m R^o NS hNS A (h q)
  hConnected (hAnalytic q).
have hMass:=euclidean_lebesgue_is_measure R m.
case:(hRoots mu.+1)=>[hNext|hNextNull]; last first.
- left; apply:(measure_null_subset hMass _ hNextNull)=>x [hx hRank].
  split; first exact hx.
  exact:((euclidean_exterior_gram_exact_rank mu (D x)).1 hRank).2.
have hNextZero x (hx:A x):h mu.+1 x=0.
  have hxZero:=hx; rewrite -hNext in hxZero.
  exact hxZero.2.
case:(hRoots mu)=>[hLower|hLowerNull].
- left.
  have hEmpty:S=set0.
    apply/seteqP; split=>[x [hx hRank]|x []].
    have hxZero:=hx; rewrite -hLower in hxZero.
    have hp:=((euclidean_exterior_gram_exact_rank mu (D x)).1 hRank).1.
    change (is_true (0<h mu x)) in hp.
    by rewrite hxZero.2 ltxx in hp.
  by rewrite hEmpty (measure_empty hMass).
- right.
  have hS:S=(fun x=>A x /\h mu x!=0).
    apply/seteqP; split=>x [hx hxRank]; split=>//.
    + have hp:=((euclidean_exterior_gram_exact_rank mu (D x)).1 hxRank).1.
      change (is_true (0<h mu x)) in hp.
      by rewrite (gt_eqF hp).
    + apply:(euclidean_exterior_gram_exact_rank mu (D x)).2; split.
      * rewrite lt_def (euclidean_exterior_gram_nonnegative mu (D x)) andbT.
        exact hxRank.
      * exact:hNextZero.
  split.
  + rewrite hS; apply:(inner_norm_openP (@euclidean_inner_productP R m) _).2.
    exact:(@norm_class_zero_nonzero_locus_open R (R_n R m) R^o NX NS hNX hNS
      A (h mu) (norm_class_continuous (norm_analytic_class_all_orders (hAnalytic mu) 0%N))).
  + apply:(measure_null_subset hMass _ hLowerNull)=>x [hx hn].
    split=>//; apply/eqP; apply/negPn/negP=>hp.
    apply:hn; rewrite hS; by split.
Qed.

(** Source for [euclidean_analytic_map_rank_alternative]: the
    actual analytic differential used in the rank argument of
    Federer 3.2.33, p. 270, exists and satisfies the
    full rank-stratum alternative. Its analytic operator norm
    regularity is proved from the first jet, not supplied as
    an extra hypothesis on the original analytic map. *)
Theorem euclidean_analytic_map_rank_alternative (R:realType) m n mu
    (A:set (R_n R m)) (f:R_n R m->R_n R n):
  @connected (inner_metric_space (@euclidean_inner_productP R m)) A ->
  @norm_analytic R (R_n R m) (R_n R n)
    (inner_norm (@euclidean_inner_productP R m)) (inner_norm (@euclidean_inner_productP R n))
    (inner_norm_real_norm (@euclidean_inner_productP R m))
    (inner_norm_real_norm (@euclidean_inner_productP R n)) A f ->
  exists D:R_n R m->Hom (R_n R m) (R_n R n),
    (forall x,A x ->has_norm_differential (inner_norm (@euclidean_inner_productP R m))
      (inner_norm (@euclidean_inner_productP R n)) A f x (D x)) /\
    (euclidean_lebesgue_measure m (fun x=>A x /\has_linear_rank (D x) mu)=0%E \/
      (@open (inner_metric_space (@euclidean_inner_productP R m))
        (fun x=>A x /\has_linear_rank (D x) mu) /\
        euclidean_lebesgue_measure m
          (A `\` (fun x=>A x /\has_linear_rank (D x) mu))=0%E)).
Proof.
move=>hc hf; have [D [hD hAnalytic]]:=euclidean_analytic_differential_field_exists hf.
exists D; split; first exact hD.
exact:(euclidean_analytic_rank_stratum_alternative mu hc hAnalytic).
Qed.
