(** Federer (1969), 3.4.1 and 3.4.3, pp. 310,
    316–317: the announced degree satisfies the original upper
    nullity property. Sharpness remains a separate 3.4.4 obligation. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerNorm HilbertFormCompactness
  RealNormUP NormMetric NormDifferentialUP NormRegularity LinearRankUP CriticalValueLoci
  CriticalValueProblem CriticalRankDegreeComparison.
From Federer Require Export CriticalValueUpperTheorem.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [critical_value_upper_degree]: the upper
    half of the answer announced in 3.4.1, p. 310,
    proved by 3.4.3, pp. 316–317. The original
    rank locus supplies exactly the theorem's actual-differential
    premise. The least-degree property still requires 3.4.4. *)
Theorem critical_value_upper_degree (R:realType) m nu k
    (hp:0<=(nu%:R+(m-nu)%:R/k%:R:R)):
  (nu<m)%N ->(1<=k)%N ->@critical_value_nullity_degree R m nu k (nu%:R+(m-nu)%:R/k%:R) hp.
Proof.
move=>hNu hk Y NY hNY A f hOpen hf.
rewrite critical_value_imageE.
have hBA:critical_rank_locus NY A f nu `<=` A:=
  @critical_rank_locus_subset R m Y NY A f nu.
have hRank x (hx:critical_rank_locus NY A f nu x):
    exists D:Hom (R_n R m) Y,
      has_norm_differential (inner_norm (@euclidean_inner_productP R m)) NY A f x D /\
      exists r,has_linear_rank D r /\(r<=nu)%N.
  have [_ h]:=(critical_rank_locusP NY A f nu x).1 hx;exact:h.
exact:(@federer_3_4_3 R m nu k Y NY hNY A (critical_rank_locus NY A f nu) f hp
  hNu hk hOpen hBA hf hRank).
Qed.
