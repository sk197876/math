(** Federer (1969), 3.4.1 and 3.4.4, pp. 310,
    317–318: the announced critical-value degree is the least possible. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals constructive_ereal topology lra.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates EuclideanInnerProduct
  InnerNorm HilbertFormCompactness RealNormUP NormMetric NormDifferentialUP NormOpenDomainLaws
  NormRegularity LinearRankUP CriticalValueLoci CriticalValueProblem CriticalValueDegree
  CriticalValueDegreeSealed CriticalValueUpper CriticalValueSharpness CriticalImageDegreeLaws
  RealHausdorffMeasure MeasureUP MeasureAlmostBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [critical_value_least_degree]: the least-number
    claim announced in 3.4.1, p. 310, now proved
    by 3.4.3 and 3.4.4, pp. 316–318.
    A proposed smaller nonnegative universal degree would make
    the actual sharpness example null also at its larger
    positive image degree. This contradicts the proved original
    product mass. Degree zero is retained in this argument. *)
Theorem critical_value_least_degree (R:realType) m nu k
    (hp:(0<=(nu%:R+(m-nu)%:R/k%:R:R))%R):
  (nu<m)%N ->(1<=k)%N ->
  @is_least_critical_value_degree R m nu k (nu%:R+(m-nu)%:R/k%:R)%R hp.
Proof.
move=>hNu hK;constructor.
- exact:(@critical_value_upper_degree R m nu k hp hNu hK).
- move=>t ht hUniversal.
  pose s:R:=(nu%:R+(m-nu)%:R/k%:R)%R.
  case hCompare: ((s<=t)%R);first by [].
  exfalso.
  have hLess:(t<s)%R by rewrite ltNge hCompare.
  have hS:(0<s)%R:=le_lt_trans ht hLess.
  pose gamma:=((t+s)/2)%R.
  have hGamma:(0<gamma)%R by rewrite /gamma;lra.
  have hGammaUpper:(gamma<s)%R by rewrite /gamma;lra.
  have hTGamma:(t<gamma)%R by rewrite /gamma;lra.
  have [sigma [hSigma [B [F [hGammaSigma [hClass [hRank hPositive]]]]]]]:=
    @federer_3_4_4 R m nu k gamma hNu hK hGamma hGammaUpper.
  pose X:=R_n R m.
  pose N:=inner_norm (@euclidean_inner_productP R m).
  pose hN:=inner_norm_real_norm (@euclidean_inner_productP R m).
  pose M:=[the metricType R of real_norm_metric_space hN].
  have hOpen a (ha:True):norm_domain_interior N (fun _=>True) a.
    exact:norm_full_domain_interior.
  have hOriginalNull:=@hUniversal X N hN (fun _=>True) F hOpen hClass.
  have hSubset:F @` B `<=` critical_value_image N (fun _=>True) F nu.
    move=>y [x hx <-];rewrite critical_value_imageE.
    exists x;last reflexivity.
    apply/critical_rank_locusP;split;first exact:Logic.I.
    have [D [hD hRankD]]:=hRank x hx.
    exists D;split;first exact:hD.
    exists nu;split;first exact:hRankD.
    exact:leqnn.
  have hMeasure:is_measure (@real_hausdorff_measure R M t ht):=
    @real_hausdorff_measure_is_measure R M t ht.
  have hNull:@real_hausdorff_measure R M t ht (F @` B)=0.
    exact:(@measure_null_subset R (Choice.clone M _)
      (@real_hausdorff_measure R M t ht) hMeasure (F @` B)
      (critical_value_image N (fun _=>True) F nu) hSubset hOriginalNull).
  have hDegree:(t<=sigma)%R:=ltW (lt_trans hTGamma hGammaSigma).
  have hHigher:=@critical_real_hausdorff_null_higher_degree R M t sigma ht hSigma
    (F @` B) hDegree hNull.
  by rewrite hHigher ltxx in hPositive.
Qed.

(** Source for [critical_value_announced_least]: the opaque
    scalar s defined for the problem in 3.4.1, p. 310,
    is now proved least by 3.4.3–3.4.4,
    pp. 316–318. Its exact public equation identifies
    natural complementary dimension with real subtraction. *)
Theorem critical_value_announced_least (R:realType) m nu k
    (hK:(1<=k)%N) (hNu:(nu<m)%N)
    (hp:(0<=@CriticalValueDegree.value R m nu k hK hNu)%R):
  @is_least_critical_value_degree R m nu k (@CriticalValueDegree.value R m nu k hK hNu) hp.
Proof.
have hEquation:@CriticalValueDegree.value R m nu k hK hNu=
    (nu%:R+(m-nu)%:R/k%:R)%R.
  by rewrite critical_value_degree_formula natrB //;exact:ltnW hNu.
move:hp;rewrite hEquation=>hp.
exact:(@critical_value_least_degree R m nu k hp hNu hK).
Qed.
