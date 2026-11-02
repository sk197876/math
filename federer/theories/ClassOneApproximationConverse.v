(** Federer (1969), 3.1.17, p. 229: the converse of 3.1.16, with the
    necessary measurable-domain and positive-source qualifications made
    explicit. Borel hulls of the approximation errors produce measurable
    agreement sets; their density-one points give finite approximate growth. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations EuclideanInnerProduct InnerNorm InnerMetric
  HilbertFormCompactness ContinuousMultilinearUP NormClassOneUP NormClassHigherUP
  NormClassHigherFirst EuclideanLebesgueDimensions MeasureUP MeasureBasic
  MeasureFiniteClosure MeasureAlmostUP MeasureAlmostBasic MeasureSplit
  BorelRegularMeasureUP MeasureDensityPoints DensityMeasurableSets
  EuclideanApproximateContext ExtendedRealReciprocalBounds
  ClassOneApproximationUP ClassOneAgreementApproximateGrowth
  ApproximateGrowthDomainMeasurable ApproximateGrowthClassOneApproximation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section Converse.
Variable R : realType.
Variables m n : nat.
Local Notation X := (inner_metric_space (@euclidean_inner_productP R m.+1)).
Local Notation Y := (inner_metric_space (@euclidean_inner_productP R n)).
Local Notation NX := (inner_norm (@euclidean_inner_productP R m.+1)).
Local Notation NY := (inner_norm (@euclidean_inner_productP R n)).
Local Notation mu := (@euclidean_lebesgue_measure R m.+1).
Variable Z : nat->lmodType R.
Variable ev : forall i, {ffun 'I_i->R_n R m.+1}->Hom (Z i) (R_n R n).
Variable ZN : forall i, Z i->R.
Hypothesis hZ : forall i, is_continuous_multilinear_space NX NY (@ev i) (@ZN i).
Variables (A : set X) (f : X->Y).

(** Source for [class_one_approximation_finite_approximate_growth]: the
    converse asserted in Federer 3.1.17, p. 229, for a measurable domain
    in positive source dimension. These qualifications are necessary under
    the book's partial-domain and empty-product conventions, as shown by
    the separate counterexamples. *)
Theorem class_one_approximation_finite_approximate_growth :
  measure_measurable mu A -> has_class_one_lusin_approximation ev ZN A f ->
  measure_almost_everywhere_on mu A (finite_approximate_growth_points A f).
Proof.
move=>hA happ.
pose hm := euclidean_lebesgue_is_measure R m.+1.
pose hr := euclidean_lebesgue_borel_regular R m.+1.
pose P := finite_approximate_growth_points A f.
have hp (j : nat) : 0<(j.+1%:R : R)^-1 by rewrite invr_gt0 ltr0n.
have hex j := happ ((j.+1%:R : R)^-1) (hp j).
have [G hG] := choice hex.
have [H hH] := choice (fun j=>borel_regular_cover hr (A `\` [set x | f x=G j x])).
pose K j := A `\` H j.
have hKm j : measure_measurable mu (K j).
  apply: (@measure_measurable_difference R X mu hm _ _ hA).
  exact (borel_regular_borel_measurable hm hr (hH j).2.1).
have hfg j x : K j x -> f x=G j x.
  move=>[ha hn]; apply: contrapT=>hne; apply: hn; apply: (hH j).1.
  by split.
have hnull : mu (A `\` \bigcup_j K j)=0%E.
  apply/eqP; rewrite eq_le (measure_nonnegative hm) andbT.
  apply: (@extended_real_reciprocal_upper_bound R _ 0%R)=>j; rewrite add0r.
  have hsub : A `\` \bigcup_j K j `<=` H j.
    move=>x [ha hn]; apply: contrapT=>hnot; apply: hn; exists j=>//; by split.
  have hb := measure_mono hm hsub.
  rewrite -(hH j).2.2 in hb.
  exact (le_trans hb (ltW (hG j).2)).
have hpiece j : measure_almost_everywhere_on mu (K j) P.
  have hden := (density_complement_zero_points_conclusions (K j)
    (euclidean_approximate_context R m.+1)).2.2.2.1 (hKm j).
  have hclass : norm_class_one NX NY (fun _=>True) (G j).
    exact ((@norm_class_higher_first R (R_n R m.+1) (R_n R n) NX NY
      (inner_norm_real_norm (@euclidean_inner_productP R m.+1))
      (inner_norm_real_norm (@euclidean_inner_productP R n)) Z ev ZN hZ
      (fun _=>True) (G j)).1 (hG j).1).
  apply: (measure_almost_everywhere_on_implication _ _ _).2.
  apply: (measure_almost_everywhere_mono hm _
    ((measure_almost_everywhere_on_implication _ _ _).1 hden)).
  move=>a hd ha.
  exact (@class_one_agreement_finite_approximate_growth R m n A (K j) f (G j) a
    (fun x hx=>hx.1) (hfg j) ha (hd ha) hclass).
have hall : measure_almost_everywhere mu (\bigcap_j [set a | K j a -> P a]).
  apply: (measure_almost_everywhere_countable hm); first exact: countableP.
  move=>j _; exact: (measure_almost_everywhere_on_implication _ _ _).1 (hpiece j).
have hcov : A `\` P `<=` (A `\` \bigcup_j K j) `|` (~`\bigcap_j [set a | K j a -> P a]).
  move=>a [ha hn]; case: (pselect ((\bigcup_j K j) a))=>[[j _ hj]|hnot]; last by left; split.
  right.
  move=>hh; apply: hn; exact: hh j I hj.
apply/eqP; rewrite eq_le (measure_nonnegative hm) andbT.
have hb := @measure_binary_cover R X mu hm (A `\` P) _ _ hcov.
by rewrite hnull hall add0e in hb.
Qed.

(** Source for [federer_3_1_17]: precise positive-dimensional equivalence
    underlying the optimality discussion in Federer 3.1.17, p. 229.
    The right side includes domain measurability, which is forced by the
    growth condition but is not forced by approximation alone. The
    higher-class question in the paragraph is historical commentary. *)
Theorem federer_3_1_17 :
  measure_almost_everywhere_on mu A (finite_approximate_growth_points A f) <->
  measure_measurable mu A /\ has_class_one_lusin_approximation ev ZN A f.
Proof.
split.
- move=>hg; split; first exact: approximate_growth_ae_domain_measurable hg.
  move=>e he; exact (@federer_3_1_16 R m.+1 n Z ev ZN hZ A f hg e he).
- by move=>[hA happ]; exact: class_one_approximation_finite_approximate_growth.
Qed.
End Converse.
