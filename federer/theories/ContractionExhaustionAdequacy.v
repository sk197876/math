(** Federer (1969), proof of 2.8.2, p. 143, last paragraph: each
    finite-measure target has vanishing remaining measure because its
    contraction occurs infinitely often. We prove the conclusion for any
    abstract exhaustion with the required laws, never unfolding the selected
    witness. Source context and initial-index convention:
    ContractionCoverUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import MeasureUP MeasureBasic MeasureAlmostBasic
  CoveringFamilyUP RecurrentEnumerationUP RecurrentContraction
  ContractionCoverUP ContractionExhaustionLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [contraction_exhaustion_adequate_selection]:
    the countable disjointed family and null remainder in
    Federer 2.8.2, p. 143. This is the finite-target-measure
    case of the proof; targets themselves need not be measurable.
    Countability is used to unite their null remainders. *)
Theorem contraction_exhaustion_adequate_selection (R : realType) (X : metricType R)
    (mu : set X -> \bar R) (hm : is_measure mu)
    (F K : set (set X)) (sigma : set X -> R)
    (b : nat -> set X) (V : set X) (W : nat -> set X)
    (G : nat -> set (set X)) :
  countable K -> is_recurrent_enumeration K b ->
  (forall T, K T -> mu T < +oo) ->
  (forall T, K T -> (0 < sigma T < 1)%R) ->
  is_cover_contraction_exhaustion mu F b (fun n => Num.sqrt (sigma (b n))) V W G ->
  is_adequate_cover_selection mu F (\bigcup_(T in K) T) V (cover_exhaustion_family G).
Proof.
move=> hK hb hfinite hsigma hE.
pose q n := Num.sqrt (sigma (b n)).
pose U := \bigcup_(B in cover_exhaustion_family G) B.
have hres := @contraction_exhaustion_residual R X mu F b q V W G hE.
have hnull T (hT : K T) : mu ((V `&` T) `\` U) = 0.
  have hfin n : mu (W n `&` T) \is a fin_num.
    rewrite (ge0_fin_numE (@measure_nonnegative R X mu hm _)).
    apply: le_lt_trans (@measure_mono R X mu hm _ T _) (hfinite T hT).
    by move=> x [].
  pose a n := fine (mu (W n `&` T)).
  have hnon n : (0 <= a n)%R.
    have h := @measure_nonnegative R X mu hm (W n `&` T).
    by rewrite -(fineK (hfin n)) lee_fin in h.
  have hmono n m : (n <= m)%N -> (a m <= a n)%R.
    move=> hnm.
    have h := @contraction_exhaustion_measure_decreasing R X mu F b q V W G hE hm T n m hnm.
    by rewrite -(fineK (hfin m)) -(fineK (hfin n)) lee_fin in h.
  have hrec N : exists n, (N <= n)%N /\ (a n.+1 <= Num.sqrt (sigma T) * a n)%R.
    have [n [hN hn]] := @recurrent_enumeration_cofinal [the choiceType of set X] K b hb T hT N.
    have hq : q n = Num.sqrt (sigma T) by rewrite /q hn.
    have h := @contraction_exhaustion_measure_step R X mu F b q V W G hE n T
      (Num.sqrt (sigma T)) hn hq.
    rewrite -(fineK (hfin n.+1)) -(fineK (hfin n)) -EFinM lee_fin in h.
    exists n; by split.
  have hroot := @covering_contraction_root_bounds R (sigma T) (hsigma T hT).
  have hsmall := @recurrent_contraction_small R (Num.sqrt (sigma T)) a hroot.1 hnon hmono hrec.
  have hrf : mu ((V `&` T) `\` U) \is a fin_num.
    rewrite (ge0_fin_numE (@measure_nonnegative R X mu hm _)).
    apply: le_lt_trans (@measure_mono R X mu hm _ T _) (hfinite T hT).
    by move=> x [[_ ht] _].
  apply/eqP; rewrite eq_le (measure_nonnegative hm) andbT leNgt; apply/negP=> hp.
  have hrp : (0 < fine (mu ((V `&` T) `\` U)))%R.
    by move: hp; rewrite -(fineK hrf) lte_fin.
  have [N hN] := hsmall _ hrp.
  have hle : mu ((V `&` T) `\` U) <= mu (W N `&` T).
    apply: (@measure_mono R X mu hm _ _)=> x [[hv ht] hn].
    have hx : (V `\` U) x by split.
    rewrite hres in hx; split=> //; exact: hx N Logic.I.
  have hreal : (fine (mu ((V `&` T) `\` U)) <= a N)%R.
    by move: hle; rewrite -(fineK hrf) -(fineK (hfin N)) lee_fin.
  have hbad := le_lt_trans hreal (hN N (leqnn N)).
  by rewrite ltxx in hbad.
constructor.
- exact (@contraction_exhaustion_family_members R X mu F b q V W G hE).
- exact (@contraction_exhaustion_family_countable R X mu F b q V W G hE).
- exact (@contraction_exhaustion_family_disjoint R X mu F b q V W G hE).
- exact (@contraction_exhaustion_union_within R X mu F b q V W G hE).
- have hz := @measure_null_countable_union R X [the choiceType of set X] mu hm K
    (fun T => (V `&` T) `\` U) hK hnull.
  apply: (@measure_null_subset R X mu hm _ _ _ hz).
  move=> x [[hv [T hT ht]] hn]; exists T=> //; by split=> //; split.
Qed.
