(** Federer (1969), 2.10.25, p. 189, grouped weights u_j(T)=sum of source
    costs over members with the same closed image: supporting
    finite-real-weight assembly. The intermediate grouped sum can be
    infinite. Finite total cost forces such a group's target cost to vanish;
    an explicit null-generator law then permits its removal. The actual
    cover retains finite real coefficients, as required by 2.10.24, p. 186. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import NonnegativeSum NonnegativeSumSupport NonnegativeSumGrouping
  NonnegativeSumRestriction NonnegativeSumExtendedScale MeasureUP MeasureBasic MeasureIndexedCover
  MeasureAlmostUP MeasureAlmostBasic WeightedMetricEnvelopeUP MetricDiameter.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [weighted_generator_image_assembly]: supporting
    regrouping in the proof of 2.10.25, p. 189,
    with the finite-real coefficient domain of 2.10.24,
    p. 186. The map from source to target generators
    need not be injective. A zero-cost target is
    removed only under its separately proved null law;
    no infinite covering coefficient is introduced. *)
Theorem weighted_generator_image_assembly (R : realType) (Y : metricType R) (I K : choiceType)
    (T : K -> set Y) (c : K -> \bar R) (psi : set Y -> \bar R)
    (G : set I) (q : I -> K) (a : I -> R) (delta : \bar R) (f : Y -> \bar R) :
  is_measure psi -> (forall k, 0<=c k) -> countable G -> (forall i, G i -> (0<=a i)%R) ->
  (forall i, G i -> extended_metric_diameter (T (q i))<=delta) ->
  (forall k, (q @` G) k -> c k=0 -> psi (T k)=0) ->
  nonnegative_sum G (fun i=>(a i)%:E*c (q i))< +oo ->
  measure_almost_everywhere psi [set y | f y<=weighted_generator_sum (fun i=>T (q i)) G a y] ->
  exists H u, is_weighted_metric_cover T psi delta f H u /\
    weighted_generator_cost c H u<=nonnegative_sum G (fun i=>(a i)%:E*c (q i)).
Proof.
move=> hm hc hG ha hdiam hnull hbudget hdom.
pose U := q @` G.
pose sigma k := nonnegative_sum (G `&` [set i | q i==k]) (fun i=>(a i)%:E).
have hs0 k : 0<=sigma k := nonnegative_sum_nonnegative _ _.
have hU : countable U.
  apply: sub_countable (card_image_le _ _) hG.
have hqu i (hi : G i) : U (q i) by exists i.
have hcostgroup : nonnegative_sum G (fun i=>(a i)%:E*c (q i))=
    nonnegative_sum U (fun k=>sigma k*c k).
  rewrite (@nonnegative_sum_grouping R I K G U q (fun i=>(a i)%:E*c (q i)))=> //.
  2: move=> i hi; apply: mule_ge0; [rewrite lee_fin; exact: ha|exact: hc].
  apply: nonnegative_sum_ext=> k hk.
  have he : nonnegative_sum (G `&` [set i | q i==k]) (fun i=>(a i)%:E*c (q i))=
      nonnegative_sum (G `&` [set i | q i==k]) (fun i=>c k*(a i)%:E).
    apply: nonnegative_sum_ext=> i [hi /eqP hik]; by rewrite hik muleC.
  rewrite he nonnegative_sum_extended_scale //; first exact: muleC.
  move=> i [hi _]; rewrite lee_fin; exact: ha.
pose B := U `&` [set k | sigma k=+oo].
pose H := U `&` [set k | sigma k< +oo].
pose u k := fine (sigma k).
have hB : countable B := sub_countable (subset_card_le (fun k (hk : B k)=>hk.1)) hU.
have hH : countable H := sub_countable (subset_card_le (fun k (hk : H k)=>hk.1)) hU.
have hreal k (hk : H k) : sigma k=(u k)%:E.
  have hh : sigma k \is a fin_num by rewrite (ge0_fin_numE (hs0 k)); exact hk.2.
  by rewrite /u fineK.
have hu k (hk : H k) : (0<=u k)%R.
  have hh := hs0 k; by rewrite (hreal k hk) lee_fin in hh.
have hbadcost k (hk : B k) : c k=0.
  case: (eqVneq (c k) 0)=> [hz|hne]; first exact hz.
  have hpos : 0<c k by rewrite lt_neqAle eq_sym hne (hc k).
  have hh := @nonnegative_sum_term R K U (fun k=>sigma k*c k) k hk.1.
  have hsumfin : nonnegative_sum U (fun k=>sigma k*c k)< +oo by rewrite -hcostgroup.
  rewrite hk.2 (gt0_mulye hpos) in hh.
  have hfalse := le_lt_trans hh hsumfin; by rewrite ltxx in hfalse.
pose Z := \bigcup_(k in B) T k.
have hZ : psi Z=0.
  have hh := @measure_indexed_cover R Y K psi hm Z B T hB (fun y hy=>hy).
  have he : nonnegative_sum B (fun k=>psi (T k))=0.
    apply: nonnegative_sum_zero=> k hk; exact: hnull k hk.1 (hbadcost k hk).
  rewrite he in hh; apply/eqP; by rewrite eq_le hh (measure_nonnegative hm Z).
have hpoint y (hyZ : ~Z y) : weighted_generator_sum T H u y=
    weighted_generator_sum (fun i=>T (q i)) G a y.
  have hgroup := @nonnegative_sum_grouping R I K [set i | G i /\ T (q i) y] U q
    (fun i=>(a i)%:E) (fun i hi=>hqu i hi.1)
    (fun i hi=>(ha i hi.1 : 0<=(a i)%:E)).
  have hinner k : nonnegative_sum
      ([set i | G i /\ T (q i) y] `&` [set i | q i==k]) (fun i=>(a i)%:E)=
      if y \in T k then sigma k else 0.
    case hy: (y \in T k).
    - have he : ([set i | G i /\ T (q i) y] `&` [set i | q i==k])=
          (G `&` [set i | q i==k]).
        apply/seteqP; split=> [i [[hi _] heq]|i [hi heq]]; first by split.
        split=> //; split=> //; have /eqP hik := heq; rewrite hik; exact: set_mem hy.
      by rewrite he.
    - have he : ([set i | G i /\ T (q i) y] `&` [set i | q i==k])=set0.
        apply/seteqP; split=> [i [[hi hiy] /eqP hik]|i []].
        have hky : T k y by rewrite -hik.
        by rewrite (mem_set hky) in hy.
      by rewrite he nonnegative_sum_empty.
  have hfun : (fun k=>nonnegative_sum
      ([set i | G i /\ T (q i) y] `&` [set i | q i==k]) (fun i=>(a i)%:E))=
      (fun k=>if k \in [set k | T k y] then sigma k else 0).
    apply: funext=> k; rewrite hinner.
    have hi : (y \in T k)=(k \in [set k | T k y]).
      apply/idP/idP=> /set_mem hy; apply: mem_set; exact hy.
    by rewrite hi.
  rewrite hfun nonnegative_sum_restrict in hgroup.
  have hset : (U `&` [set k | T k y])=(H `&` [set k | T k y]).
    apply/seteqP; split.
    - move=> k [hkU hky]; split=> //; split=> //.
      case: (ltP (sigma k) +oo)=> [hfin|hinf]; first by [].
      have he : sigma k=+oo by apply/eqP; rewrite eq_le leey hinf.
      exfalso; apply: hyZ; exists k=> //; by split.
    - by move=> k [[hk _] hky]; split.
  rewrite hset in hgroup; rewrite /weighted_generator_sum hgroup.
  apply: nonnegative_sum_ext=> k [hk hky]; exact: esym (hreal k hk).
have hoff : measure_almost_everywhere psi (~` Z) by rewrite /measure_almost_everywhere setCK.
have hcover : is_weighted_metric_cover T psi delta f H u.
  constructor.
  - exact hH.
  - exact hu.
  - move=> k [[i hi <-] _]; exact: hdiam i hi.
  - apply: (@measure_almost_everywhere_mono R Y psi hm _ _ _
      (measure_almost_everywhere_and hm hdom hoff))=> y [hy hyZ].
    change (is_true (f y<=weighted_generator_sum T H u y)); by rewrite (hpoint y hyZ).
exists H,u; split=> //.
rewrite /weighted_generator_cost hcostgroup.
apply: le_trans (_ : nonnegative_sum H (fun k=>sigma k*c k)<=nonnegative_sum U (fun k=>sigma k*c k)).
- apply: nonnegative_sum_mono=> k hk; by rewrite (hreal k hk).
- apply: nonnegative_sum_subset=> k hk; exact hk.1.
Qed.
