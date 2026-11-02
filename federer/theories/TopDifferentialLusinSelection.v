(** Federer (1969), 3.1.15, p. 227:
    "we use 2.3.5 to obtain a closed set E such that D D^k f|E is
    continuous and L^m(A-E)<epsilon". On a measurable set A2 of
    finite measure inside the common domain of the approximate
    partials of the coordinates, Lusin's theorem gives a closed
    subset on which all these partials are continuous, with small
    defect; their values are chosen there. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct InnerNorm InnerMetric HilbertFormCompactness RealNormUP
  EuclideanLebesgueDimensions EuclideanMetricSeparability NormClassOneUP
  ContinuousMultilinearUP NormHigherDifferentialUP SymmetricMultiIndices
  PartialFunctionUP PartialFunctionBasic PartialZeroExtension PartialContinuityUP
  MeasurableFunctionUP MeasureUP MeasureBasic MeasureRestriction MeasureFiniteClosure
  MeasureFiniteUnionBound MeasureAlmostUP MeasureAlmostBasic RegularMeasureUP
  BorelRegularMeasureUP RegularMeasureRestriction MetricClosedBalls LusinMetric MeasureSplit
  TopDifferentialMeasurablePartials.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Section LusinSelection.
Variable R : realType.
Variables m n : nat.
Local Notation X := (inner_metric_space (@euclidean_inner_productP R m.+1)).
Local Notation N := (inner_norm (@euclidean_inner_productP R m.+1)).
Local Notation hN := (inner_norm_real_norm (@euclidean_inner_productP R m.+1)).
Local Notation Yn := (inner_metric_space (@euclidean_inner_productP R n)).
Local Notation NY := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hNY := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation Leb := (@euclidean_lebesgue_measure R m.+1).
Variable Z : nat->lmodType R.
Variable ev : forall i, {ffun 'I_i->R_n R m.+1}->Hom (Z i) (R_n R n).
Variable ZN : forall i, Z i->R.
Hypothesis hZ : forall i, is_continuous_multilinear_space N NY (@ev i) (@ZN i).
Variable k : nat.
Variable B : set X.
Variable Dk : X->Z k.
Hypothesis hDk : norm_class_zero N (@ZN k) B Dk.
Local Notation P := (symmetric_indices m.+1 k*'I_m.+1)%type.
Variable A2 : set X.
Hypothesis hA2m : measure_measurable Leb A2.
Hypothesis hA2f : (Leb A2< +oo)%E.
Hypothesis hA2D : A2 `<=` top_partial_all_domains ev B Dk.
Let hm := euclidean_lebesgue_is_measure R m.+1.
Let hr := euclidean_lebesgue_borel_regular R m.+1.

(** Source for [top_partial_extension]:
    the approximate partial ap D_i D^alpha f restricted to A2 and
    extended by zero, Federer 2.4.10, p. 85, a measurable partial
    function on the whole space. *)
Definition top_partial_extension (p : P) : partial_function X Yn :=
  partial_function_zero_extension 0 A2 (top_partial ev B Dk p.1 p.2).

(** Source for [top_partial_restricted_preimage_measurable]:
    the inverse image under ap D_i D^alpha f of an open set,
    intersected with A2, is measurable, by 3.1.4 and the
    characterisation of measurability for restricted measures,
    Federer 2.1.2, p. 54, and 3.1.4, p. 214. *)
Lemma top_partial_restricted_preimage_measurable (p : P) (U : set Yn) : open U ->
  measure_measurable Leb (A2 `&` partial_function_preimage (top_partial ev B Dk p.1 p.2) U).
Proof.
move=>hU.
have hD := (top_partial_measurable hZ hDk p.1 p.2).2.
have hpre := measurable_function_open_preimage hD hU.
have hsub : A2 `<=` top_partial_domain ev B Dk p.1 p.2.
  move=>x hx; have h := hA2D hx; rewrite /top_partial_all_domains in h; exact: (h p I).
have hres : measure_restrict Leb A2=
    measure_restrict (measure_restrict Leb (top_partial_domain ev B Dk p.1 p.2)) A2.
  by apply/funext=>T; rewrite /measure_restrict setIA (setIidr hsub).
have hpre' : measure_measurable (measure_restrict Leb A2)
    (partial_function_preimage (top_partial ev B Dk p.1 p.2) U).
  rewrite hres; exact: (measure_restrict_measurable _ hpre).
have [B' [C [hB' [hC he]]]] := (regular_measure_restriction_measurable_iff hm
  (borel_regular_is_regular hm hr) (S:=A2)
  (partial_function_preimage (top_partial ev B Dk p.1 p.2) U) hA2f).1 hpre'.
have -> : A2 `&` partial_function_preimage (top_partial ev B Dk p.1 p.2) U=A2 `&` B'.
  rewrite he; apply/seteqP; split=>x.
  - move=>[hx [[hb _]|hc]]; first by split.
    by exfalso; exact: (hC x hc hx).
  - by move=>[hx hb]; split=>//; left; split.
exact: (measure_measurable_intersection hm hA2m hB').
Qed.

(** Source for [top_partial_extension_measurable]:
    the restricted zero extension is measurable, Federer 2.3.2,
    p. 73, and 2.4.10, p. 85. *)
Lemma top_partial_extension_measurable (p : P) :
  is_measure_measurable_function Leb (top_partial_extension p).
Proof.
have hon := @partial_function_zero_extension_on X Yn 0 A2 (top_partial ev B Dk p.1 p.2).
have hoff := @partial_function_zero_extension_off X Yn 0 A2 (top_partial ev B Dk p.1 p.2).
constructor.
- apply: (measure_almost_everywhere_mono hm _ (measure_almost_everywhere_true hm))=>x _.
  rewrite /top_partial_extension partial_function_zero_extension_domain.
  case: (pselect (A2 x))=>[hx|hx]; last by right.
  left; split=>//; have h := hA2D hx; rewrite /top_partial_all_domains in h; exact: (h p I).
- move=>U hU.
  have he : partial_function_preimage (top_partial_extension p) U=
      (A2 `&` partial_function_preimage (top_partial ev B Dk p.1 p.2) U) `|`
      (if pselect (U 0) then ~` A2 else set0).
    apply/seteqP; split=>x.
    + move=>[y [hy hUy]]; case: (pselect (A2 x))=>[hx|hx].
      * by left; split=>//; exists y; split=>//; exact: (hon x y hx).1 hy.
      * right; have hy0 := (hoff x y hx).1 hy; rewrite hy0 in hUy.
        by case: pselect=>[hU0|hn]; [exact hx|exact: (hn hUy)].
    + move=>[[hx [y [hy hUy]]]|hx].
      * by exists y; split=>//; exact: (hon x y hx).2 hy.
      * move: hx; case: pselect=>[hU0 hx|hn hx0]; last by case: hx0.
        by exists 0; split=>//; exact: (hoff x 0 hx).2 erefl.
  rewrite he; apply: (measure_measurable_union hm).
  - exact: top_partial_restricted_preimage_measurable.
  - case: pselect=>hU0; first exact: (measure_measurable_complement hA2m).
    exact: (measure_measurable_empty hm).
Qed.

(** Source for [top_partial_lusin]:
    Lusin's theorem 2.3.5, p. 76, for one restricted partial,
    Federer 3.1.15, p. 227. *)
Lemma top_partial_lusin (p : P) (e : R) : 0<e ->
  exists E : set X, closed E /\ E `<=` A2 /\ (Leb (A2 `\` E)<e%:E)%E /\
    partial_function_continuous_on E (top_partial_extension p).
Proof.
move=>he; have [D [hc hd]] := euclidean_metric_separable R n.
exact: (lusin_borel_regular hm hr hc hd (top_partial_extension_measurable p) hA2m hA2f he).
Qed.

(** Source for [symmetric_index_witness]:
    the multi-index concentrating the degree k on the first
    coordinate, Federer 1.9.2, p. 42; it shows that the index
    set is nonempty. *)
Lemma symmetric_index_witness : exists alpha : symmetric_indices m.+1 k, True.
Proof.
pose a0 : {ffun 'I_m.+1->'I_k.+1} := [ffun i=>if i==ord0 then inord k else ord0].
have hsum : (\sum_(i<m.+1) val (a0 i))%N==k.
  apply/eqP; rewrite (bigD1 ord0) //= big1=>[|i hi].
  - by rewrite ffunE eqxx inordK ?addn0 // ltnSn.
  - by rewrite ffunE (negbTE hi).
by exists (Sub a0 hsum).
Qed.

(** Source for [partial_continuity_pointwise]:
    relative continuity on C in the inverse-image sense of
    Federer 2.3.5, p. 77, gives the epsilon-delta form at each
    point of C. *)
Lemma partial_continuity_pointwise (C : set X) (f : partial_function X Yn) (a : X) (y : Yn) :
  partial_function_continuous_on C f -> C a -> partial_function_graph f a y ->
  forall e : R, 0<e -> exists d : R, 0<d /\
    forall b y', C b -> partial_function_graph f b y' -> mdist a b<d -> mdist y y'<e.
Proof.
move=>hf ha hy e he.
have hU : open [set z : Yn | mdist y z<e] := metric_open_ball_open y e.
have [V [hV hVe]] := partial_continuity_open hf hU.
have haV : V a.
  have hmem : (C `&` partial_function_preimage f [set z | mdist y z<e]) a.
    by split=>//; exists y; split=>//; rewrite /= mdistxx.
  by rewrite hVe in hmem; case: hmem.
rewrite openE in hV; have hnb := hV a haV.
have [d hd hball] := (metricType_numDomainType.nbhs_mdistP a V).1 hnb.
exists d; split=>// b y' hb hy' hab.
have hbV : V b := hball b hab.
have hmem : (C `&` partial_function_preimage f [set z | mdist y z<e]) b by rewrite hVe.
have [_ [y'' [hy'' hlt]]] := hmem.
by rewrite (partial_function_single_valued hy'' hy') in hlt.
Qed.

(** Source for [top_partial_selection]:
    the closed set E of Federer 3.1.15, p. 227: inside A2, with
    L^m(A2-E)<e, on which every approximate partial of every
    coordinate is continuous. *)
Theorem top_partial_selection (e : R) : 0<e ->
  exists E : set X, closed E /\ E `<=` A2 /\ (Leb (A2 `\` E)<e%:E)%E /\
    forall p : P, partial_function_continuous_on E (top_partial_extension p).
Proof.
move=>he.
set e' := e/(#|{: P}|.+1)%:R.
have he' : 0<e' by apply: divr_gt0=>//; rewrite ltr0n.
have [E hE] := choice (fun p=>top_partial_lusin p he').
have [alpha0 _] := symmetric_index_witness.
exists (\bigcap_(p in [set: P]) E p); split; [|split; [|split]].
- by apply: closed_bigI=>p _; exact: (hE p).1.
- by move=>x hx; exact: (hE (alpha0, ord0)).2.1 x (hx (alpha0, ord0) I).
- have hcov : A2 `\` \bigcap_(p in [set: P]) E p `<=` \bigcup_p (A2 `\` E p).
    move=>x [hx hn]; apply: contrapT=>hall; apply: hn=>p _.
    by apply: contrapT=>hnp; apply: hall; exists p.
  apply: (le_lt_trans (measure_mono hm hcov)).
  apply: (le_lt_trans (measure_finite_union_bound _ hm)).
  have hsum : (\sum_(p : P) Leb (A2 `\` E p)<=\sum_(p : P) e'%:E)%E.
    by apply: lee_sum=>p _; exact: (ltW (hE p).2.2.1).
  apply: (le_lt_trans hsum).
  rewrite sumEFin sumr_const lte_fin -mulr_natl /e' mulrA ltr_pdivrMr ?ltr0n //.
  by rewrite [_%:R*e]mulrC (ltr_pM2l he) ltr_nat ltnSn.
- move=>p; apply: (partial_continuity_subset _ (hE p).2.2.2).
  by move=>x hx; exact: (hx p I).
Qed.
End LusinSelection.
