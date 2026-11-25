(** Federer (1969), 3.1.15, p. 227:
    the closed set F of the proof. The domain is exhausted by the
    open annuli about the origin; on each annulus Lusin's theorem
    gives a closed set E_i on which the derivative D D^k f is
    continuous, and continuity from above of the measure, tested
    through a measurable hull of A, selects the radii 1/(q+1) of
    the uniform differentiability sets of the top differential.
    The closed union F of the pieces satisfies L^m(A-F)<epsilon,
    D^k f is differentiable with the continuous derivative T at
    every point of F, and the rates are uniform on bounded sets. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  cardinality reals constructive_ereal topology lra.
From Federer Require Import Hom GrassmannAbbreviations FiniteCoordinates
  EuclideanInnerProduct InnerNorm InnerMetric HilbertFormCompactness RealNormUP
  EuclideanLebesgueDimensions EuclideanLebesgueBoxes NormDifferentialUP
  NormDifferentialLocal NormDifferentialFiniteCalculus NormClassOneUP
  ContinuousMultilinearUP ContinuousMultilinearNorm NormHigherDifferentialUP
  SymmetricMultiIndices NormHigherMultiPartialUP PartialFunctionUP
  PartialZeroExtension PartialContinuityUP MeasurableFunctionUP MeasureUP
  MeasureBasic MeasureHull MeasureAlmostUP MeasureAlmostBasic
  MeasureContinuityAbove MeasureSplit RegularMeasureUP BorelRegularMeasureUP
  TopologicalBorel MetricClosedBalls NonnegativeSum NonnegativeSumImageBound
  CountableGeometricBudget EuclideanClosedBallVolume ExtendedRealOrderLimit
  MeasureFiniteClosure MeasureCountableClosure TopDifferentialStepanoff
  TopDifferentialMeasurablePartials TopDifferentialLusinSelection
  TopDifferentialDerivativeField TopDifferentialFromCoordinates
  TopDifferentialUniformSets OpenAnnuliClosedUnion EuclideanSphereNull.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Section GoodSet.
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
Variables (A B : set X).
Variable f : X->R_n R n.
Variable Dk : X->Z k.
Hypothesis hDkf : forall x, B x -> has_norm_higher_differential N ev ZN B f k x (Dk x).
Hypothesis hDk : norm_class_zero N (@ZN k) B Dk.
Hypothesis hAB : A `<=` B.
Hypothesis hB : open B.
Hypothesis hgrowth : forall a, A a -> exists M r : R, 0<r /\
  forall x, B x -> N (x-a)<r -> @ZN k (Dk x-Dk a)<=M*N (x-a).
Local Notation P := (symmetric_indices m.+1 k*'I_m.+1)%type.
Variable iota : symmetric_indices m.+1 k->Hom (R_n R n) (Z k).
Hypothesis hiota_bound : forall alpha, norm_bounded_linear NY (@ZN k) (iota alpha).
Hypothesis hiota_rec : forall (A : X->Prop) (g : X->R_n R n) (a : X) (z : Z k),
  has_norm_higher_differential N ev ZN A g k a z ->
  z=\sum_alpha iota alpha (@ev k (norm_multi_partial_arguments R alpha) z).
Let hZNk : is_real_norm (@ZN k) := continuous_multilinear_norm_is_norm hNY (@hZ k).
Let hm := euclidean_lebesgue_is_measure R m.+1.
Let hr := euclidean_lebesgue_borel_regular R m.+1.
Local Notation U := (open_annulus (0:X)).
Local Notation Diff := ([set a : X | norm_differentiable_at N (@ZN k) B Dk a]).
Local Notation AllDom := (top_partial_all_domains ev B Dk).

(** Source for [top_partial_value]:
    a value of the approximate partial ap D_i D^alpha f at every
    point of its domain, Federer 3.1.15, p. 227. *)
Definition top_partial_value (p : P) (x : X) : Yn :=
  match pselect (exists y, partial_function_graph (top_partial ev B Dk p.1 p.2) x y) with
  | left h => proj1_sig (cid h)
  | right _ => 0
  end.

(** Source for [top_partial_value_graph]:
    on the common domain the chosen values lie on the graphs,
    Federer 3.1.15, p. 227. *)
Lemma top_partial_value_graph (p : P) (x : X) : AllDom x ->
  partial_function_graph (top_partial ev B Dk p.1 p.2) x (top_partial_value p x).
Proof.
move=>hx; rewrite /top_partial_value; case: pselect=>[h|h].
- exact: (proj2_sig (cid h)).
- exfalso; apply: h; rewrite /top_partial_all_domains in hx; exact: (hx p I).
Qed.

(** Source for [top_derivative_field]:
    the derivative D D^k f assembled from the chosen partial
    values, Federer 3.1.15, p. 227. *)
Definition top_derivative_field : X->Hom X (Z k) := top_derivative iota top_partial_value.

(** Source for [differentiable_in_all_domains]:
    at a point of differentiability of D^k f every coordinate is
    differentiable, so the point lies in the common domain of
    the approximate partials, Federer 3.1.15, p. 227. *)
Lemma differentiable_in_all_domains (a : X) : Diff a -> AllDom a.
Proof.
move=>[L hL]; apply: top_partial_all_domains_at_differentiability_point=>alpha.
have hbnd : norm_bounded_linear (@ZN k) NY (@ev k (norm_multi_partial_arguments R alpha)).
  exists (\prod_(j<k) N (norm_multi_partial_arguments R alpha j)); split.
  - apply: prodr_ge0=>j _; exact: (real_seminorm_nonnegative hN.1).
  - move=>z; rewrite mulrC.
    exact: (multilinear_operator_bound (continuous_multilinear_norm_laws (@hZ k) z) _).
exists (hom_comp (@ev k (norm_multi_partial_arguments R alpha)) L).
exact: (norm_differential_postcompose hN hL hbnd).
Qed.

(** Source for [top_differential_null_complement]:
    L^m(A-dmn D D^k f)=0, Federer 3.1.15, p. 227, from 3.1.9. *)
Lemma top_differential_null_complement : Leb (A `\` Diff)=0.
Proof. exact: (top_differential_almost_everywhere hZ hDkf hDk hiota_bound hiota_rec hAB hB hgrowth). Qed.

(** Source for [good_piece]:
    the piece of the construction inside the i-th open annulus:
    the Lusin set E with L^m(A_i-E) at most b_0, and for every j
    the closed set G_j of points of E where eta_q<=1/(j+1) for the
    selected q_j, with L^m(A_i cap E-G_j) at most b_j; the
    selection uses continuity from above tested through the hull
    of A_i, since the limit set consists of points of A_i where
    D^k f is not differentiable, Federer 3.1.15, p. 227
    ("2.3.7 and 2.2.2 allow us to construct a closed subset F"). *)
Lemma good_piece (i : nat) (b0 : R) (b : nat->R) : 0<b0 -> (forall j, 0<b j) ->
  exists E : set X, exists G : nat->set X, exists q : nat->nat,
    [/\ closed E, E `<=` U i, E `<=` B, (forall j, closed (G j)) & (forall j, G j `<=` E)] /\
    [/\ (Leb ((A `&` U i) `\` E)<=b0%:E)%E,
        (forall j, (Leb ((E `\` G j) `&` (A `&` U i))<=(b j)%:E)%E),
        (forall j a, G j a -> forall x, B x -> 0<N (x-a) -> N (x-a)<((q j).+1%:R)^-1 ->
          @ZN k (Dk x-Dk a-top_derivative_field a (x-a))<=(j.+1%:R)^-1*N (x-a)),
        (forall a, (forall j, G j a) -> has_norm_differential N (@ZN k) B Dk a (top_derivative_field a)) &
        (forall a, E a -> forall t : R, 0<t -> exists d : R, 0<d /\ forall b', E b' -> N (b'-a)<d ->
          forall h, @ZN k ((top_derivative_field b'-top_derivative_field a) h)<=t*N h)].
Proof.
move=>hb0 hb.
set Ui := U i.
set Ai := A `&` Ui.
have hUio : open Ui := open_annulus_open (0:X) i.
have hUim : measure_measurable Leb Ui := euclidean_borel_measurable (open_borel_set hUio).
have hBm : measure_measurable Leb B := euclidean_borel_measurable (open_borel_set hB).
have hAiball : Ai `<=` metric_closed_ball (0:X) i.+1%:R.
  by move=>x [_ /andP [_ hx]]; rewrite /metric_closed_ball /=; exact: ltW hx.
have hAifin : (Leb Ai< +oo)%E.
  apply: (le_lt_trans (measure_mono hm hAiball)).
  rewrite (euclidean_closed_ball_normalized_volume (0:X) (ler0n _ _)); exact: ltry.
have [H hH] := regular_measure_finite_hull hm (borel_regular_is_regular hm hr) hAifin.
have hAiH : Ai `<=` H := measure_hull_subset hH.
have hHm : measure_measurable Leb H := measure_hull_measurable hH.
have hHfin : (Leb H< +oo)%E by rewrite -(measure_hull_equal_measure hm hH).
set A2 := H `&` Ui `&` B `&` AllDom.
have hA2m : measure_measurable Leb A2.
  apply: (measure_measurable_intersection hm); last exact: (top_partial_all_domains_measurable hZ hDk).
  apply: (measure_measurable_intersection hm)=>//.
  exact: (measure_measurable_intersection hm).
have hA2H : A2 `<=` H by move=>x [[[hx _] _] _].
have hA2U : A2 `<=` Ui by move=>x [[[_ hx] _] _].
have hA2B : A2 `<=` B by move=>x [[_ hx] _].
have hA2D : A2 `<=` AllDom by move=>x [_ hx].
have hA2f : (Leb A2< +oo)%E := le_lt_trans (measure_mono hm hA2H) hHfin.
have [E [hEc [hEA2 [hEdef hEcont]]]] := top_partial_selection hZ hDk hA2m hA2f hA2D hb0.
have hEB : E `<=` B := subset_trans hEA2 hA2B.
have hEU : E `<=` Ui := subset_trans hEA2 hA2U.
have hval : forall (p : P) x, A2 x ->
    partial_function_graph (top_partial ev B Dk p.1 p.2) x (top_partial_value p x).
  move=>p x hx; have hx2 : AllDom x := hA2D x hx.
  exact: (top_partial_value_graph p hx2).
have hTb : forall a, E a -> norm_bounded_linear N (@ZN k) (top_derivative_field a).
  by move=>a _; exact: (top_derivative_bounded hZ hiota_bound top_partial_value a).
have hTc : forall a, E a -> forall t : R, 0<t -> exists d : R, 0<d /\ forall b', E b' -> N (b'-a)<d ->
    forall h, @ZN k ((top_derivative_field b'-top_derivative_field a) h)<=t*N h.
  by move=>a ha t ht; exact: (top_derivative_continuous hZ hiota_bound hEA2 hEcont hval ha ht).
pose G q j := uniform_set (@ZN k) B Dk E top_derivative_field q j.
have hGc : forall q j, closed (G q j).
  by move=>q j; exact: (uniform_set_closed hZNk hDk hEc hEB hTb hTc).
have hGE : forall q j, G q j `<=` E by move=>q j; exact: uniform_set_subset.
have hGm : forall q q' j, (q<=q')%N -> G q j `<=` G q' j by move=>q q' j; exact: uniform_set_monotone.
have hGdiff : forall j a, E a -> has_norm_differential N (@ZN k) B Dk a (top_derivative_field a) ->
    exists q, G q j a.
  by move=>j a ha hd; exact: (uniform_set_from_differential j ha hd).
have hEm : measure_measurable Leb E := euclidean_borel_measurable (closed_borel_set hEc).
have hGmeas : forall q j, measure_measurable Leb (G q j).
  by move=>q j; exact: euclidean_borel_measurable (closed_borel_set (hGc q j)).
have hEfin : (Leb E< +oo)%E := le_lt_trans (measure_mono hm hEA2) hA2f.
have hdiffnull := top_differential_null_complement.
have hq : forall j, exists q, (Leb (E `\` G q j)<=(b j)%:E)%E.
  move=>j.
  pose D q := E `\` G q j.
  have hDm : forall q, measure_measurable Leb (D q).
    by move=>q; exact: (measure_measurable_difference hm hEm (hGmeas q j)).
  have hDmono : forall q q', (q<=q')%N -> D q' `<=` D q.
    by move=>q q' hqq x [hx hn]; split=>// hG; apply: hn; exact: (hGm q q' j hqq x hG).
  have hD0 : (Leb (D 0%N)< +oo)%E.
    exact: (le_lt_trans (measure_mono hm (fun x (hx : D 0%N x)=>hx.1)) hEfin).
  have hlim := measure_continuity_above hm hDm hDmono hD0.
  have hTm : measure_measurable Leb (\bigcap_q D q).
    exact: (measure_measurable_countable_intersection hm (countableP _) (fun q _=>hDm q)).
  have hnull : Leb (\bigcap_q D q)=0.
    have hTH : (\bigcap_q D q) `&` H=\bigcap_q D q.
      apply/seteqP; split=>x; first by move=>[hx _].
      by move=>hx; split=>//; exact: (hA2H x (hEA2 x (hx 0%N I).1)).
    rewrite -hTH -(measure_hull_test hH hTm).
    apply: (measure_null_subset hm _ hdiffnull)=>x [hx [hxA _]].
    split; first exact: hxA.
    move=>[L hL].
    have hxE : E x := (hx 0%N I).1.
    have hTL : top_derivative_field x=L :=
      top_derivative_differential hZ hDkf hiota_bound hiota_rec hval (hEA2 x hxE) hL.
    have hd : has_norm_differential N (@ZN k) B Dk x (top_derivative_field x) by rewrite hTL.
    have [q hGq] := hGdiff j x hxE hd.
    exact: (hx q I).2 hGq.
  rewrite hnull in hlim.
  have hbj : (0<(b j)%:E)%E by rewrite lte_fin.
  have [Q hQ] := hlim.2.2 (b j)%:E hbj.
  exists Q; exact: ltW (hQ Q (leqnn Q)).
have [q hq'] := choice hq.
exists E, (fun j=>G (q j) j), q; split; split.
- exact: hEc.
- exact: hEU.
- exact: hEB.
- by move=>j; exact: hGc.
- by move=>j; exact: hGE.
- have hcov : Ai `\` E `<=` (A `\` Diff) `|` (A2 `\` E).
    move=>x [[hxA hxU] hxE].
    case: (pselect (AllDom x))=>[hxD|hxD].
    + right; split=>//; split; [split; [split|]|]=>//.
      * exact: (hAiH x (conj hxA hxU)).
      * exact: hAB.
    + left; split=>// hdiff; exact: hxD (differentiable_in_all_domains hdiff).
  apply: (le_trans (measure_binary_cover hm hcov)).
  by rewrite hdiffnull add0e; exact: ltW hEdef.
- move=>j.
  have hTm : measure_measurable Leb (E `\` G (q j) j) :=
    measure_measurable_difference hm hEm (hGmeas _ _).
  rewrite (measure_hull_test hH hTm).
  have -> : (E `\` G (q j) j) `&` H=E `\` G (q j) j.
    by apply/seteqP; split=>x; [move=>[hx _]|move=>hx; split=>//; exact: (hA2H x (hEA2 x hx.1))].
  exact: hq'.
- by move=>j a [_ hrate] x hx hp hs; exact: (hrate x hx hp hs).
- by move=>a hQ; exact: (uniform_set_to_differential hZNk hDk hEB hTb hQ).
- exact: hTc.
Qed.

(** Source for [top_differential_good_set]:
    the closed set F of Federer 3.1.15, p. 227, with the
    derivative T=D D^k f on it: L^m(A-F)<epsilon, D^k f is
    differentiable at every point of F with derivative T(a), T is
    continuous on F, and for every bounded part of F and every j
    there is a radius 1/(Q+1) below which the remainder of D^k f
    is at most |x-a|/(j+1); this is the uniform convergence
    lim sup{eta_q(a) : a in C}=0 on compact subsets of F. *)
Theorem top_differential_good_set (e : R) : 0<e ->
  exists (F : set X) (T : X->Hom X (Z k)),
    [/\ closed F, F `<=` B, (Leb (A `\` F)<e%:E)%E,
      (forall a, F a -> has_norm_differential N (@ZN k) B Dk a (T a)) &
      [/\ (forall a, F a -> forall t : R, 0<t -> exists d : R, 0<d /\ forall b, F b -> N (b-a)<d ->
            forall h, @ZN k ((T b-T a) h)<=t*N h) &
          (forall (rho : R) (j : nat), exists Q : nat, forall a, F a -> N a<=rho ->
            forall x, B x -> 0<N (x-a) -> N (x-a)<(Q.+1%:R)^-1 ->
            @ZN k (Dk x-Dk a-T a (x-a))<=(j.+1%:R)^-1*N (x-a))]].
Proof.
move=>he.
have [bud [hbpos hbsum]] := countable_geometric_error_budget (countableP [set: nat*nat]) he.
have [E hE] := choice (fun i=>good_piece i (hbpos (i,0%N)) (fun j=>hbpos (i,j.+1))).
have [G hG] := choice hE.
have [q hq] := choice hG.
have hEc : forall i, closed (E i) by move=>i; case: (hq i)=>[[h _ _ _ _] _]; exact: h.
have hEU : forall i, E i `<=` U i by move=>i; case: (hq i)=>[[_ h _ _ _] _]; exact: h.
have hEB : forall i, E i `<=` B by move=>i; case: (hq i)=>[[_ _ h _ _] _]; exact: h.
have hGc : forall i j, closed (G i j) by move=>i; case: (hq i)=>[[_ _ _ h _] _]; exact: h.
have hGE : forall i j, G i j `<=` E i by move=>i; case: (hq i)=>[[_ _ _ _ h] _]; exact: h.
have hb0 : forall i, (Leb ((A `&` U i) `\` E i)<=(bud (i,0%N))%:E)%E.
  by move=>i; case: (hq i)=>[_ [h _ _ _ _]]; exact: h.
have hbj : forall i j, (Leb ((E i `\` G i j) `&` (A `&` U i))<=(bud (i,j.+1))%:E)%E.
  by move=>i; case: (hq i)=>[_ [_ h _ _ _]]; exact: h.
have hrate : forall i j a, G i j a -> forall x, B x -> 0<N (x-a) -> N (x-a)<((q i j).+1%:R)^-1 ->
    @ZN k (Dk x-Dk a-top_derivative_field a (x-a))<=(j.+1%:R)^-1*N (x-a).
  by move=>i; case: (hq i)=>[_ [_ _ h _ _]]; exact: h.
have hdiff : forall i a, (forall j, G i j a) ->
    has_norm_differential N (@ZN k) B Dk a (top_derivative_field a).
  by move=>i; case: (hq i)=>[_ [_ _ _ h _]]; exact: h.
have hcont : forall i a, E i a -> forall t : R, 0<t -> exists d : R, 0<d /\
    forall b', E i b' -> N (b'-a)<d ->
    forall h, @ZN k ((top_derivative_field b'-top_derivative_field a) h)<=t*N h.
  by move=>i; case: (hq i)=>[_ [_ _ _ _ h]]; exact: h.
pose Fi i := E i `&` \bigcap_j G i j.
pose F := \bigcup_i Fi i.
have hFic : forall i, closed (Fi i).
  by move=>i; apply: closedI; [exact: hEc|apply: closed_bigI=>j _; exact: hGc].
have hFiU : forall i, Fi i `<=` U i by move=>i x [hx _]; exact: (hEU i x hx).
have hFiE : forall i, Fi i `<=` E i by move=>i x [hx _].
have hFc : closed F := annuli_closed_union hFic hFiU.
have hFB : F `<=` B by move=>x [i _ hx]; exact: (hEB i x (hFiE i x hx)).
pose S (p : nat*nat) : set X :=
  match p.2 with
  | 0%N => (A `&` U p.1) `\` E p.1
  | j.+1 => (E p.1 `\` G p.1 j) `&` (A `&` U p.1)
  end.
have hSb : forall p : nat*nat, (Leb (S p)<=(bud p)%:E)%E.
  by move=>[i [|j]]; [exact: hb0|exact: hbj].
have hN0 : Leb (A `\` \bigcup_i U i)=0.
  by apply: (measure_null_subset hm _ (euclidean_annuli_complement_null R m))=>x [_ hx]; exact: hx.
have hcov : A `\` F `<=` (A `\` \bigcup_i U i) `|` \bigcup_(p in [set: nat*nat]) S p.
  move=>x [hxA hxF].
  case: (pselect (exists i, U i x))=>[[i hxU]|hnU]; last first.
    by left; split=>// [[i _ hi]]; apply: hnU; exists i.
  right.
  case: (pselect (E i x))=>[hxE|hxE]; last first.
    by exists (i,0%N)=>//; rewrite /S /=; split.
  have [j hj] : exists j, ~ G i j x.
    apply: contrapT=>hall; apply: hxF; exists i=>//; split=>// j _.
    by apply: contrapT=>hn; apply: hall; exists j.
  by exists (i,j.+1)=>//; rewrite /S /=; split=>//; split.
have hSsum : (Leb (\bigcup_(p in [set: nat*nat]) S p)<=(e/2)%:E)%E.
  have hcount : countable (S @` [set: nat*nat]).
    exact: (sub_countable (card_image_le S _) (countableP _)).
  have hsub : \bigcup_(p in [set: nat*nat]) S p `<=` \bigcup_(B' in S @` [set: nat*nat]) B'.
    by move=>x [p _ hx]; exists (S p)=>//; exists p.
  apply: (le_trans (measure_countable_cover hm hcount hsub)).
  apply: (le_trans (nonnegative_sum_image_bound (A:=[set: nat*nat]) (h:=S) (g:=Leb)
    (fun p _=>measure_nonnegative hm (S p)))).
  exact: (le_trans (nonnegative_sum_mono (A:=[set: nat*nat]) (f:=fun p=>Leb (S p))
    (g:=fun p=>(bud p)%:E) (fun p _=>hSb p)) hbsum).
have hAF : (Leb (A `\` F)<e%:E)%E.
  apply: (le_lt_trans (measure_binary_cover hm hcov)).
  rewrite hN0 add0e; apply: (le_lt_trans hSsum).
  by rewrite lte_fin; lra.
have hFdiff : forall a, F a -> has_norm_differential N (@ZN k) B Dk a (top_derivative_field a).
  by move=>a [i _ [_ hQ]]; exact: (hdiff i a (fun j=>hQ j I)).
have hFcont : forall a, F a -> forall t : R, 0<t -> exists d : R, 0<d /\ forall b, F b -> N (b-a)<d ->
    forall h, @ZN k ((top_derivative_field b-top_derivative_field a) h)<=t*N h.
  move=>a [i _ hai] t ht.
  have haE : E i a := hFiE i a hai.
  have [d1 [hd1 hcd]] := hcont i a haE t ht.
  have hUo := open_annulus_open (0:X) i; rewrite openE in hUo.
  have [d2 hd2 hball] := (metricType_numDomainType.nbhs_mdistP a (U i)).1 (hUo a (hFiU i a hai)).
  have hmin1 : Num.min d1 d2<=d1 by rewrite ge_min lexx.
  have hmin2 : Num.min d1 d2<=d2 by rewrite ge_min lexx orbT.
  exists (Num.min d1 d2); split; first by rewrite lt_min hd1 hd2.
  move=>b [i' _ hbi'] hba h.
  have hbU : U i b.
    apply: hball; rewrite /= inner_metric_distanceE (real_seminorm_subtract hN.1).
    exact: (lt_le_trans hba hmin2).
  have hii' : i' = i := open_annulus_disjoint (hFiU i' b hbi') hbU.
  rewrite hii' in hbi'.
  apply: hcd=>//; first exact: (hFiE i b hbi').
  exact: (lt_le_trans hba hmin1).
have hFrate : forall (rho : R) (j : nat), exists Q : nat, forall a, F a -> N a<=rho ->
    forall x, B x -> 0<N (x-a) -> N (x-a)<(Q.+1%:R)^-1 ->
    @ZN k (Dk x-Dk a-top_derivative_field a (x-a))<=(j.+1%:R)^-1*N (x-a).
  move=>rho j.
  exists (\max_(i<(Num.truncn rho).+1) q i j).
  move=>a [i _ hai] hrho x hx hp hs.
  have hiU : U i a := hFiU i a hai.
  have hNa : mdist (0:X) a=N a by rewrite inner_metric_distanceE sub0r inner_normN.
  have /andP [hi1 _] := hiU.
  have hrho0 : 0<=rho := le_trans (real_seminorm_nonnegative hN.1 a) hrho.
  have /andP [_ ht] := truncn_itv hrho0.
  have hi : (i<(Num.truncn rho).+1)%N.
    rewrite -(ltr_nat R); apply: (lt_trans hi1); rewrite hNa.
    exact: (le_lt_trans hrho ht).
  have hle : (q i j<=\max_(i'<(Num.truncn rho).+1) q i' j)%N :=
    @leq_bigmax _ (fun i' : 'I_(Num.truncn rho).+1=>q i' j) (Ordinal hi).
  have hQs : ((\max_(i'<(Num.truncn rho).+1) q i' j).+1%:R)^-1<=((q i j).+1%:R)^-1 :> R.
    by rewrite lef_pV2 ?posrE ?ltr0n // ler_nat; exact: hle.
  exact: (hrate i j a (hai.2 j I) x hx hp (lt_le_trans hs hQs)).
exists F, top_derivative_field; split.
- exact: hFc.
- exact: hFB.
- exact: hAF.
- exact: hFdiff.
- by split; [exact: hFcont|exact: hFrate].
Qed.
End GoodSet.
