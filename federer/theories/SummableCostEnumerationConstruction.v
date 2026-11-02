(** Federer (1969), 2.10.22, pp. 184–185: private greedy construction of a
    positive-cost cover enumeration. Select a largest remaining positive
    cost and remove that generator. Finite covers terminate with inactive
    None slots. All downstream use is to be through the enumeration
    specification and its sealed existence witness. Source context and the
    cost-order proof route: SummablePositiveMaximum.v. *)
From mathcomp Require Import all_boot all_order all_algebra finmap boolp classical_sets cardinality
  reals constructive_ereal lra.
From Federer Require Import NonnegativeSum NonnegativeSumCountable SummablePositiveMaximum
  SummableCostEnumerationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Construction.
Variable R : realType.
Variable I : choiceType.
Variable G : set I.
Variable w : I -> R.
Variable M : R.
Hypothesis hw : forall x, G x -> 0<=w x.
Hypothesis hsum : (nonnegative_sum G (fun x=>(w x)%:E)<=M%:E)%E.

(** Source for [greedy_cost_remaining]: private remaining
    cover after finitely many selections, supporting
    2.10.22, p. 184. *)
Definition greedy_cost_remaining (F : {fset I}) : set I :=
  [set x | G x /\ x \notin F].

(** Source for [greedy_positive_cost_remaining]: private
    active remainder for the positive-cost extraction,
    2.10.22, pp. 184–185. *)
Definition greedy_positive_cost_remaining (F : {fset I}) : set I :=
  greedy_cost_remaining F `&` [set x | 0<w x].

(** Source for [greedy_remaining_maximum]: private
    existence of a largest positive remaining cost,
    supporting 2.10.22, pp. 184–185. *)
Lemma greedy_remaining_maximum F : greedy_positive_cost_remaining F !=set0 ->
  exists a, greedy_cost_remaining F a /\ 0<w a /\
    forall x, greedy_cost_remaining F x -> w x<=w a.
Proof.
move=> hne.
have hn x : greedy_cost_remaining F x -> 0<=w x by move=> [hx _]; exact: hw x hx.
have hsub : greedy_cost_remaining F `<=` G by move=> x [hx _].
have hb := le_trans (@nonnegative_sum_subset R I (greedy_cost_remaining F) G
  (fun x=>(w x)%:E) hsub) hsum.
exact: (@summable_positive_cost_maximum R I (greedy_cost_remaining F) w M hn hb hne).
Qed.

(** Source for [greedy_cost_step]: private choice of
    the largest positive remaining generator in
    2.10.22, pp. 184–185. None marks an
    empty positive remainder and has auxiliary cost zero. *)
Definition greedy_cost_step (F : {fset I}) : option I :=
  if pselect (greedy_positive_cost_remaining F !=set0) is left h
  then Some (sval (cid (greedy_remaining_maximum h))) else None.

(** Source for [greedy_cost_step_some]: private
    membership, freshness and dominance laws of one
    selection, supporting 2.10.22, pp. 184–185. *)
Lemma greedy_cost_step_some F x : greedy_cost_step F=Some x ->
  G x /\ x \notin F /\ 0<w x /\
    forall y, G y -> y \notin F -> w y<=w x.
Proof.
rewrite /greedy_cost_step; case: pselect=> [h|h]; last by [].
have [[ha haf] [hpos hmax]] := svalP (cid (greedy_remaining_maximum h)).
move=> [<-]; split=> //; split=> //; split=> // y hy hyF; exact: hmax y (conj hy hyF).
Qed.

(** Source for [greedy_cost_step_none]: private
    stopping law for finite positive-cost covers,
    supporting 2.10.22, pp. 184–185. *)
Lemma greedy_cost_step_none F : greedy_cost_step F=None ->
  forall x, G x -> 0<w x -> x \in F.
Proof.
rewrite /greedy_cost_step; case: pselect=> [h|h]; first by [].
move=> _ x hx hpos; apply/negPn/negP=> hnot.
apply: h; exists x; split; [by split|exact hpos].
Qed.

(** Source for [greedy_cost_used]: private finite
    set of already selected generators in the cover
    extraction of 2.10.22, pp. 184–185. *)
Fixpoint greedy_cost_used (n : nat) : {fset I} :=
  if n is k.+1 then
    if greedy_cost_step (greedy_cost_used k) is Some x then (x |` greedy_cost_used k)%fset
    else greedy_cost_used k
  else fset0.

(** Source for [greedy_cost_enumeration]: private
    natural sequence of positive-cost selections and
    inactive slots, supporting 2.10.22, pp. 184–185. *)
Definition greedy_cost_enumeration n := greedy_cost_step (greedy_cost_used n).

(** Source for [greedy_cost_used_trace]: private
    bookkeeping for the cover extraction in
    2.10.22, pp. 184–185. The finite used
    set contains exactly earlier active selections. *)
Lemma greedy_cost_used_trace n x : x \in greedy_cost_used n <->
  exists k, (k<n)%N /\ greedy_cost_enumeration k=Some x.
Proof.
elim: n=> [|n ih].
- split.
  + by rewrite /= inE.
  + move=> [k [hk _]]; by rewrite ltn0 in hk.
- rewrite /=; case hs: (greedy_cost_step (greedy_cost_used n))=> [a|].
  + split.
    * move=> /fset1UP [->|hx].
      - exists n; split; first exact: ltnSn.
        exact hs.
      - have [k [hk hku]] := (proj1 ih hx).
        exists k; split=> //; exact: ltn_trans hk (ltnSn n).
    * move=> [k [hk hku]].
      case: (ltnP k n)=> hkn.
      - exact: fset1Ur (proj2 ih (ex_intro _ k (conj hkn hku))).
      - have hkn' : k=n.
          apply/eqP; rewrite eqn_leq hkn andbT; by move: hk; rewrite ltnS.
        move: hku; rewrite hkn' /greedy_cost_enumeration hs=> [[<-]]; exact: fset1U1.
  + split.
    * move=> hx; have [k [hk hku]] := proj1 ih hx.
      exists k; split=> //; exact: ltn_trans hk (ltnSn n).
    * move=> [k [hk hku]].
      case: (ltnP k n)=> hkn.
      - exact: (proj2 ih (ex_intro _ k (conj hkn hku))).
      - have hkn' : k=n.
          apply/eqP; rewrite eqn_leq hkn andbT; by move: hk; rewrite ltnS.
        by move: hku; rewrite hkn' /greedy_cost_enumeration hs.
Qed.

(** Source for [greedy_cost_used_monotone]: private
    monotonicity of the selected finite sets,
    supporting 2.10.22, pp. 184–185. *)
Lemma greedy_cost_used_monotone n m x : (n<=m)%N ->
  x \in greedy_cost_used n -> x \in greedy_cost_used m.
Proof.
move=> hnm hx; have [k [hk hku]] := proj1 (greedy_cost_used_trace n x) hx.
apply: (proj2 (greedy_cost_used_trace m x)); exists k; split=> //.
exact: leq_trans hk hnm.
Qed.

(** Source for [greedy_cost_used_member]: private
    positivity and source membership of all selected
    generators, supporting 2.10.22, pp. 184–185. *)
Lemma greedy_cost_used_member n x : x \in greedy_cost_used n -> G x /\ 0<w x.
Proof.
move=> hx; have [k [hk hku]] := proj1 (greedy_cost_used_trace n x) hx.
have [hG [_ [hpos _]]] := greedy_cost_step_some hku; by split.
Qed.

(** Source for [greedy_cost_used_successor]: private
    finite-set recursion law for the cover selection
    in 2.10.22, pp. 184–185. *)
Lemma greedy_cost_used_successor n : greedy_cost_used n.+1=
  if greedy_cost_enumeration n is Some x then (x |` greedy_cost_used n)%fset
  else greedy_cost_used n.
Proof. by []. Qed.

(** Source for [greedy_cost_enumeration_injective]: private
    absence of repeated positive-cost generators,
    supporting 2.10.22, pp. 184–185. *)
Lemma greedy_cost_enumeration_injective n m x :
  greedy_cost_enumeration n=Some x -> greedy_cost_enumeration m=Some x -> n=m.
Proof.
move=> hn hm; case: (ltngtP n m)=> [hnm|hmn|he]; last exact he.
- have hxF := proj2 (greedy_cost_used_trace m x) (ex_intro _ n (conj hnm hn)).
  have hnot := (greedy_cost_step_some hm).2.1; by rewrite hxF in hnot.
- have hxF := proj2 (greedy_cost_used_trace n x) (ex_intro _ m (conj hmn hm)).
  have hnot := (greedy_cost_step_some hn).2.1; by rewrite hxF in hnot.
Qed.

(** Source for [greedy_earlier_cost_dominates]: private
    decreasing-cost comparison for the extracted cover,
    supporting 2.10.22, pp. 184–185. A later
    active generator was available at every earlier step. *)
Lemma greedy_earlier_cost_dominates k n x : (k<n)%N ->
  greedy_cost_enumeration n=Some x ->
  exists y, greedy_cost_enumeration k=Some y /\ w x<=w y.
Proof.
move=> hkn hnx.
have [hG [hnotn [hpos hmax]]] := greedy_cost_step_some hnx.
have hnotk : x \notin greedy_cost_used k.
  apply/negP=> hxk.
  have hxn := greedy_cost_used_monotone (ltnW hkn) hxk.
  by rewrite hxn in hnotn.
case hky: (greedy_cost_enumeration k)=> [y|].
- exists y; split=> //.
  exact: (greedy_cost_step_some hky).2.2.2 x hG hnotk.
- have hxk : x \in greedy_cost_used k := greedy_cost_step_none hky hG hpos.
  by rewrite hxk in hnotk.
Qed.

(** Source for [greedy_active_prefix_cardinality]: private
    number of distinct selections preceding an active
    position, supporting 2.10.22, pp. 184–185. *)
Lemma greedy_active_prefix_cardinality n x : greedy_cost_enumeration n=Some x ->
  #|` greedy_cost_used n.+1|=n.+1.
Proof.
elim: n x=> [|n ih] x hx.
- by rewrite greedy_cost_used_successor hx cardfsU1 inE /=.
- have [y [hy hwy]] := greedy_earlier_cost_dominates (ltnSn n) hx.
  have hcard := ih y hy.
  have hnot := (greedy_cost_step_some hx).2.1.
  by rewrite greedy_cost_used_successor hx cardfsU1 hnot hcard add1n.
Qed.

(** Source for [greedy_cost_budget_nonnegative]: private
    nonnegativity of the finite cover budget in
    2.10.22, p. 184, from its summation bound. *)
Lemma greedy_cost_budget_nonnegative : 0<=M.
Proof.
have hh := le_trans (nonnegative_sum_nonnegative G (fun x=>(w x)%:E)) hsum.
by rewrite lee_fin in hh.
Qed.

(** Source for [greedy_cost_uniform_position_bound]: private
    uniform late-cost bound for the cover array in
    2.10.22, pp. 184–185. Every earlier chosen
    cost dominates the current cost, so its position
    times its cost is bounded by the whole budget. *)
Lemma greedy_cost_uniform_position_bound n :
  n.+1%:R*optional_generator_cost w (greedy_cost_enumeration n)<=M.
Proof.
case hn: (greedy_cost_enumeration n)=> [x|].
- have hcard := greedy_active_prefix_cardinality hn.
  have hF y (hy : y \in greedy_cost_used n.+1) : G y /\ ((w x)%:E<=(w y)%:E)%E.
    split; first exact: (greedy_cost_used_member hy).1.
    have [k [hk hky]] := proj1 (greedy_cost_used_trace n.+1 y) hy.
    change (is_true (w x<=w y)).
    case: (ltnP k n)=> hkn.
    + have [z [hkz hwxz]] := greedy_earlier_cost_dominates hkn hn.
      have heq : z=y by move: hkz; rewrite hky; by case.
      by rewrite -heq.
    + have heq : k=n.
        apply/eqP; rewrite eqn_leq hkn andbT; by move: hk; rewrite ltnS.
      move: hky; rewrite heq hn=> [[<-]]; exact: lexx.
  have hb := @nonnegative_finite_threshold_bound R I G (fun y=>(w y)%:E)
    (greedy_cost_used n.+1) (w x) hF.
  have hh := le_trans hb hsum; rewrite hcard lee_fin in hh; exact hh.
- rewrite /optional_generator_cost mulr0; exact: greedy_cost_budget_nonnegative.
Qed.

(** Source for [greedy_remaining_cost_position_bound]: private
    cost bound for every still available positive
    generator, supporting 2.10.22, pp. 184–185. *)
Lemma greedy_remaining_cost_position_bound n x : G x -> 0<w x ->
  x \notin greedy_cost_used n -> n.+1%:R*w x<=M.
Proof.
move=> hx hpos hnot; case hn: (greedy_cost_enumeration n)=> [y|].
- have hxy := (greedy_cost_step_some hn).2.2.2 x hx hnot.
  have hN0 : (0<=n.+1%:R :> R) by rewrite ler0n.
  have hmul := ler_wpM2l hN0 hxy.
  have hb := greedy_cost_uniform_position_bound n; rewrite hn /optional_generator_cost in hb.
  exact: le_trans hmul hb.
- have hmem : x \in greedy_cost_used n := greedy_cost_step_none hn hx hpos.
  by rewrite hmem in hnot.
Qed.

(** Source for [greedy_positive_cost_covered]: private
    exhaustion of all positive-cost generators in
    2.10.22, p. 184. A permanently remaining
    positive value would violate the finite budget
    at a sufficiently large natural position. *)
Lemma greedy_positive_cost_covered x : G x -> 0<w x ->
  exists n, greedy_cost_enumeration n=Some x.
Proof.
move=> hx hpos; apply: contrapT=> hnone.
have hnot n : x \notin greedy_cost_used n.
  apply/negP=> hused.
  have [k [hk hku]] := proj1 (greedy_cost_used_trace n x) hused.
  apply: hnone; by exists k.
have hbound n := greedy_remaining_cost_position_bound hx hpos (hnot n).
have hM := greedy_cost_budget_nonnegative.
have hratio : 0<=M/w x by rewrite divr_ge0 //; exact: ltW hpos.
pose N := Num.bound (M/w x).
have hlarge : M<N%:R*w x.
  rewrite -ltr_pdivrMr //; exact: archi_boundP hratio.
have hidx : (N%:R<=N.+1%:R :> R) by rewrite ler_nat.
have hmul := ler_wpM2r (ltW hpos) hidx.
have hh := lt_le_trans hlarge (le_trans hmul (hbound N)); by rewrite ltxx in hh.
Qed.
End Construction.

(** Source for [summable_cost_enumeration_exists]: existence
    of the cost-ordered optional cover enumeration
    supporting 2.10.22, pp. 184–185. The
    construction is private; its four selection laws
    are the complete downstream interface. *)
Theorem summable_cost_enumeration_exists (R : realType) (I : choiceType)
    (G : set I) (w : I -> R) (M : R) :
  (forall x, G x -> 0<=w x) -> (nonnegative_sum G (fun x=>(w x)%:E)<=M%:E)%E ->
  exists u, is_summable_cost_enumeration G w M u.
Proof.
move=> hw hs.
exists (@greedy_cost_enumeration R I G w M hw hs); constructor.
- move=> n x hx.
  have [hG [_ [hpos _]]] := @greedy_cost_step_some R I G w M hw hs
    (@greedy_cost_used R I G w M hw hs n) x hx.
  by split.
- move=> n m x hn hm; exact: (@greedy_cost_enumeration_injective R I G w M hw hs n m x hn hm).
- move=> x hx hpos; exact: (@greedy_positive_cost_covered R I G w M hw hs x hx hpos).
- move=> n; exact: (@greedy_cost_uniform_position_bound R I G w M hw hs n).
Qed.
