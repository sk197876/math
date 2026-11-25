(** Federer (1969), 2.1.6(2), p. 59: the matrix U(b,a) from injections of
    proper initial segments into the predecessor cardinal. We follow the
    disjoint-column and null-row argument. Instead of estimating the
    cardinality of the exceptional pairs by aleph-zero times alpha, we show
    their projection null using the already proved Ulam null-cover property.
    A point outside this null exceptional set suffices when the total
    measure is nonzero. This changes the proof, not the theorem or its
    hypotheses. Federer's erratum p. 1, book p. 59 line 3, corrects a in
    alpha. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets functions cardinality reals constructive_ereal.
From Federer Require Import MeasureUP MeasureBasic MeasureSplit
  UlamCardinalUP UlamCountable UlamNullCover CardinalInjection
  CardinalSuccessorUP MeasureDisjointSupport.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope card_scope.
Local Open Scope ereal_scope.

(** Source for [ulam_small_prefix_measure_zero]: Federer
    2.1.6(2), p. 59, core matrix argument. If every predecessor
    set embeds in an Ulam set and every pair is comparable, a
    finite point-null measure with all subsets measurable vanishes.
    Only comparability is needed here; the later application obtains
    the predecessor bounds from the successor-cardinal specification. *)
Theorem ulam_small_prefix_measure_zero (R : realType) (I J : choiceType)
    (mu : set I -> \bar R) (hm : is_measure mu) (X : set I)
    (A : set J) (d : J) (r : rel I) :
  is_ulam_set R A ->
  (forall x y, X x -> X y -> r x y || r y x) ->
  (forall x, X x -> well_order_prefix X r x #<= A) ->
  mu X < +oo -> (forall B, B `<=` X -> measure_measurable mu B) ->
  (forall x, X x -> mu [set x] = 0) -> mu X = 0.
Proof.
move=> hu ht hp hf ha hz.
have hc x : exists f : I -> J, X x ->
  set_fun (well_order_prefix X r x) A f /\ set_inj (well_order_prefix X r x) f.
  case: (pselect (X x))=> hx.
  - have [f h] := cardinal_injection_with_default d (hp x hx); by exists f.
  - exists (fun _ => d)=> h; exfalso; exact: hx h.
pose f x := projT1 (cid (hc x)).
have hfx x : X x -> set_fun (well_order_prefix X r x) A (f x) /\
  set_inj (well_order_prefix X r x) (f x).
  exact: projT2 (cid (hc x)).
pose U b a : set I := [set x | X x /\ r b x /\ b <> x /\ f x b = a].
have hUX b a : U b a `<=` X by move=> x [hx _].
have hUm b a : measure_measurable mu (U b a) := ha _ (hUX b a).
have hUd a b c : X b -> X c -> b <> c -> U b a `&` U c a = set0.
  move=> hb hcx0 hne; apply/seteqP; split=> [x [[hx [hbx [hbn hfb]]] [_ [hcx [hcn hfc]]]]|x []].
  exfalso; apply: hne; apply: (hfx x hx).2.
  - apply/mem_set; by split=> //; split.
  - apply/mem_set; by split=> //; split.
  - by rewrite hfb hfc.
pose P a := X `&` [set b | 0 < mu (U b a)].
have hPc a : countable (P a).
  exact: (@measure_disjoint_positive_countable R I I mu hm X X (fun b => U b a)
    hf (fun b _ => hUX b a) (fun b _ => hUm b a) (hUd a)).
have hPX a : P a `<=` X by move=> x [hx _].
have hPz a : mu (P a) = 0.
  apply: (@measure_countable_null_singletons R I mu hm (P a) (hPc a))=> x hx.
  exact: hz x (hPX a x hx).
pose N := \bigcup_(a in A) P a.
have hNX : N `<=` X by move=> x [a _ hx]; exact: hPX a x hx.
have hNz : mu N = 0.
  apply: (@ulam_null_cover R I J mu hm A P hu).
  - exact: le_lt_trans (@measure_mono R I mu hm N X hNX) hf.
  - move=> B hB; apply: ha=> x hx; exact: hNX x (hB x hx).
  - by move=> a _; exact: hPz.
case: (pselect (exists b, X b /\ ~ N b))=> [[b [hb hn]]|hcovered]; last first.
  have hXN : X `<=` N.
    move=> x hx; apply: contrapT=> h; apply: hcovered; exists x; by split.
  apply/eqP; rewrite eq_le (measure_nonnegative hm) andbT.
  have h := @measure_mono R I mu hm X N hXN; by rewrite hNz in h.
have hUz a : A a -> mu (U b a) = 0.
  move=> haA; apply/eqP; rewrite eq_le (measure_nonnegative hm) andbT.
  apply: contrapT=> hne.
  have hpos : 0 < mu (U b a) by rewrite ltNge; apply/negP.
  apply: hn; exists a=> //; by split.
pose V := \bigcup_(a in A) U b a.
have hVX : V `<=` X by move=> x [a _ hx]; exact: hUX b a x hx.
have hVz : mu V = 0.
  apply: (@ulam_null_cover R I J mu hm A (U b) hu).
  - exact: le_lt_trans (@measure_mono R I mu hm V X hVX) hf.
  - move=> B hB; apply: ha=> x hx; exact: hVX x (hB x hx).
  - exact hUz.
have hpreX : well_order_prefix X r b `<=` X by move=> x [hx _].
have hprez : mu (well_order_prefix X r b) = 0.
  apply: (hu I mu _ hm (hp b hb)).
  - exact: le_lt_trans (@measure_mono R I mu hm _ X hpreX) hf.
  - move=> B hB; apply: ha=> x hx; exact: hpreX x (hB x hx).
  - move=> x hx; exact: hz x (hpreX x hx).
have hcover : X `<=` (well_order_prefix X r b `|` [set b]) `|` V.
  move=> x hx; case: (eqVneq x b)=> [he|hne].
  - left; by right.
  - have [hxb|hbx] := orP (ht x b hx hb).
    + left; left; split=> //; split=> //; exact/eqP.
    + right; exists (f x b).
      * apply: (hfx x hx).1; split=> //; split=> //.
        move=> he; move: hne; by rewrite he eqxx.
      * split=> //; split=> //; split=> //.
        move=> he; move: hne; by rewrite he eqxx.
have hbound := @measure_binary_cover R I mu hm X
  (well_order_prefix X r b `|` [set b]) V hcover.
have hbound2 := @measure_binary_cover R I mu hm (well_order_prefix X r b `|` [set b])
  (well_order_prefix X r b) [set b] (fun x hx => hx).
rewrite hprez (hz b hb) add0e in hbound2.
rewrite hVz adde0 in hbound.
apply/eqP; rewrite eq_le (measure_nonnegative hm) andbT.
exact: le_trans hbound hbound2.
Qed.
