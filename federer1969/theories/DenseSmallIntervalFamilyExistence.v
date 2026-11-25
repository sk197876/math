(** Federer (1969), 3.2.33, p. 270: prove the
    dense open interval family's existence using a small open
    cover of a countable dense scalar set. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets cardinality constructive_ereal topology lra.
From Federer Require Import RealMetricBackground RealOpenIntervals RealLineSeparability CountableDefaultEnumeration
  LebesgueScalarMeasure ScalarLebesgueBallContext DerivationOpenSupersets MeasureUP MeasureBasic MeasureSplit
  DenseSmallIntervalFamilyUP OpenUnitIntervalNeighborhood.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [dense_small_interval_family_exists]: supporting
    the choice of U_j in Federer 3.2.33, p. 270.
    A countable dense set has a scalar Lebesgue-null measure.
    Cover it by an open set of length at most one quarter.
    Enumerated interior dense points have small interval neighborhoods
    in that cover. Their union is dense in (0,1), and
    the central closed half-interval proves its omitted length
    positive. The family is a local proved witness only. *)
Theorem dense_small_interval_family_exists (R:realType):
  exists a b:nat->R,is_dense_small_interval_family a b.
Proof.
have hm:=lebesgue_scalar_is_measure R.
have [D [hCount hDense]]:=real_line_countable_dense R.
have hNull:=scalar_lebesgue_countable_null hCount.
have hQuarter:(0<(1/4:R)) by rewrite divr_gt0 // ltr0n.
have [U [hU [hDU hMass]]]:=@derivation_measure_open_superset R
  (real_line_metric R) (@lebesgue_scalar_measure R) D (1/4)
  (scalar_lebesgue_derivation_class R) hQuarter.
rewrite hNull add0e in hMass.
pose T:=real_open_interval (0:R) 1.
have hTOpen:open T:=@real_open_interval_open R 0 1.
have hTNonempty:T!=set0:=real_open_interval_nonempty (@ltr01 R).
have [c0 [hc0 hDc0]]:=hDense T hTNonempty hTOpen.
have [e [hE hSurj]]:=countable_default_enumeration c0 hCount.
pose c j:R:=if pselect (T (e j)) then e j else c0.
have hC j:T (c j) /\U (c j).
  rewrite /c; case:pselect=>hTj.
  - split; first exact hTj.
    apply:hDU; case:(hE j)=>[hDj|->]; assumption.
  - split; first exact hc0; exact:hDU c0 hDc0.
have hLocal j:exists a b:R,0<a /\a<c j /\c j<b /\b<1 /\b-a<= 1/2 /\real_open_interval a b `<=` U.
  exact:(open_unit_interval_small_neighborhood hU (hC j).2 (hC j).1).
have hPairs j:exists p:R*R,0<p.1 /\p.1<c j /\c j<p.2 /\p.2<1 /\p.2-p.1<= 1/2 /\
    real_open_interval p.1 p.2 `<=` U.
  have [a [b h]]:=hLocal j; by exists (a,b).
have [p hP]:=choice hPairs.
pose a j:=(p j).1; pose b j:=(p j).2.
pose V:=\bigcup_j real_open_interval (a j) (b j).
have hVU:V `<=` U by move=>x [j _ hx]; exact:((hP j).2.2.2.2.2 x hx).
exists a,b; constructor.
- move=>j; split; first exact:(hP j).1.
  split; last exact:(hP j).2.2.2.1.
  exact:(lt_trans (hP j).2.1 (hP j).2.2.1).
- move=>j; exact:(hP j).2.2.2.2.1.
- move=>O hOpen [x [hTx hOx]].
  have hNonempty:T `&` O!=set0 by exists x.
  have [y [[hTy hOy] hDy]]:=hDense (T `&` O) hNonempty (openI hTOpen hOpen).
  have [j hj]:=hSurj y hDy.
  have hCy:c j= y by rewrite /c hj; case:pselect=>// hNot; exfalso; exact:hNot hTy.
  exists y; split; first exact hOy.
  exists j=>//; rewrite -hCy; split; [exact:(hP j).2.1|exact:(hP j).2.2.1].
- have hNonzero:lebesgue_scalar_measure (T `\` V)!= 0%E.
    apply/negP=>/eqP hZero.
    have hCover:`[(1/4:R),3/4] `<=` U `|` (T `\` V).
      move=>x hx; case:(pselect (U x))=>hUx; first by left.
      right; split.
      + change (0<x /\x<1); move:hx; rewrite /= in_itv /= =>/andP [h0 h1]; split; lra.
      + by move=>hVx; apply:hUx; exact:hVU x hVx.
    have hBound:=measure_binary_cover hm hCover.
    have hOrder:(1/4:R)<=3/4 by lra.
    rewrite (lebesgue_scalar_segment hOrder) hZero adde0 in hBound.
    have hBad:=le_trans hBound hMass.
    move:hBad; rewrite lee_fin; lra.
  rewrite lt_neqAle eq_sym hNonzero; exact:measure_nonnegative.
Qed.
