(** General metric probability support for the expanded continuity
    argument of Federer (1969), 3.2.45, p. 279. *)
From mathcomp Require Import all_boot all_order all_algebra finmap reals boolp classical_sets cardinality
  constructive_ereal topology lra.
From Federer Require Import CoveringFamilyUP MetricClosedBalls FinitePositiveBallCover FiniteRealMaximum
  MeasureUP MeasureBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [compact_full_support_probability_ball_floor]: an
    expanded helper for the exponent infinity endpoint in Federer
    3.2.45, p. 279. On a compact metric probability space with
    full support, every fixed positive-radius open ball has mass
    bounded below by one positive real constant. The existing finite
    ball cover and finite minimum prove the assertion; no uniform
    mass bound is an additional measure assumption. *)
Theorem compact_full_support_probability_ball_floor (R : realType) (X : metricType R)
    (mu : set X -> \bar R) (hMu : is_measure mu) :
  compact [set: X] -> mu setT = 1 ->
  (forall U : set X, open U -> U !=set0 -> 0 < mu U) ->
  forall r : R, (0 < r)%R -> exists a : R, (0 < a)%R /\
    forall x, a%:E <= mu (@metric_open_ball R X x r).
Proof.
move=> hCompact hTotal hSupport r hr.
case: (pselect (exists x : X, True))=> [[x0 _]|hEmpty].
- have hr2 : (0 < r/2)%R by lra.
  have [N [p [_ hCover]]] := @finite_positive_ball_cover R X x0 setT
    (fun _ => (r/2)%R) hCompact (fun _ _ => hr2).
  pose B (i : 'I_N) := @metric_open_ball R X (p i) (r/2)%R.
  pose b (i : 'I_N) : R := fine (mu (B i)).
  have hValue i : mu (B i) = (b i)%:E.
    symmetry; apply: fineK.
    rewrite (ge0_fin_numE (measure_nonnegative hMu _)).
    have hBound : mu (B i) <= 1.
      have h := @measure_mono R X mu hMu (B i) setT (subsetT _).
      by rewrite hTotal in h.
    exact: le_lt_trans hBound (ltry (1 : R)).
  have hPositive i : (0 < b i)%R.
    have hOpen : open (B i) := @metric_open_ball_open R X (p i) (r/2)%R.
    have hNE : B i !=set0.
      exists (p i); by rewrite /B /metric_open_ball /= mdistxx.
    have h := hSupport (B i) hOpen hNE.
    by rewrite hValue lte_fin in h.
  have hIndexNonempty : [set: 'I_N] !=set0.
    have [j hJ _] := hCover x0 I.
    by exists (Ordinal hJ).
  have [i0 [_ hMinimum]] := @finite_nonempty_real_maximum R [the choiceType of 'I_N]
    setT (fun i => (-b i)%R) (@finite_finset [the finType of 'I_N] setT) hIndexNonempty.
  exists (b i0); split; first exact: hPositive.
  move=> x; have [j hJ hX] := hCover x I.
  pose i : 'I_N := Ordinal hJ.
  have hLower : (b i0 <= b i)%R.
    have h := hMinimum i I; by rewrite lerN2 in h.
  have hContain : B i `<=` @metric_open_ball R X x r.
    move=> z hZ.
    have hXSmall : (mdist (p i) x < r/2)%R := hX.
    have hZSmall : (mdist (p i) z < r/2)%R := hZ.
    change (is_true (mdist x z < r)%R).
    have hTriangle := metric_triangle x (p i) z.
    rewrite (metric_sym x (p i)) in hTriangle; lra.
  apply: le_trans (lee_tofin hLower) _.
  rewrite -hValue; exact: (@measure_mono R X mu hMu (B i) _ hContain).
- exists 1%R; split; first exact: ltr01.
  move=> x; exfalso; apply: hEmpty; by exists x.
Qed.
