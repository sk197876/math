(** Federer (1969), 2.2.16, p. 71: private metric-base construction of the
    open null cover H of the support complement. Balls are indexed by a
    dense centre and a positive reciprocal-integer radius. The product index
    is Ulam by 2.1.6(1), so the construction also covers finite and empty
    dense sets without an incorrect cardinal equality. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import MeasureUP MeasureBasic MeasureSupport MetricClosedBalls
  SeparableClosedCover ExtendedRealReciprocalBounds UlamCardinalUP UlamCountableProduct
  DenseUlamSupportCoverUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [dense_ulam_support_cover_exists]: direct
    existence of the family H in Federer 2.2.16,
    p. 71. Refine every open null neighborhood by
    a dense-centred ball, and retain exactly the null balls.
    Finiteness and Borel measurability are unnecessary for this
    cover construction; they enter the later null-union theorem. *)
Theorem dense_ulam_support_cover_exists (R : realType) (X : metricType R)
    (mu : set X -> \bar R) (hm : is_measure mu) (D : set X) :
  dense D -> is_ulam_set R D ->
  exists J : set (X * nat), exists U : X * nat -> set X,
    is_ulam_open_null_cover mu (~` measure_support mu) J U.
Proof.
move=> hd hu.
pose r n : R := (((n.+1)%:R)^-1)%R.
pose B (p : X * nat) := [set x | (mdist p.1 x < r p.2)%R].
have hB p : open (B p) := metric_open_ball_open p.1 (r p.2).
have hbasis V : open V -> forall x, V x ->
    exists p : X * nat, D p.1 /\ B p x /\ B p `<=` V.
  move=> hV x hx.
  have hnb : nbhs x V by rewrite openE in hV; exact: hV x hx.
  have [e he heB] := proj1 (metricType_numDomainType.nbhs_mdistP x V) hnb.
  have he2 : (0 < e/2)%R by rewrite divr_gt0 // ltr0n.
  have [n hn] := positive_reciprocal_nat_small he2.
  have hr : (0 < r n)%R by rewrite /r invr_gt0 ltr0n.
  have [c [hc hcx]] := metric_dense_point_near hd x hr.
  exists (c,n); split=> //; split.
  - rewrite /B /= metric_sym; exact hcx.
  - move=> y hy; apply: heB.
    have ht := le_lt_trans (metric_triangle x c y) (ltrD hcx hy).
    have hh := ltrD hn hn; rewrite -splitr in hh; exact: lt_trans ht hh.
pose J : set (X * nat) := [set p | D p.1 /\ mu (B p) = 0].
exists J, B; constructor.
- apply: (@ulam_set_downward R [the choiceType of (X * nat)%type] [the choiceType of (X * nat)%type]
    J (D `*` (@setT nat)) _ (@ulam_set_times_naturals R X D hu)).
  apply: subset_card_le=> p [hp _]; by split.
- move=> p hp; exact: hB p.
- by move=> p [_ hp].
- rewrite measure_support_formula setCK; apply/seteqP; split.
  + move=> x [p [hp hz] hx]; exists (B p)=> //; by split=> //; exact: hB p.
  + move=> x [V [hV hz] hx].
    have [p [hp [hpx hsub]]] := hbasis V hV x hx.
    have hzero : mu (B p) = 0.
      apply/eqP; rewrite eq_le (measure_nonnegative hm) andbT.
      have hh := @measure_mono R X mu hm (B p) V hsub; by rewrite hz in hh.
    exists p=> //; by split.
Qed.
