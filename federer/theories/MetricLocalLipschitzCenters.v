(** Federer (1969), 3.1.9, p. 218: the closed sets
    of points with a common local growth bound. The neighborhood
    containment used in the printed proof is kept explicitly.
    Erratum p. 4 corrects book p. 218, line 12, to U(z,1/j). *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals topology lra.
From Federer Require Import MetricClosedBalls LipschitzUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

(** Source for [metric_local_lipschitz_centers]: the set C_j
    of Federer 3.1.9, p. 218, with M and r in
    place of j and 1/j. Each center belongs to B, its
    entire open r-ball lies in B, and the stated bound holds
    from that center to every point of that ball. *)
Definition metric_local_lipschitz_centers (R : realType) (X Y : metricType R)
    (B : set X) (f : X->Y) (M r : R) : set X :=
  [set z | B z /\ forall x, mdist z x<r ->
    B x /\ mdist (f x) (f z)<=M*mdist x z].

(** Source for [metric_local_lipschitz_centers_closed]: the
    closedness assertion and limiting argument for C_j in
    Federer 3.1.9, p. 218. We express the same
    limit using closure neighborhoods; no continuity of f
    on its whole domain is assumed. *)
Theorem metric_local_lipschitz_centers_closed (R : realType)
    (X Y : metricType R) (B : set X) (f : X->Y) (M r : R) :
  0<=M -> 0<r -> closed (metric_local_lipschitz_centers B f M r).
Proof.
move=> hM hr z hz.
have hminl (x y : R) : Num.min x y<=x by rewrite ge_min lexx.
have hminr (x y : R) : Num.min x y<=y by rewrite ge_min lexx orbT.
have hnear d (hd : 0<d) : exists w,
    metric_local_lipschitz_centers B f M r w /\ mdist z w<d.
  apply: hz.
  apply: (metricType_numDomainType.nbhs_mdistP z _).2.
  by exists d.
have [w0 [hw0 hzw0]] := hnear r hr.
have hw0z : mdist w0 z<r by rewrite metric_sym.
split; first exact: (hw0.2 z hw0z).1.
move=> x hx.
have hgap : 0<r-mdist z x by rewrite subr_gt0.
have hrad : 0<Num.min r (r-mdist z x) by rewrite lt_min hr hgap.
have [w [hw hzw]] := hnear (Num.min r (r-mdist z x)) hrad.
have hwz : mdist w z<r.
  rewrite metric_sym; exact: lt_le_trans hzw (hminl _ _).
have hwx : mdist w x<r.
  have hh := metric_triangle w z x.
  rewrite (metric_sym w z) in hh.
  have hs := lt_le_trans hzw (hminr _ _); lra.
split; first exact: (hw.2 x hwx).1.
rewrite leNgt; apply/negP=> hbad.
pose q := mdist (f x) (f z)-M*mdist x z.
have hq : 0<q by rewrite /q subr_gt0.
have hden : 0<4*(1+M).
  apply: mulr_gt0; first by rewrite ltr0n.
  lra.
pose d := Num.min r (Num.min (r-mdist z x) (q/(4*(1+M)))).
have hd : 0<d by rewrite /d !lt_min hr hgap divr_gt0.
have [v [hv hzv]] := hnear d hd.
have hvz : mdist v z<r.
  rewrite metric_sym; exact: lt_le_trans hzv (hminl _ _).
have hzvg : mdist z v<r-mdist z x.
  exact: lt_le_trans hzv (le_trans (hminr _ _) (hminl _ _)).
have hvx : mdist v x<r.
  have hh := metric_triangle v z x.
  rewrite (metric_sym v z) in hh; lra.
have hfx := (hv.2 x hvx).2.
have hfz := (hv.2 z hvz).2.
have htri := metric_triangle (f x) (f v) (f z).
rewrite (metric_sym (f v) (f z)) in htri.
have hsource := metric_triangle x z v.
have hsmall : mdist z v<q/(4*(1+M)).
  exact: lt_le_trans hzv (le_trans (hminr _ _) (hminr _ _)).
have hmul := hsmall.
rewrite (ltr_pdivlMr _ _ hden) in hmul.
have hdist0 := mdist_ge0 z v.
have hsourceM : M*mdist x v<=M*(mdist x z+mdist z v).
  apply: ler_wpM2l; [exact hM|exact hsource].
have hsum : mdist (f x) (f z)<=M*mdist x z+2*M*mdist z v.
  have hh := le_trans htri (lerD hfx hfz); nra.
rewrite /q in hmul.
nra.
Qed.

(** Source for [metric_local_lipschitz_centers_small_piece]:
    the restriction to C_(j,k) in Federer 3.1.9,
    p. 218, is Lipschitz when the piece has diameter
    smaller than the common radius. *)
Lemma metric_local_lipschitz_centers_small_piece (R : realType)
    (X Y : metricType R) (B E : set X) (f : X->Y) (M r : R) :
  0<M -> E `<=` metric_local_lipschitz_centers B f M r ->
  (forall x y, E x -> E y -> mdist x y<r) ->
  is_metric_lipschitz E f.
Proof.
move=> hM hE hd; exists M; split=> //; split; first exact: ltW hM.
move=> x y hx hy.
have h := ((hE y hy).2 x (hd y x hy hx)).2.
exact h.
Qed.
