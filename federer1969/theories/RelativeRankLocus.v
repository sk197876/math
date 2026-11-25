(** Federer (1969), 3.2.33, p. 270: the exact
    intrinsic rank stratum S. Specify exact finite image
    dimension by its independent upper-dimension thresholds. *)
From mathcomp Require Import all_boot all_order all_algebra reals boolp classical_sets.
From Federer Require Import Hom GrassmannAbbreviations RelativeLowImageLocus
  PartialImageDimensionUP LinearRankUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [relative_rank_locus]: S={x:dim im Df(x)=mu}
    in Federer 3.2.33, p. 270. Exact dimension
    means the actual relative image has dimension at most
    mu and has no strictly smaller natural dimension bound.
    This abstract specification includes mu=0 and selects
    neither a basis nor an ambient differential. *)
Definition relative_rank_locus (R:realType) n v mu
    (W:set (R_n R n)) (F:R_n R n->R_n R v):set (R_n R n):=
  relative_low_image_locus mu W F `&`
    [set x|forall r,(r<mu)%N ->~relative_low_image_locus r W F x].

(** Source for [relative_low_image_locus_monotone]: upper
    dimension bounds in the description of S, Federer
    3.2.33, p. 270. The same actual image space
    and relative differential witness satisfy the larger bound. *)
Lemma relative_low_image_locus_monotone (R:realType) n v r s
    (W:set (R_n R n)) (F:R_n R n->R_n R v):
  (r<=s)%N ->relative_low_image_locus r W F `<=` relative_low_image_locus s W F.
Proof.
move=>hrs x [hx [d [hD [q [P [hqr hRange]]]]]].
split; first exact hx; exists d; split; first exact hD.
exists q,P; split; last exact hRange; exact:leq_trans hqr hrs.
Qed.

(** Source for [relative_rank_locus_coordinate_iff]: S is
    exactly the coordinate derivative's rank-mu locus,
    Federer 3.2.33, p. 270. The already-proved
    image-threshold equivalence and unique actual linear
    rank prove this specification, including degree zero. *)
Lemma relative_rank_locus_coordinate_iff (R:realType) n m v mu
    (W:set (R_n R n)) (F:R_n R n->R_n R v) x
    (L:Hom (R_n R m) (R_n R v)):
  (forall q,relative_low_image_locus q W F x <->
    exists r,has_linear_rank L r /\(r<=q)%N) ->
  (relative_rank_locus mu W F x <->has_linear_rank L mu).
Proof.
move=>hThreshold; split.
- move=>[hLow hNoSmaller]; have [r [hRank hr]]:=(hThreshold mu).1 hLow.
  have hMu:(mu<=r)%N.
    rewrite leqNgt; apply/negP=>hLess; apply:(hNoSmaller r hLess).
    apply:(hThreshold r).2; exists r; by split; [exact hRank|exact:leqnn].
  have he:r=mu by apply/eqP; rewrite eqn_leq hr hMu.
  by rewrite -he.
- move=>hRank; split.
  + apply:(hThreshold mu).2; exists mu; by split; [exact hRank|exact:leqnn].
  + move=>r hr hLow; have [s [hS hs]]:=(hThreshold r).1 hLow.
    have he:mu=s:=linear_rank_unique hRank hS.
    rewrite -he in hs.
    by have:=leq_ltn_trans hs hr; rewrite ltnn.
Qed.
