(** Federer (1969), 2.5.16, p. 110: for any metric space Y one may consider
    the Banach space E of all bounded real valued continuous functions on Y
    with the norm v(f) = sup im |f|, choose any base point eta in Y, and
    construct the isometric embedding F : Y -> E, F(y)(w) = p(y, w) - p(eta,
    w) for y, w in Y. The embedding, its boundedness, continuity and
    isometry are proved directly; the Banach space structure of E is not
    constructed here. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology normedtype.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section BoundedContinuousEmbedding.
Variable R : realType.
Variable Y : metricType R.

(** Source for [bounded_continuous_functions]: the set E of all bounded
    real valued continuous functions on Y, Federer 2.5.16, p. 110. *)
Definition bounded_continuous_functions : set (Y -> R) :=
  [set f : Y -> R | continuous f /\ exists M : R, forall w, `|f w| <= M].

(** Source for [uniform_distance_values]: the set of values |f(w) - h(w)|
    whose supremum is v(f - h), Federer 2.5.16, p. 110. *)
Definition uniform_distance_values (f h : Y -> R) : set R := [set `|f w - h w| | w in [set: Y]].

Variable eta : Y.

(** Source for [metric_embedding]: the map F of Federer 2.5.16, p. 110,
    F(y)(w) = p(y, w) - p(eta, w). *)
Definition metric_embedding (y : Y) : Y -> R := fun w => mdist y w - mdist eta w.

(** Source for [metric_embedding_difference]: the pointwise identity
    F(y)(w) - F(y')(w) = p(y, w) - p(y', w), Federer 2.5.16, p. 110. *)
Lemma metric_embedding_difference (y y' w : Y) :
  metric_embedding y w - metric_embedding y' w = mdist y w - mdist y' w.
Proof. by rewrite /metric_embedding opprB addrA addrNK. Qed.

(** Source for [mdist_difference_le]: supporting inequality
    |p(y, w) - p(y', w)| <= p(y, y'), the triangle inequality of
    Federer 2.5.16, p. 110. *)
Lemma mdist_difference_le (y y' w : Y) : `|mdist y w - mdist y' w| <= mdist y y'.
Proof.
rewrite ler_distl; apply/andP; split.
- by rewrite lerBlDr addrC [mdist y y']metric_sym; exact: (metric_triangle y' y w).
- by rewrite addrC; exact: (metric_triangle y y' w).
Qed.

(** Source for [metric_embedding_bounded]: F(y) is bounded by
    p(y, eta), Federer 2.5.16, p. 110. *)
Lemma metric_embedding_bounded (y w : Y) : `|metric_embedding y w| <= mdist y eta.
Proof. exact: mdist_difference_le. Qed.

(** Source for [metric_embedding_lipschitz]: F(y) is Lipschitzian in w
    with constant 2, supporting the continuity of F(y) in Federer
    2.5.16, p. 110. *)
Lemma metric_embedding_lipschitz (y w w' : Y) :
  `|metric_embedding y w - metric_embedding y w'| <= 2 * mdist w w'.
Proof.
rewrite /metric_embedding opprB addrACA [- mdist eta w + _]addrC addrACA mulr_natl mulr2n.
apply: le_trans (ler_normD _ _) _; apply: lerD.
- by rewrite [mdist y w]metric_sym [mdist y w']metric_sym; exact: mdist_difference_le.
- rewrite [mdist eta w']metric_sym [mdist eta w]metric_sym [mdist w w']metric_sym.
  exact: mdist_difference_le.
Qed.

(** Source for [metric_embedding_continuous]: F(y) is continuous,
    Federer 2.5.16, p. 110. *)
Lemma metric_embedding_continuous (y : Y) : continuous (metric_embedding y).
Proof.
move=> w; apply/cvg_ballP=> e he.
have he2 : 0 < e / 2 by rewrite divr_gt0 ?ltr0n.
have hnear : \forall w' \near w, mdist w w' < e / 2.
  by have := nbhsx_ballx w (e / 2) he2; apply: filterS=> w' /=; rewrite ballEmdist.
near=> w'; rewrite /ball /=.
apply: le_lt_trans (metric_embedding_lipschitz y w w') _.
rewrite mulrC -ltr_pdivlMr ?ltr0n //.
by near: w'.
Unshelve. all: end_near.
Qed.

(** Source for [metric_embedding_member]: F(y) belongs to E, Federer
    2.5.16, p. 110. *)
Lemma metric_embedding_member (y : Y) : bounded_continuous_functions (metric_embedding y).
Proof.
split; first exact: metric_embedding_continuous.
by exists (mdist y eta)=> w; exact: metric_embedding_bounded.
Qed.

(** Source for [metric_embedding_distance_le]: |F(y)(w) - F(y')(w)| is
    at most p(y, y'), half of the isometry of Federer 2.5.16, p. 110. *)
Lemma metric_embedding_distance_le (y y' w : Y) :
  `|metric_embedding y w - metric_embedding y' w| <= mdist y y'.
Proof. by rewrite metric_embedding_difference; exact: mdist_difference_le. Qed.

(** Source for [metric_embedding_distance_attained]: the bound p(y, y')
    is attained at w = y', Federer 2.5.16, p. 110. *)
Lemma metric_embedding_distance_attained (y y' : Y) :
  `|metric_embedding y y' - metric_embedding y' y'| = mdist y y'.
Proof. by rewrite metric_embedding_difference mdistxx subr0 ger0_norm ?mdist_ge0. Qed.

(** Source for [metric_embedding_isometric]: F is an isometric
    embedding, Federer 2.5.16, p. 110: v(F(y) - F(y')) = p(y, y'). *)
Theorem metric_embedding_isometric (y y' : Y) :
  sup (uniform_distance_values (metric_embedding y) (metric_embedding y')) = mdist y y'.
Proof.
have hne : uniform_distance_values (metric_embedding y) (metric_embedding y') !=set0.
  by exists `|metric_embedding y y' - metric_embedding y' y'|, y'.
have hub : ubound (uniform_distance_values (metric_embedding y) (metric_embedding y')) (mdist y y').
  by move=> _ [w _ <-]; exact: metric_embedding_distance_le.
apply/le_anti/andP; split; first exact: ge_sup.
rewrite -(metric_embedding_distance_attained y y').
by apply: sup_upper_bound; [split=> //; exists (mdist y y')|exists y'].
Qed.

End BoundedContinuousEmbedding.
