(** A project counterexample under review for the spherical parenthesis
    in Federer 2.10.11, p. 176. The binary prefix distance is specified
    independently of a witness. This module proves only metric facts. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets
  reals topology lra.
From Federer Require Import BinarySequenceCylinders DyadicScaleBounds.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [binary_common_prefix]: supporting finite-prefix
    relation for a project test of Federer 2.10.11, p. 176.
    This is an additional metric example, not a book definition. *)
Definition binary_common_prefix n (x y:binary_sequence_space) :=
  forall k, (k<n)%N -> x k=y k.

(** Source for [binary_first_difference]: supporting first differing
    coordinate for the project test of Federer 2.10.11, p. 176. *)
Definition binary_first_difference (x y:binary_sequence_space) j :=
  x j != y j /\ binary_common_prefix j x y.

(** Source for [binary_first_difference_exists]: the missing Boolean
    coordinate connection for the well-order argument already used in
    2.2.8, pp. 64–65; supporting the project test of 2.10.11, p. 176. *)
Lemma binary_first_difference_exists (x y:binary_sequence_space) :
  x != y -> exists j, binary_first_difference x y j.
Proof.
move=> hxy.
have hex : exists j, x j != y j.
  case: (pselect (exists j, x j != y j))=> h; first exact h.
  exfalso; have he:x=y.
    apply:funext=> j; case:(eqVneq (x j) (y j))=> // hn.
    exfalso; apply:h; by exists j.
  by move:hxy; rewrite he eqxx.
have [j hj hmin]:=ex_minnP hex.
exists j; split=> // k hk; apply/eqP; apply/negPn/negP=> hn.
have h:=leq_ltn_trans (hmin k hn) hk; by rewrite ltnn in h.
Qed.

(** Source for [binary_first_difference_unique]: uniqueness of the
    common-prefix length, supporting the project metric example for
    Federer 2.10.11, p. 176. *)
Lemma binary_first_difference_unique (x y:binary_sequence_space) i j :
  binary_first_difference x y i -> binary_first_difference x y j -> i=j.
Proof.
move=> [hi hpi] [hj hpj]; apply/eqP; rewrite eqn_leq; apply/andP; split.
- rewrite leqNgt; apply/negP=> hji.
  by move:hj; rewrite (hpi j hji) eqxx.
- rewrite leqNgt; apply/negP=> hij.
  by move:hi; rewrite (hpj i hij) eqxx.
Qed.

(** Source for [is_binary_prefix_distance]: independent distance
    specification for the project test of Federer 2.10.11, p. 176.
    Distinct sequences at first difference j have distance 2^(-j).
    No metric or measure conclusion is included as an assumption. *)
Record is_binary_prefix_distance (R:realType)
    (d:binary_sequence_space->binary_sequence_space->R):Prop := {
  (** Source for [binary_prefix_distance_self]: zero self-distance in
      the project test metric for Federer 2.10.11, p. 176. *)
  binary_prefix_distance_self:forall x,d x x= 0;
  (** Source for [binary_prefix_distance_first]: exact dyadic first-
      difference value in the project test of Federer 2.10.11, p. 176. *)
  binary_prefix_distance_first:forall x y j,
    binary_first_difference x y j -> d x y=((2^j)%N)%:R^-1
}.

(** Source for [binary_prefix_distance_nonnegative]: metric background
    for the project test of Federer 2.10.11, p. 176. *)
Lemma binary_prefix_distance_nonnegative (R:realType) (d:binary_sequence_space->binary_sequence_space->R)
    (hd:is_binary_prefix_distance d) x y : 0<=d x y.
Proof.
case:(eqVneq x y)=> [->|hn]; first by rewrite (binary_prefix_distance_self hd).
have [j hj]:=binary_first_difference_exists hn.
rewrite (binary_prefix_distance_first hd hj); exact:ltW (dyadic_side_positive R j).
Qed.

(** Source for [binary_prefix_distance_separates]: zero distance
    forces equality in the supporting project test of Federer
    2.10.11, p. 176. *)
Lemma binary_prefix_distance_separates (R:realType) (d:binary_sequence_space->binary_sequence_space->R)
    (hd:is_binary_prefix_distance d) x y : d x y= 0 -> x=y.
Proof.
move=> hz; case:(eqVneq x y)=> // hn.
have [j hj]:=binary_first_difference_exists hn.
have h:=dyadic_side_positive R j.
by rewrite -(binary_prefix_distance_first hd hj) hz ltxx in h.
Qed.

(** Source for [binary_prefix_distance_symmetric]: metric background
    for the project test of Federer 2.10.11, p. 176. *)
Lemma binary_prefix_distance_symmetric (R:realType) (d:binary_sequence_space->binary_sequence_space->R)
    (hd:is_binary_prefix_distance d) x y : d x y=d y x.
Proof.
case:(eqVneq x y)=> [->|hn]; first by [].
have [j hj]:=binary_first_difference_exists hn.
have hj':binary_first_difference y x j.
  split; first by rewrite eq_sym;exact:hj.1.
  move=> k hk; exact:esym (hj.2 k hk).
by rewrite (binary_prefix_distance_first hd hj) (binary_prefix_distance_first hd hj').
Qed.

(** Source for [binary_prefix_distance_prefix_bound]: agreeing on
    n initial coordinates bounds distance by 2^(-n). This is the
    missing ultrametric conversion used by the project test of
    Federer 2.10.11, p. 176. *)
Lemma binary_prefix_distance_prefix_bound (R:realType) (d:binary_sequence_space->binary_sequence_space->R)
    (hd:is_binary_prefix_distance d) n x y :
  binary_common_prefix n x y -> d x y<=((2^n)%N)%:R^-1.
Proof.
move=> hprefix; case:(eqVneq x y)=> [->|hn].
- rewrite (binary_prefix_distance_self hd); exact:ltW (dyadic_side_positive R n).
have [j hj]:=binary_first_difference_exists hn.
have hnj:(n<=j)%N.
  rewrite leqNgt;apply/negP=> hjn.
  by move:hj.1;rewrite (hprefix j hjn) eqxx.
rewrite (binary_prefix_distance_first hd hj);exact:dyadic_side_antitone hnj.
Qed.

(** Source for [binary_prefix_distance_triangle]: the ordinary
    triangle law follows from the common-prefix bound and the first
    differences. Supporting metric background for the project test
    of Federer 2.10.11, p. 176. *)
Lemma binary_prefix_distance_triangle (R:realType) (d:binary_sequence_space->binary_sequence_space->R)
    (hd:is_binary_prefix_distance d) x y z : d x z<=d x y+d y z.
Proof.
case:(eqVneq x y)=> [->|hxy]; first by rewrite (binary_prefix_distance_self hd) add0r.
case:(eqVneq y z)=> [->|hyz]; first by rewrite (binary_prefix_distance_self hd) addr0.
have [i hi]:=binary_first_difference_exists hxy.
have [j hj]:=binary_first_difference_exists hyz.
have hprefix:binary_common_prefix (minn i j) x z.
  move=> k hk;rewrite (hi.2 k (leq_trans hk (geq_minl i j))).
  exact:hj.2 k (leq_trans hk (geq_minr i j)).
have h:=binary_prefix_distance_prefix_bound hd hprefix.
rewrite (binary_prefix_distance_first hd hi) (binary_prefix_distance_first hd hj).
case:(leqP i j)=> hij.
- rewrite (minn_idPl hij) in h.
  apply:le_trans h _;rewrite lerDl;exact:ltW (dyadic_side_positive R j).
- have hji:=ltnW hij;rewrite (minn_idPr hji) in h.
  apply:le_trans h _;rewrite lerDr;exact:ltW (dyadic_side_positive R i).
Qed.
