(** Federer (1969), 2.2.6, p. 63, positive-integer coordinate distance
    |m-n|/(1+|m-n|). A positive integer is encoded by a natural n
    representing n+1; shifting both coordinates preserves their difference.
    This convention is explicit and keeps zero-based sequence indexing
    separate from the book's positive indices. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import BoundedDistanceScalar.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [positive_integer_distance]: Federer 2.2.6,
    p. 63, the bounded coordinate distance; the encoded positive
    integers are m+1 and n+1, whose difference is m-n. This scalar
    construction supplies a witness for the sequence metric. *)
Definition positive_integer_distance (R : realType) (m n : nat) : R :=
  bounded_distance_scalar `|m%:R - n%:R|.
Arguments positive_integer_distance {R} m n.

(** Source for [positive_integer_distance_formula]: Federer
    2.2.6, p. 63, exact agreement with the printed positive-integer
    formula after the natural-number encoding. *)
Lemma positive_integer_distance_formula (R : realType) (m n : nat) :
  @positive_integer_distance R m n =
    `|m.+1%:R - n.+1%:R| / (1 + `|m.+1%:R - n.+1%:R|).
Proof.
rewrite /positive_integer_distance /bounded_distance_scalar -(@natr1 R m) -(@natr1 R n).
by rewrite (addrC (n%:R : R) 1) addrKA.
Qed.

(** Source for [positive_integer_distance_nonnegative]: Federer
    2.2.6, p. 63, supporting nonnegativity of the coordinate metric. *)
Lemma positive_integer_distance_nonnegative (R : realType) m n :
  0 <= @positive_integer_distance R m n.
Proof. exact: bounded_distance_scalar_nonnegative (normr_ge0 _). Qed.

(** Source for [positive_integer_distance_lt_one]: Federer
    2.2.6, p. 63, supporting uniform upper bound for the
    coordinate metric, needed to control weighted tails. *)
Lemma positive_integer_distance_lt_one (R : realType) m n :
  @positive_integer_distance R m n < 1.
Proof. exact: bounded_distance_scalar_lt_one (normr_ge0 _). Qed.

(** Source for [positive_integer_distance_self]: Federer
    2.2.6, p. 63, coordinate distance from a positive integer
    to itself is zero. *)
Lemma positive_integer_distance_self (R : realType) m :
  @positive_integer_distance R m m = 0.
Proof. by rewrite /positive_integer_distance subrr normr0 bounded_distance_scalar_zero. Qed.

(** Source for [positive_integer_distance_separates]: Federer
    2.2.6, p. 63, supporting separation of distinct coordinates. *)
Lemma positive_integer_distance_separates (R : realType) m n :
  @positive_integer_distance R m n = 0 -> m = n.
Proof.
move=> /eqP; rewrite /positive_integer_distance bounded_distance_scalar_eq_zero ?normr_ge0 //.
by rewrite normr_eq0 subr_eq0 eqr_nat=> /eqP.
Qed.

(** Source for [positive_integer_distance_symmetry]: Federer
    2.2.6, p. 63, supporting symmetry of the bounded coordinate distance. *)
Lemma positive_integer_distance_symmetry (R : realType) m n :
  @positive_integer_distance R m n = positive_integer_distance n m.
Proof. by rewrite /positive_integer_distance -[m%:R - n%:R]opprB normrN. Qed.

(** Source for [positive_integer_distance_triangle]: Federer 2.2.6, p. 63,
    supporting triangle inequality for each coordinate metric. we use the
    locally proved monotonicity and subadditivity of the bounded transform. *)
Lemma positive_integer_distance_triangle (R : realType) m n k :
  @positive_integer_distance R m k <= positive_integer_distance m n + positive_integer_distance n k.
Proof.
rewrite /positive_integer_distance.
apply: le_trans _ (bounded_distance_scalar_subadditive (normr_ge0 _) (normr_ge0 _)).
apply: bounded_distance_scalar_monotone; first exact: normr_ge0.
have he : (m%:R - k%:R : R) = (m%:R - n%:R) + (n%:R - k%:R).
  by rewrite addrA subrK.
rewrite he; exact: ler_normD.
Qed.

(** Source for [positive_integer_distance_gap]: Federer 2.2.6, p. 63,
    supporting discreteness estimate: distinct positive integers differ by
    at least one, so their normalised distance is at least one half. This
    explicit gap makes coordinate stabilisation in Cauchy sequences
    immediate. *)
Lemma positive_integer_distance_gap (R : realType) m n :
  m != n -> (1 / 2 <= @positive_integer_distance R m n)%R.
Proof.
move=> hmn; have hnorm : (1 <= `|m%:R - n%:R| :> R)%R.
  case: (ltngtP m n)=> h.
  - rewrite -[m%:R - n%:R]opprB normrN -natrB ?(ltnW h) // normr_nat ler1n subn_gt0.
    exact h.
  - rewrite -natrB ?(ltnW h) // normr_nat ler1n subn_gt0; exact h.
  - by move: hmn; rewrite h eqxx.
have hb := bounded_distance_scalar_monotone (ler01 : (0 <= (1 : R))%R) hnorm.
have he : bounded_distance_scalar (1 : R) = (1 / 2)%R.
  by rewrite /bounded_distance_scalar -mulr2n.
by rewrite he in hb.
Qed.

Arguments positive_integer_distance_nonnegative {R} m n.
Arguments positive_integer_distance_lt_one {R} m n.
Arguments positive_integer_distance_self {R} m.
Arguments positive_integer_distance_separates {R} m n _.
Arguments positive_integer_distance_symmetry {R} m n.
Arguments positive_integer_distance_triangle {R} m n k.
Arguments positive_integer_distance_gap {R} m n _.
