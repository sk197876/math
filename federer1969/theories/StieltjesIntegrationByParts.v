(** Federer (1969), 2.5.18(1), p. 112: if f : R -> R and g : R -> R are
    continuous and -oo < a < b < oo, then int_a^b f dg + int_a^b g df = f(b)
    g(b) - f(a) g(a). In fact, for a = t_1 <= t_2 <= ... <= t_{n+1} = b,
    sum_j f(t_{j+1}) [g(t_{j+1}) - g(t_j)] + sum_j g(t_j) [f(t_{j+1}) -
    f(t_j)] = f(b) g(b) - f(a) g(a). The integrals are those of 2.5.17, so
    both functions are assumed to have finite variation on segments. The
    identity is verified for the uniform sequences with right tags and with
    left tags, and the integrals are the limits of these sums. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals
  constructive_ereal topology normedtype.
From mathcomp Require Import ring lra.
From Federer Require Import RealMetricBackground CurveVariationUP CurveArcLength StieltjesSums
  StieltjesIntegral.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Import numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section Parts.
Variable R : realType.

(** Source for [uniform_right_tagged]: the uniform sequence with the
    tags u_j = t_{j+1}, Federer 2.5.18(1), p. 112. *)
Fixpoint uniform_right_tagged (a h : R) (n : nat) : seq R :=
  if n is k.+1 then a :: (a + h) :: uniform_right_tagged (a + h) h k else [:: a].

(** Source for [uniform_right_tagged_path]: supporting path property of
    the right tagged uniform sequence, Federer 2.5.18(1), p. 112. *)
Lemma uniform_right_tagged_path (x a h : R) (n : nat) :
  0 <= h -> x <= a -> path <=%O x (uniform_right_tagged a h n).
Proof.
elim: n x a=> [|k ih] x a hh hxa /=; first by rewrite hxa.
by rewrite hxa lerDl hh /=; apply: ih=> //; rewrite lerDl.
Qed.

(** Source for [uniform_right_tagged_sorted]: the right tagged uniform
    sequence is nondecreasing, Federer 2.5.18(1), p. 112. *)
Lemma uniform_right_tagged_sorted (a h : R) (n : nat) :
  0 <= h -> sorted <=%O (uniform_right_tagged a h n).
Proof.
case: n=> [//|k] hh; rewrite /= lerDl hh /=.
by apply: uniform_right_tagged_path=> //; rewrite lerDl.
Qed.

(** Source for [uniform_right_tagged_size]: the right tagged uniform
    sequence with n cells has 2n+1 terms, Federer 2.5.18(1), p. 112. *)
Lemma uniform_right_tagged_size (a h : R) (n : nat) :
  size (uniform_right_tagged a h n) = (2 * n).+1.
Proof. by elim: n a=> [//|k ih] a /=; rewrite ih mulnS. Qed.

(** Source for [uniform_right_tagged_head]: the first term is a, Federer
    2.5.18(1), p. 112. *)
Lemma uniform_right_tagged_head (a h x : R) (n : nat) : head x (uniform_right_tagged a h n) = a.
Proof. by case: n. Qed.

(** Source for [uniform_right_tagged_last]: the last term is a + n h,
    Federer 2.5.18(1), p. 112. *)
Lemma uniform_right_tagged_last (a h x : R) (n : nat) :
  last x (uniform_right_tagged a h n) = a + n%:R * h.
Proof.
elim: n a x=> [|k ih] a x /=; first by rewrite mul0r addr0.
by rewrite ih -addn1 natrD mulrDl mul1r; ring.
Qed.

(** Source for [uniform_right_tagged_mesh]: the cells of the right tagged
    uniform sequence have length h, Federer 2.5.18(1), p. 112. *)
Lemma uniform_right_tagged_mesh (a h d : R) (n : nat) :
  h < d -> tagged_mesh_lt d (uniform_right_tagged a h n).
Proof.
elim: n a=> [//|k ih] a hd; rewrite /=.
case: k ih=> [|k'] ih /=.
- by rewrite (_ : a + h - a = h) ?hd //; ring.
- apply/andP; split; first by rewrite (_ : a + h - a = h) //; ring.
  exact: ih.
Qed.

(** Source for [uniform_right_tagged_is]: the right tagged uniform
    sequence of [a, b] with n+1 cells is a sequence from a to b, Federer
    2.5.18(1), p. 112. *)
Lemma uniform_right_tagged_is (a b : R) (n : nat) :
  a <= b -> is_tagged_partition a b (uniform_right_tagged a ((b - a) / n.+1%:R) n.+1).
Proof.
move=> hab; have hh : 0 <= (b - a) / n.+1%:R by rewrite divr_ge0 ?subr_ge0 ?ler0n.
split; first exact: uniform_right_tagged_sorted.
split; first by rewrite uniform_right_tagged_size mul2n /= odd_double.
split; first exact: uniform_right_tagged_head.
rewrite uniform_right_tagged_last mulrC mulfVK ?pnatr_eq0 //.
by rewrite addrC subrK.
Qed.

(** Source for [uniform_parts_identity]: the displayed telescoping
    identity of Federer 2.5.18(1), p. 112, for the uniform sequences with
    right tags for f and left tags for g. *)
Lemma uniform_parts_identity (f g : R -> R) (a h : R) (n : nat) :
  stieltjes_sum f g (uniform_right_tagged a h n) + stieltjes_sum g f (uniform_tagged a h n)
  = f (a + n%:R * h) * g (a + n%:R * h) - f a * g a.
Proof.
elim: n a=> [|k ih] a /=; first by rewrite mul0r !addr0 subrr.
case: k ih=> [|k'] ih /=.
- by rewrite mul1r; ring.
- have := ih (a + h); rewrite /= => ih'.
  have -> : a + k'.+2%:R * h = a + h + k'.+1%:R * h by ring.
  lra.
Qed.

Variables f g : R -> R.
Hypothesis hf : curve_locally_finite_variation (f : R -> real_line_metric R).
Hypothesis hg : curve_locally_finite_variation (g : R -> real_line_metric R).
Hypothesis hfc : continuous f.
Hypothesis hgc : continuous g.

(** Source for [stieltjes_integration_by_parts]: the formula int_a^b f dg +
    int_a^b g df = f(b) g(b) - f(a) g(a) of Federer 2.5.18(1), p. 112. *)
Theorem stieltjes_integration_by_parts (a b : R) :
  a <= b -> stieltjes_integral g f a b + stieltjes_integral f g a b = f b * g b - f a * g a.
Proof.
move=> hab.
apply/eqP; rewrite -subr_eq0 -normr_eq0 eq_le normr_ge0 andbT.
apply/ler_addgt0Pr=> e he; rewrite add0r.
have he2 : 0 < e / 2 by lra.
have [d1 [hd1 h1]] := stieltjes_integral_limit hg hfc hab he2.
have [d2 [hd2 h2]] := stieltjes_integral_limit hf hgc hab he2.
have hdm : 0 < Order.min d1 d2 by rewrite lt_min hd1 hd2.
have hmin1 : Order.min d1 d2 <= d1 by rewrite ge_min lexx.
have hmin2 : Order.min d1 d2 <= d2 by rewrite ge_min lexx orbT.
have [N hN] := uniform_mesh_small hab hdm.
have hmesh := hN N (leqnn N).
have hw1 := uniform_right_tagged_is N hab.
have hw2 := uniform_partition_is N hab.
have hm1 := tagged_mesh_lt_le hmin1 (uniform_right_tagged_mesh a N.+1 hmesh).
have hm2 := tagged_mesh_lt_le hmin2 (uniform_partition_mesh hmesh).
have e1 := h1 _ hw1 hm1.
have e2 := h2 _ hw2 hm2.
have hid := uniform_parts_identity f g a ((b - a) / N.+1%:R) N.+1.
have hlast : a + N.+1%:R * ((b - a) / N.+1%:R) = b.
  by rewrite mulrC mulfVK ?pnatr_eq0 // addrC subrK.
rewrite hlast in hid.
rewrite /uniform_partition in hw2 hm2 e2.
apply: ltW; apply: le_lt_trans (ler_distD (stieltjes_sum f g (uniform_right_tagged a ((b - a) / N.+1%:R) N.+1)
  + stieltjes_sum g f (uniform_tagged a ((b - a) / N.+1%:R) N.+1)) _ _) _.
rewrite [in X in _ + X]hid subrr normr0 addr0 (splitr e).
have -> : stieltjes_integral g f a b + stieltjes_integral f g a b
    - (stieltjes_sum f g (uniform_right_tagged a ((b - a) / N.+1%:R) N.+1)
       + stieltjes_sum g f (uniform_tagged a ((b - a) / N.+1%:R) N.+1))
  = (stieltjes_integral g f a b - stieltjes_sum f g (uniform_right_tagged a ((b - a) / N.+1%:R) N.+1))
    + (stieltjes_integral f g a b - stieltjes_sum g f (uniform_tagged a ((b - a) / N.+1%:R) N.+1)) by ring.
apply: le_lt_trans (ler_normD _ _) _.
by rewrite distrC [X in _ + X]distrC; exact: (ltrD e1 e2).
Qed.

End Parts.
