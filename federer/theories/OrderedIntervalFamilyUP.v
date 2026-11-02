(** Federer (1969), 2.9.20(3), pp. 165–166: finite ordered families
    a<=u_1<v_1<=...<=u_n<v_n<=b and the sums of their lengths and absolute
    increments. These predicates specify the family laws without choosing a
    subdivision. No relevant correction occurs in the local transcription of
    Federer's erratum. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [is_ordered_real_interval_family]: direct finite-family
    hypothesis of Federer 2.9.20(3), p. 165 Each cell is nondegenerate,
    consecutive cells may share an endpoint, and the empty family is
    allowed. *)
Fixpoint is_ordered_real_interval_family (R : realType) (a b : R)
    (s : seq (R * R)) : Prop :=
  match s with
  | [::] => True
  | (u,v) :: rest => a<=u /\ u<v /\ v<=b /\
      is_ordered_real_interval_family v b rest
  end.

(** Source for [real_interval_family_length]: direct sum of v_j-u_j in
    Federer 2.9.20(3), p. 165 The empty sum is zero. *)
Definition real_interval_family_length (R : realType) (s : seq (R * R)) : R :=
  \sum_(uv <- s) (uv.2-uv.1).

(** Source for [real_interval_family_increment_sum]: direct sum of
    |g(v_j)-g(u_j)| in Federer 2.9.20(3), p. 165 This definition makes no
    regularity or variation assumption on g. *)
Definition real_interval_family_increment_sum (R : realType) (g : R -> R)
    (s : seq (R * R)) : R := \sum_(uv <- s) `|g uv.2-g uv.1|.

(** Source for [ordered_real_interval_family_lower_bound]: supporting
    restriction law for the families of Federer 2.9.20(3), p. 165.
    Moving the ambient left endpoint to the left preserves eligibility. *)
Lemma ordered_real_interval_family_lower_bound (R : realType) (a a' b : R)
    (s : seq (R * R)) :
  a<=a' -> is_ordered_real_interval_family a' b s ->
  is_ordered_real_interval_family a b s.
Proof. by case: s=> [|[u v] s] //= haa' [h1 [h2 [h3 h4]]]; split; [exact: le_trans haa' h1|]. Qed.

(** Source for [ordered_real_interval_family_upper_bound]: supporting
    restriction law for Federer 2.9.20(3), p. 165: moving the
    ambient right endpoint to the right preserves all family laws. *)
Lemma ordered_real_interval_family_upper_bound (R : realType) (a b b' : R)
    (s : seq (R * R)) : b<=b' ->
  is_ordered_real_interval_family a b s ->
  is_ordered_real_interval_family a b' s.
Proof.
move=> hbb'; elim: s a=> [//|[u v] s ih] a /= [hau [huv [hvb hs]]].
split=> //; split=> //; split; first exact: le_trans hvb hbb'.
exact: ih hs.
Qed.

(** Source for [ordered_real_interval_family_cell_bounds]: supporting
    endpoint bounds for each cell in Federer 2.9.20(3), p. 165.
    The order hypotheses imply a<=u<v<=b for every member. *)
Lemma ordered_real_interval_family_cell_bounds (R : realType) (a b : R)
    (s : seq (R * R)) (u v : R) :
  is_ordered_real_interval_family a b s -> (u,v) \in s ->
  a<=u /\ u<v /\ v<=b.
Proof.
elim: s a=> [//|[p q] s ih] a /= [hap [hpq [hqb hs]]].
rewrite inE=> /orP[/eqP heq|huv].
  have hu : u=p := congr1 fst heq.
  have hv : v=q := congr1 snd heq.
  by rewrite hu hv.
have [hqu [huv' hvb]] := ih q hs huv.
split; first exact: le_trans (le_trans hap (ltW hpq)) hqu.
by split.
Qed.

(** Source for [real_interval_family_length_nonnegative]: supporting
    sign of the length sum in Federer 2.9.20(3), p. 165. *)
Lemma real_interval_family_length_nonnegative (R : realType) (a b : R)
    (s : seq (R * R)) : is_ordered_real_interval_family a b s ->
  0<=real_interval_family_length s.
Proof.
move=> hs; rewrite /real_interval_family_length big_seq.
apply: sumr_ge0=> uv huv; case: uv huv=> u v huv.
have [_ [huv' _]] := ordered_real_interval_family_cell_bounds hs huv.
by rewrite subr_ge0; exact: ltW huv'.
Qed.

(** Source for [real_interval_family_increment_sum_nonnegative]: supporting
    sign of the absolute-increment sum in Federer 2.9.20(3), p. 165.
    This sign does not require the intervals to be ordered. *)
Lemma real_interval_family_increment_sum_nonnegative (R : realType)
    (g : R -> R) (s : seq (R * R)) :
  0<=real_interval_family_increment_sum g s.
Proof. by apply: sumr_ge0=> uv huv; exact: normr_ge0. Qed.
