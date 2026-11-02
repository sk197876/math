(** Federer (1969), 2.10.38, printed p. 199: supporting triangular form of
    the chosen chords under successive perpendicular projections. All
    formulas below follow from the public residual-map laws, without
    inspecting an implementation. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerProductUP
  InnerMetric GreedyChordFrameUP FinitePrefixes FiniteSpans.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section Expansion.
Variable R : realType.
Variable n : nat.
Variable S : set (inner_metric_space (@euclidean_inner_productP R n)).
Variable D : greedy_chord_frame_data R n.
Hypothesis hD : is_greedy_chord_frame S D.
Local Notation e := (greedy_chord_axis D).
Local Notation P := (greedy_chord_residual D).
Local Notation B := (@euclidean_inner_product R n).

(** Source for [greedy_chord_residual_expansion]: supporting
    iterated perpendicular-coordinate identity for 2.10.38,
    p. 199. In words, the removed components are
    precisely the sum along the previously chosen axes.
    This is a consequence of the abstract recursion. *)
Lemma greedy_chord_residual_expansion k (hk : (k<=n)%N) (v : R_n R n) :
  v-P k v=\sum_(j<k) B v (family_prefix hk e j)*:family_prefix hk e j.
Proof.
elim: k hk=> [|k IH] hk.
- by rewrite (greedy_chord_residual_zero_law hD) subrr big_ord0.
have hkn := leq_trans (leqnSn k) hk.
pose i : 'I_n := Ordinal hk.
rewrite (greedy_chord_residual_successor_law hD i v) opprB.
change (v+(B v (e i)*:e i-P k v)=
  \sum_(j<k.+1) B v (family_prefix hk e j)*:family_prefix hk e j).
rewrite [B v (e i)*:e i-P k v]addrC addrA (IH hkn) big_ord_recr.
congr (_+_).
- apply: eq_bigr=> j _.
  congr (B v _*:_); rewrite /family_prefix; congr (e _); exact: val_inj.
- congr (B v _*:_); rewrite /family_prefix; congr (e _); exact: val_inj.
Qed.

(** Source for [greedy_chord_triangular]: supporting
    triangular chord identity in 2.10.38, p. 199.
    The selected chord minus its diagonal axis component
    lies in the span of the earlier axes, including
    when its selected width is zero. *)
Lemma greedy_chord_triangular (i : 'I_n) :
  in_finite_span (family_prefix (ltnW (ltn_ord i)) e)
    (greedy_chord_first D i-greedy_chord_second D i-
      greedy_chord_length D i*:e i).
Proof.
rewrite -(greedy_chord_selected_law hD).
exists (fun j=>B (greedy_chord_first D i-greedy_chord_second D i)
  (family_prefix (ltnW (ltn_ord i)) e j)).
exact: greedy_chord_residual_expansion.
Qed.
End Expansion.
