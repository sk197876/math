(** Federer (1969), 2.10.38, printed p. 199: successive perpendicular
    projections cannot increase the attained chord lengths. Derive this and
    coordinate preservation from the abstract frame laws before constructing
    a witness. The norm contraction is proved from the elementary
    Pythagorean identity of 1.7.1, pp. 27–28. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import GrassmannAbbreviations EuclideanInnerProduct InnerProductUP InnerNorm
  InnerMetric InnerNormalization OrthonormalFamilies UnitNormalGeometry Bilinear GreedyChordFrameUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [unit_normal_foot_norm_bound]: supporting
    perpendicular projection contraction in 2.10.38,
    p. 199. Pythagoras proves the bound
    in any real inner-product space, without a
    finite-dimensional hypothesis. *)
Lemma unit_normal_foot_norm_bound (R : realType) (V : lmodType R)
    (B : V -> V -> R) (hB : is_inner_product B) (u v : V) :
  B u u= 1 -> inner_norm hB (normal_foot hB u v)<=inner_norm hB v.
Proof.
move=> hu.
have hh := @normal_line_norm_square R V B hB u hu (normal_foot hB u v)
  (inner_coordinate hB u v) (normal_coordinate_foot hB hu v).
rewrite normal_decomposition in hh.
rewrite -(ler_sqr (inner_norm_nonnegative hB (normal_foot hB u v))
  (inner_norm_nonnegative hB v)) hh lerDl.
exact: sqr_ge0.
Qed.

Section FrameLaws.
Variable R : realType.
Variable n : nat.
Variable S : set (inner_metric_space (@euclidean_inner_productP R n)).
Variable D : greedy_chord_frame_data R n.
Hypothesis hD : is_greedy_chord_frame S D.
Local Notation e := (greedy_chord_axis D).
Local Notation c := (greedy_chord_length D).
Local Notation P := (greedy_chord_residual D).
Local Notation B := (@euclidean_inner_product R n).
Local Notation hB := (@euclidean_inner_productP R n).

(** Source for [greedy_chord_length_nonnegative]: supporting
    nonnegative box widths in 2.10.38,
    p. 198. Apply the abstract maximality
    law to a point paired with itself. *)
Lemma greedy_chord_length_nonnegative (i : 'I_n) : 0<=c i.
Proof.
have hx := (greedy_chord_endpoints_law hD i).1.
have hh := @greedy_chord_maximal_law R n S D hD i
  (greedy_chord_first D i) (greedy_chord_first D i) hx hx.
by rewrite subrr linear0 inner_norm0 in hh.
Qed.

(** Source for [greedy_chord_coordinate_preserved]: supporting
    unchanged later coordinates under earlier perpendicular
    projections in 2.10.38, p. 199.
    This follows only from residual recursion
    and orthogonality of the specified axes. *)
Lemma greedy_chord_coordinate_preserved (k : nat) (j : 'I_n) (v : R_n R n) :
  (k<=j)%N -> B (P k v) (e j)=B v (e j).
Proof.
elim: k=> [|k IH] hkj; first by rewrite (greedy_chord_residual_zero_law hD).
have hkn : (k<n)%N := ltn_trans hkj (ltn_ord j).
pose i : 'I_n := Ordinal hkn.
have hij : i!=j.
  apply/eqP=> he; have hi : (i<j)%N := hkj; by rewrite he ltnn in hi.
rewrite (greedy_chord_residual_successor_law hD i v)
  (bilBl (inner_bilinear hB)) (bilZl (inner_bilinear hB)).
change (B (P k v) (e j)-B v (e i)*B (e i) (e j)=B v (e j)).
by rewrite (IH (leq_trans (leqnSn k) hkj)) (greedy_chord_orthonormal_law hD)
  (negbTE hij) mulr0 subr0.
Qed.

(** Source for [greedy_chord_selected_norm]: supporting
    selected projected chord has its specified
    width in 2.10.38, p. 199.
    Nonnegative widths and unit axes also
    cover a zero projected chord. *)
Lemma greedy_chord_selected_norm (i : 'I_n) :
  inner_norm hB (P i (greedy_chord_first D i-greedy_chord_second D i))=c i.
Proof.
rewrite (greedy_chord_selected_law hD) inner_normZ
  (orthonormal_norm1 hB (greedy_chord_orthonormal_law hD) i) mulr1.
exact: ger0_norm (greedy_chord_length_nonnegative i).
Qed.

(** Source for [greedy_chord_residual_step_contracts]: supporting
    norm contraction for each additional projection
    in 2.10.38, p. 199. The abstract
    successor is the unit-normal foot of
    the preceding residual. *)
Lemma greedy_chord_residual_step_contracts (i : 'I_n) (v : R_n R n) :
  inner_norm hB (P i.+1 v)<=inner_norm hB (P i v).
Proof.
have hu : B (e i) (e i)= 1 by rewrite (greedy_chord_orthonormal_law hD) eqxx.
have he : P i.+1 v=normal_foot hB (e i) (P i v).
  rewrite (greedy_chord_residual_successor_law hD) /normal_foot inner_coordinateE
    (greedy_chord_coordinate_preserved v (lexx i)); reflexivity.
rewrite he; exact (@unit_normal_foot_norm_bound R (R_n R n) _ hB (e i) (P i v) hu).
Qed.

(** Source for [greedy_chord_residual_norm_antitone]: supporting
    contraction over any interval of the finite
    projection chain in 2.10.38, p. 199.
    No law beyond the stated frame length
    is assumed for the total residual-map data. *)
Lemma greedy_chord_residual_norm_antitone (k l : nat) (v : R_n R n) :
  (k<=l)%N -> (l<=n)%N -> inner_norm hB (P l v)<=inner_norm hB (P k v).
Proof.
elim: l k=> [|l IH] k hkl hln.
- by move: hkl; rewrite leqn0=> /eqP ->.
- case: (eqVneq k l.+1)=> [->|hkn]; first exact: lexx.
  have hkl' : (k<=l)%N by move: hkl; rewrite leq_eqVlt (negbTE hkn) /= ltnS.
  apply: le_trans (@greedy_chord_residual_step_contracts (Ordinal hln) v) _.
  exact: IH k hkl' (leq_trans (leqnSn l) hln).
Qed.

(** Source for [greedy_chord_lengths_ordered]: direct
    ordering c_1>=...>=c_n required in 2.10.38,
    p. 198, derived from maximality and
    projection contraction in the proof on p. 199. *)
Theorem greedy_chord_lengths_ordered (i j : 'I_n) :
  (i<=j)%N -> c j<=c i.
Proof.
move=> hij.
have [ha hb] := greedy_chord_endpoints_law hD j.
have hh := greedy_chord_residual_norm_antitone
  (greedy_chord_first D j-greedy_chord_second D j) hij (ltnW (ltn_ord j)).
rewrite (greedy_chord_selected_norm j) in hh.
exact (le_trans hh (@greedy_chord_maximal_law R n S D hD i
  (greedy_chord_first D j) (greedy_chord_second D j) ha hb)).
Qed.
End FrameLaws.
