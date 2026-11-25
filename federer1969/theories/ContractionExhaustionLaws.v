(** Federer (1969), proof of 2.8.2, p. 143: the union of the finite
    selections is countable and disjointed, remains in V, and its complement
    in V is the intersection of the open remainders. They are derived solely
    from the abstract exhaustion laws, independently of its construction.
    Source context and index convention: ContractionCoverUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import MeasureUP MeasureBasic CountablyClosedFamilyUP
  ContractionCoverUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory.
Local Open Scope classical_set_scope.
Local Open Scope ereal_scope.

(** Source for [cover_exhaustion_family]: the union of the
    finite families G_j in Federer 2.8.2, p. 143, first
    display. It is defined from an abstract family sequence,
    without inspecting how the selections were constructed. *)
Definition cover_exhaustion_family (X : choiceType)
    (G : nat -> set (set X)) := \bigcup_n G n.

Section Exhaustion.
Variable R : realType.
Variable X : metricType R.
Variable mu : set X -> \bar R.
Variable F : set (set X).
Variable A : nat -> set X.
Variable q : nat -> R.
Variable V : set X.
Variable W : nat -> set X.
Variable G : nat -> set (set X).
Variable hE : is_cover_contraction_exhaustion mu F A q V W G.

(** Source for [contraction_exhaustion_step_subset]: removing
    G_j makes W_{j+1} a subset of W_j in Federer 2.8.2,
    pp. 142–143; supporting monotonicity of remainders. *)
Lemma contraction_exhaustion_step_subset n : W n.+1 `<=` W n.
Proof.
rewrite (contraction_exhaustion_next hE n); by move=> x [].
Qed.

(** Source for [contraction_exhaustion_decreasing]: the decreasing open sets
    used in the last paragraph of Federer 2.8.2, p. 143 *)
Lemma contraction_exhaustion_decreasing n m :
  (n <= m)%N -> W m `<=` W n.
Proof.
move=> hnm.
have hiter k : W (n+k)%N `<=` W n.
  elim: k=> [|k ih]; first by rewrite addn0.
  rewrite addnS=> x hx.
  apply: ih; apply: contraction_exhaustion_step_subset; exact hx.
have he : (n+(m-n))%N = m by rewrite addnC subnK.
rewrite -he; exact: hiter.
Qed.

(** Source for [contraction_exhaustion_within_initial]: all
    remainders stay inside V, Federer 2.8.2, p. 143. *)
Lemma contraction_exhaustion_within_initial n : W n `<=` V.
Proof.
have h := contraction_exhaustion_decreasing (leq0n n).
by rewrite (contraction_exhaustion_initial hE) in h.
Qed.

(** Source for [contraction_exhaustion_member_within]: each
    member selected at stage n lies in W_n, by the defining
    containment in Federer 2.8.2, pp. 142–143. *)
Lemma contraction_exhaustion_member_within n B : G n B -> B `<=` W n.
Proof.
move=> hB x hx.
apply: (@contraction_selection_within R X mu F (A n) (W n) (q n)
  (G n) (contraction_exhaustion_selection hE n) x).
by exists B.
Qed.

(** Source for [contraction_exhaustion_family_countable]:
    the union of the finite families is countable, Federer
    2.8.2, p. 143; empty stage families are permitted. *)
Lemma contraction_exhaustion_family_countable :
  countable (cover_exhaustion_family G).
Proof.
apply: bigcup_countable; first exact: countableP.
move=> n _; exact: finite_set_countable (contraction_exhaustion_finite hE n).
Qed.

(** Source for [contraction_exhaustion_family_members]:
    the final family remains a subfamily of F, Federer
    2.8.2, p. 143. *)
Lemma contraction_exhaustion_family_members : cover_exhaustion_family G `<=` F.
Proof.
move=> B [n _ hB].
exact (@contraction_selection_members R X mu F (A n) (W n) (q n) (G n)
  (contraction_exhaustion_selection hE n) B hB).
Qed.

(** Source for [contraction_exhaustion_later_disjoint]: sets
    selected later avoid every earlier selected set, because
    the earlier finite union was removed, Federer 2.8.2,
    pp. 142–143; supporting the disjoint final family. *)
Lemma contraction_exhaustion_later_disjoint n m B C :
  (n < m)%N -> G n B -> G m C -> B `&` C = set0.
Proof.
move=> hnm hB hC; apply/seteqP; split=> [x [hb hc]|x []].
have hwm : W m x := contraction_exhaustion_member_within hC hc.
have hwn : W n.+1 x := contraction_exhaustion_decreasing hnm hwm.
rewrite (contraction_exhaustion_next hE n) in hwn.
apply: hwn.2; by exists B.
Qed.

(** Source for [contraction_exhaustion_family_disjoint]:
    the final union family is disjointed, Federer 2.8.2,
    p. 143. At one stage this is a selection law; at
    different stages it follows from the removed remainders. *)
Lemma contraction_exhaustion_family_disjoint :
  set_family_disjoint (cover_exhaustion_family G).
Proof.
move=> B C [n _ hB] [m _ hC] hBC.
case: (ltngtP n m)=> [hnm|hmn|he].
- exact: contraction_exhaustion_later_disjoint hnm hB hC.
- rewrite setIC; exact: contraction_exhaustion_later_disjoint hmn hC hB.
- subst m.
  exact (@contraction_selection_disjoint R X mu F (A n) (W n) (q n)
    (G n) (contraction_exhaustion_selection hE n) B C hB hC hBC).
Qed.

(** Source for [contraction_exhaustion_union_within]: the
    final selected union lies in V, Federer 2.8.2, p. 143. *)
Lemma contraction_exhaustion_union_within :
  (\bigcup_(B in cover_exhaustion_family G) B) `<=` V.
Proof.
move=> x [B [n _ hB] hx].
exact: contraction_exhaustion_within_initial
  (contraction_exhaustion_member_within hB hx).
Qed.

(** Source for [contraction_exhaustion_residual]: the identity V minus the
    final selected union equals the intersection of W_j, Federer 2.8.2, p.
    143, second display *)
Theorem contraction_exhaustion_residual :
  V `\` (\bigcup_(B in cover_exhaustion_family G) B) = \bigcap_n W n.
Proof.
apply/seteqP; split.
- move=> x [hx hn] n _; elim: n=> [|n ih].
  + by rewrite (contraction_exhaustion_initial hE).
  + rewrite (contraction_exhaustion_next hE n); split=> //.
    move=> [B hB hb]; apply: hn; exists B=> //; by exists n.
- move=> x hx; split.
  + have h := hx 0%N Logic.I; by rewrite (contraction_exhaustion_initial hE) in h.
  + move=> [B [n _ hB] hb].
    have h := hx n.+1 Logic.I; rewrite (contraction_exhaustion_next hE n) in h.
    apply: h.2; by exists B.
Qed.

(** Source for [contraction_exhaustion_measure_decreasing]:
    the measures of intersections with a fixed target decrease,
    Federer 2.8.2, p. 143, final paragraph. The target need
    not be measurable. *)
Lemma contraction_exhaustion_measure_decreasing (hm : is_measure mu) (B : set X) n m :
  (n <= m)%N -> mu (W m `&` B) <= mu (W n `&` B).
Proof.
move=> hnm.
have hsub : W m `<=` W n := contraction_exhaustion_decreasing hnm.
apply: (@measure_mono R X mu hm (W m `&` B) (W n `&` B))=> x [hw hb].
split; first exact (hsub x hw).
exact hb.
Qed.

(** Source for [contraction_exhaustion_measure_step]: at each
    stage assigned to a target B, its remaining measure contracts
    by the assigned factor, Federer 2.8.2, p. 143, final
    display. This statement uses only the abstract stage laws. *)
Lemma contraction_exhaustion_measure_step n B r :
  A n = B -> q n = r ->
  mu (W n.+1 `&` B) <= r%:E * mu (W n `&` B).
Proof.
move=> ha hq.
have he : W n.+1 `&` B = (W n `&` B) `\` \bigcup_(C in G n) C.
  rewrite (contraction_exhaustion_next hE n); apply/seteqP; split.
  - by move=> x [[hw hn] hb]; split=> //; split.
  - by move=> x [[hw hb] hn]; split=> //; split.
rewrite he.
have h := contraction_selection_bound (contraction_exhaustion_selection hE n).
by rewrite ha hq in h.
Qed.
End Exhaustion.
