(** Consequences of the defining line-section laws of Federer (1969),
    2.10.30, p. 195. No construction is used. Source context and scalar
    interpretation: CenteredSectionUP.v. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology lra.
From Federer Require Import RealMetricBackground CenteredSectionUP LebesgueScalarMeasure MeasureUP MeasureBasic.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory numFieldTopology.Exports.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [centered_section_empty]: direct empty
    alternative in 2.10.30, p. 195, derived from the
    support law without choosing a radius. *)
Lemma centered_section_empty (R : realType) (A B : set (real_line_metric R)) :
  is_centered_section A B -> (A=set0 <-> B=set0).
Proof.
move=> h; split=> hz.
- apply/seteqP; split=> x; last by case.
  move=> hx; have hb : B !=set0 by exists x.
  have [y hy] := (centered_section_support_law h).2 hb; by rewrite hz in hy.
- apply/seteqP; split=> x; last by case.
  move=> hx; have ha : A !=set0 by exists x.
  have [y hy] := (centered_section_support_law h).1 ha; by rewrite hz in hy.
Qed.

(** Source for [centered_section_radius_unique]: supporting
    uniqueness of the centred segment with specified length
    in 2.10.30, p. 195. Equal segment lengths force
    equal nonnegative radii, including zero. *)
Lemma centered_section_radius_unique (R : realType) (r s : R) :
  0<=r -> 0<=s ->
  lebesgue_scalar_measure `[-r,r]=lebesgue_scalar_measure `[-s,s] -> r=s.
Proof.
move=> hr hs.
have hrr : -r<=r by lra.
have hss : -s<=s by lra.
rewrite !lebesgue_scalar_segment // => /eqP.
rewrite eqe => /eqP he; lra.
Qed.

(** Source for [centered_section_unique]: supporting
    uniqueness of the operation defined in 2.10.30,
    p. 195, first on a single normal line. Only the
    abstract support, shape and length laws are used. *)
Theorem centered_section_unique (R : realType) (A B C : set (real_line_metric R)) :
  is_centered_section A B -> is_centered_section A C -> B=C.
Proof.
move=> hB hC; case: (pselect (A !=set0))=> [hA|hA].
- have [r [hr hBr]] := centered_section_shape_law hB ((centered_section_support_law hB).1 hA).
  have [s [hs hCs]] := centered_section_shape_law hC ((centered_section_support_law hC).1 hA).
  have he : lebesgue_scalar_measure `[-r,r]=lebesgue_scalar_measure `[-s,s].
    by rewrite -hBr -hCs (centered_section_length_law hB) (centered_section_length_law hC).
  by rewrite hBr hCs (centered_section_radius_unique hr hs he).
- have hzero : A=set0.
    apply/seteqP; split=> x; last by case.
    by move=> hx; exfalso; apply: hA; exists x.
  by rewrite ((centered_section_empty hB).1 hzero) ((centered_section_empty hC).1 hzero).
Qed.

(** Source for [centered_section_membership]: direct scalar membership
    description of the normal-line segment in 2.10.30, p. 195 The radius is
    characterised by length, without unfolding any existence witness. *)
Lemma centered_section_membership (R : realType) (A B : set (real_line_metric R)) :
  is_centered_section A B -> A !=set0 ->
  exists r : R, 0<=r /\ lebesgue_scalar_measure A=(r+r)%:E /\
    forall t, B t <-> `|t|<=r.
Proof.
move=> h hA; have [r [hr hBr]] := centered_section_shape_law h ((centered_section_support_law h).1 hA).
exists r; split=> //; split.
- rewrite -(centered_section_length_law h) hBr lebesgue_scalar_segment; last by lra.
  by rewrite opprK.
- by move=> t; rewrite hBr /= in_itv /= ler_norml.
Qed.

(** Source for [centered_section_reflection]: scalar supporting case of
    rho_u(T)=T in 2.10.30, p. 195 Empty and degenerate sections are
    included. *)
Lemma centered_section_reflection (R : realType) (A B : set (real_line_metric R)) :
  is_centered_section A B -> forall t, B (-t) <-> B t.
Proof.
move=> h t; case: (pselect (A !=set0))=> [hA|hA].
- have [r [hr [_ hm]]] := centered_section_membership h hA.
  by rewrite !hm normrN.
- have hz : A=set0.
    apply/seteqP; split=> x; last by case.
    by move=> hx; exfalso; apply: hA; exists x.
  by rewrite ((centered_section_empty h).1 hz).
Qed.
