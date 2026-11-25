(** Federer (1969), proof of 2.8.7, p. 144: F' consists of eligible sets
    contained in the testing open set V and covers V intersect A finely. *)
From mathcomp Require Import all_boot all_order all_algebra
  classical_sets reals topology.
From Federer Require Import CoveringFamilyUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [family_members_within]: the localized family F'=F intersect
    {S:S subset V} in Federer 2.8.7, p. 144 This is the printed set
    restriction, independently of any selected family. *)
Definition family_members_within (X : choiceType) (F : set (set X)) (V : set X) :=
  [set S | F S /\ S `<=` V].

(** Source for [fine_cover_open_restriction]: the assertion that F' covers V
    intersect A finely in Federer 2.8.7, p. 144 At a target point take the
    smaller of the prescribed radius and a radius whose open ball is
    contained in V. *)
Lemma fine_cover_open_restriction (R : realType) (X : metricType R)
    (F : set (set X)) (A V : set X) :
  open V -> family_covers_finely F A ->
  family_covers_finely (family_members_within F V) (V `&` A).
Proof.
move=> hV hf x [hv ha] e he.
have hn : nbhs x V by rewrite openE in hV; exact: hV x hv.
have [r hr hb] := proj1 (metricType_numDomainType.nbhs_mdistP x V) hn.
have hmin : 0 < Num.min e r by rewrite lt_min he hr.
have [S [hS [hx hsub]]] := hf x ha (Num.min e r) hmin.
exists S; split.
- split=> // y hy; apply: hb.
  apply: lt_le_trans (hsub y hy) _; by rewrite ge_min lexx orbT.
- split=> // y hy.
  apply: lt_le_trans (hsub y hy) _; by rewrite ge_min lexx.
Qed.
