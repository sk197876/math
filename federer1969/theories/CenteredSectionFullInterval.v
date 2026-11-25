(** Full scalar sections supporting the final paragraph of Federer (1969),
    2.10.31, p. 196. Compactness makes an interior hole cost positive
    length. Consequently a centred section reaching the containing interval
    endpoint forces the original compact section to fill the interval. This
    expands, rather than assumes, the printed strict line-length argument. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal topology lra.
From Federer Require Import RealMetricBackground LebesgueScalarMeasure CenteredSectionUP
  CenteredSectionLaws CenteredSectionBounds ScalarBoundedLength CompactScalarLengthGap.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [compact_scalar_full_length_interval]: supporting
    contrapositive of the strict line-length assertion
    in 2.10.31, p. 196. Nonemptiness retains
    the degenerate r=0 case, whose measure alone
    cannot distinguish the empty set from a singleton. *)
Theorem compact_scalar_full_length_interval (R : realType) (A : set (real_line_metric R)) (r : R) :
  A !=set0 -> compact A -> 0<=r -> (forall t, A t -> `|t|<=r) ->
  lebesgue_scalar_measure A=(r+r)%:E ->
  forall t, `|t|<=r -> A t.
Proof.
move=> hne hc hr hb hlen t ht.
have [hleft hright] := compact_scalar_full_length_endpoints hne hc hr hb hlen.
case: (eqVneq t (-r))=> [->|hl]; first exact hleft.
case: (eqVneq t r)=> [->|hrr]; first exact hright.
have /andP[ht0 ht1] : -r<=t<=r by rewrite -ler_norml.
have hlt : -r<t by rewrite lt_neqAle eq_sym hl ht0.
have htr : t<r by rewrite lt_neqAle hrr ht1.
case: (pselect (A t))=> [//|hnot]; exfalso.
have hh := compact_scalar_missing_interior_length hc hb hlt htr hnot.
by rewrite hlen ltxx in hh.
Qed.

(** Source for [centered_section_full_interval]: supporting
    implication used after the last symmetrisation
    in 2.10.31, p. 196. The section laws
    and a terminal boundary point force full original
    length; the preceding compactness lemma fills it. *)
Theorem centered_section_full_interval (R : realType)
    (A B : set (real_line_metric R)) (r : R) :
  is_centered_section A B -> compact A -> 0<=r ->
  (forall t, A t -> `|t|<=r) -> B r ->
  forall t, `|t|<=r -> A t.
Proof.
move=> hs hc hr hb hBr.
have hneB : B !=set0 by exists r.
have hne := (centered_section_support_law hs).2 hneB.
have [s [hs0 [hlen hm]]] := centered_section_membership hs hne.
have hh := scalar_length_norm_bound hr hb; rewrite hlen lee_fin in hh.
have hrs : r<=s by move: ((hm r).1 hBr); rewrite ger0_norm.
have he : s=r by lra.
apply: compact_scalar_full_length_interval hne hc hr hb _.
by rewrite hlen he.
Qed.
