(** Federer (1969), 3.3.2, p. 288, corrected by the published
    erratum pp. 5–6, book p. 288 lines 1–6: retain a strict
    threshold margin and both countable indices. This supporting
    order lemma applies to the actual radius-aperture costs later. *)
From mathcomp Require Import all_boot all_order all_algebra boolp
  classical_sets cardinality reals constructive_ereal topology.
From Federer Require Import ExtendedRealBounds ExtendedRealReciprocalBounds
  TopologicalBorel ExtendedRealOrderTopology.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [structure_tail_supremum]: the two-parameter
    supremum in Federer 3.3.2, pp. 287–288, restricted to
    0<r<delta and 0<s<1/(i+1). This is an application of
    the already sealed arbitrary extended supremum of 2.1.1. *)
Definition structure_tail_supremum (R:realType) (P:Type)
    (f:P->R->R->\bar R) (delta:R) i (x:P): \bar R:=
  extended_real_sup [set q|exists r s:R,
    (0<r<delta) /\ (0<s<((i.+1)%:R:R)^-1) /\ q=f x r s].

(** Source for [structure_tail_upper_limit]: the right-hand
    upper limit in Federer 3.3.2, pp. 287–288, expressed
    on the cofinal positive reciprocal cutoffs. A separate
    cofinality theorem identifies the all-positive-radius form. *)
Definition structure_tail_upper_limit (R:realType) (P:Type)
    (f:P->R->R->\bar R) (delta:R) (x:P): \bar R:=
  extended_real_inf [set q|exists i,q=structure_tail_supremum f delta i x].

(** Source for [structure_corrected_strict_superlevel]: the
    corrected union over j and intersection over i in the
    published erratum pp. 5–6, book p. 288 lines 1–6.
    The margin 1/(j+1) is essential even when every tail
    supremum strictly exceeds the unshifted threshold. *)
Theorem structure_corrected_strict_superlevel (R:realType) (P:Type)
    (f:P->R->R->\bar R) (delta b:R):
  [set x|(b%:E<structure_tail_upper_limit f delta x)%E]=
  \bigcup_j \bigcap_i [set x|
    (((b+((j.+1)%:R:R)^-1)%R)%:E<structure_tail_supremum f delta i x)%E].
Proof.
apply/seteqP; split=>x.
- move=>hLower.
  have [c hc]:=@extended_rationals_order_dense R _ _ hLower.
  have hcReal:b<ratr c by move:hc.1; rewrite lte_fin.
  have hGap:0<ratr c-b by rewrite subr_gt0.
  have [j hSmall]:=positive_reciprocal_nat_small hGap.
  exists j=>// i _.
  have hMargin:(((b+((j.+1)%:R:R)^-1)%R)%:E<(ratr c:R)%:E)%E.
    rewrite lte_fin; by move:hSmall; rewrite ltrBrDl addrC.
  apply:(lt_le_trans (lt_trans hMargin hc.2)).
  apply:extended_real_inf_lower; by exists i.
- move=>[j _ hAll].
  have hMargin:b<b+((j.+1)%:R:R)^-1 by rewrite ltrDl invr_gt0 ltr0n.
  have hGapE:(b%:E<((b+((j.+1)%:R:R)^-1)%R)%:E)%E by rewrite lte_fin.
  apply:(lt_le_trans hGapE).
  apply:extended_real_inf_greatest=>q [i ->]; exact:(ltW (hAll i Logic.I)).
Qed.

(** Source for [structure_tail_supremum_superlevel_open]:
    the open sets T_(j,i) in the corrected proof of Federer
    3.3.2, p. 288. A union over the actual positive radius
    and aperture sections is open; the parameter union need
    not be countable at this intermediate step. *)
Theorem structure_tail_supremum_superlevel_open (R:realType)
    (P:topologicalType) (f:P->R->R->\bar R) (delta b:R) i:
  (forall r s,0<r ->0<s ->forall c:R,
    open [set x|(c%:E<f x r s)%E]) ->
  open [set x|(b%:E<structure_tail_supremum f delta i x)%E].
Proof.
move=>hOpen.
pose D:=[set z:R*R|0<z.1<delta /\ 0<z.2<((i.+1)%:R:R)^-1].
have he:[set x|(b%:E<structure_tail_supremum f delta i x)%E]=
    \bigcup_(z in D) [set x|(b%:E<f x z.1 z.2)%E].
  apply/seteqP; split=>x.
  - move=>hx; case:(pselect (exists r s:R,
      (0<r<delta) /\ (0<s<((i.+1)%:R:R)^-1) /\ (b%:E<f x r s)%E))=>h.
    + have [r [s [hr [hs hValue]]]]:=h; exists (r,s)=>//; by split.
    + exfalso; have hUpper:(structure_tail_supremum f delta i x<=b%:E)%E.
        apply:extended_real_sup_least=>q [r [s [hr [hs ->]]]].
        rewrite leNgt; apply/negP=>hValue; apply:h; by exists r,s.
      by have:=lt_le_trans hx hUpper; rewrite ltxx.
  - move=>[[r s] [hr hs] hValue]; apply:lt_le_trans hValue _.
    apply:extended_real_sup_upper; by exists r,s.
rewrite he; apply:bigcup_open=>z hz.
exact:(hOpen z.1 z.2 (andP hz.1).1 (andP hz.2).1 b).
Qed.
