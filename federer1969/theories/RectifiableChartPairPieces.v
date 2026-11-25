(** Federer (1969), 3.2.22, pp. 258–260: the
    source/target chart intersections P_ij, their parameter
    preimages A_ij, and the exact corresponding fibres.
    These set formulas do not discard either null remainder. *)
From mathcomp Require Import all_boot boolp classical_sets topology.
From Federer Require Import MappingMultiplicity.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [rectifiable_chart_pair_parameters]: A_ij in
    Federer 3.2.22, p. 259, is the part of K_i
    whose F composed psi_i image lies in gamma_j(C_j).
    This is the source's auxiliary set, with its membership
    given directly by the printed formula. *)
Definition rectifiable_chart_pair_parameters (X Y U V:Type)
    (K:set X) (C:set U) (psi:X->Y) (F:Y->V) (gamma:U->V):set X:=
  K `&` ((fun a=>F (psi a)) @^-1` (gamma @` C)).

(** Source for [rectifiable_chart_pair_piece]: P_ij in
    Federer 3.2.22, p. 258: intersect the compact
    source-chart image with the inverse image of the compact
    target-chart image. The original f and its extension F
    agree on this set in the final application. *)
Definition rectifiable_chart_pair_piece (X Y U V:Type)
    (K:set X) (C:set U) (psi:X->Y) (F:Y->V) (gamma:U->V):set Y:=
  (psi @` K) `&` (F @^-1` (gamma @` C)).

(** Source for [rectifiable_chart_pair_image]: the relation
    P_ij=psi_i(A_ij) implicit in Federer 3.2.22,
    pp. 259–260. This exact set identity requires
    no ambient injectivity or omitted-set convention. *)
Lemma rectifiable_chart_pair_image (X Y U V:Type)
    (K:set X) (C:set U) (psi:X->Y) (F:Y->V) (gamma:U->V):
  rectifiable_chart_pair_piece K C psi F gamma=
    psi @` (rectifiable_chart_pair_parameters K C psi F gamma).
Proof.
apply/seteqP; split=>w.
- move=>[[a ha hEq] hTarget]; exists a; last exact hEq.
  split; first exact ha; change ((gamma @` C) (F (psi a))).
  by rewrite hEq.
- move=>[a [ha hTarget] hEq]; split.
  + by exists a.
  + change ((gamma @` C) (F w)); by rewrite -hEq.
Qed.

(** Source for [rectifiable_chart_pair_fibre]: the displayed
    fibre identity on p. 260 in Federer 3.2.22:
    P_ij intersect f inverse gamma_j(y) is psi_i of
    A_ij intersect phi_ij inverse y. Only the actual
    inverse law on C_j is needed; no global inverse
    law for the extended G_j is assumed. *)
Lemma rectifiable_chart_pair_fibre (X Y U V:Type)
    (K:set X) (C:set U) (psi:X->Y) (F:Y->V) (gamma:U->V) (G:V->U) y:
  (forall u,C u ->G (gamma u)=u) ->C y ->
  mapping_fibre F (rectifiable_chart_pair_piece K C psi F gamma) (gamma y)=
    psi @` (mapping_fibre (fun a=>G (F (psi a)))
      (rectifiable_chart_pair_parameters K C psi F gamma) y).
Proof.
move=>hG hy; apply/seteqP; split=>w.
- move=>[[[a ha hEq] hTarget] hFibre].
  have hValue:F (psi a)=gamma y by rewrite hEq; exact hFibre.
  exists a; last exact hEq; split.
  + split; first exact ha; exists y; first exact hy; exact:esym hValue.
  + change (G (F (psi a))=y); by rewrite hValue (hG y hy).
- move=>[a [[ha [u hu hEq]] hFibre] hPsi].
  have hPhi:G (F (psi a))=u by rewrite -hEq (hG u hu).
  have huy:u=y by rewrite -hPhi; exact hFibre.
  split.
  + split.
    * by exists a.
    * change ((gamma @` C) (F w)); exists u; first exact hu.
      by rewrite -hPsi.
  + change (F w=gamma y); rewrite -hPsi -hEq huy; reflexivity.
Qed.
