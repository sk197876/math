(** Federer (1969), 3.4.8(2), p. 326:
    the original reduction loci are opaque sets governed
    only by their independent membership equations. Choice
    selects a witness of their proved existence. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import RealNormUP AnalyticGermUP AnalyticGermRing
  AnalyticReductionLociUP AnalyticReductionLociExistence.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Module Type AnalyticReductionLociSignature.
(** Source for [A]: the original A loci of
    3.4.8(2), p. 326. *)
Parameter A:forall (R:realType) (X:lmodType R) (NX:X->R) (hNX:is_real_norm NX)
  (n:nat) (O:Type) (e:'I_n->X) (gamma:'I_n->@analytic_germ_ring R X NX hNX 0)
  (Q:nat->set (@analytic_germ_ring R X NX hNX 0))
  (rotated:O->set (@analytic_germ_ring R X NX hNX 0)),'I_n.+1->set O.
(** Source for [B]: the original B loci of
    3.4.8(2), p. 326. *)
Parameter B:forall (R:realType) (X:lmodType R) (NX:X->R) (hNX:is_real_norm NX)
  (n:nat) (O:Type) (e:'I_n->X) (gamma:'I_n->@analytic_germ_ring R X NX hNX 0)
  (Q:nat->set (@analytic_germ_ring R X NX hNX 0))
  (rotated:O->set (@analytic_germ_ring R X NX hNX 0)),'I_n->set O.
(** Source for [C]: the original C loci of
    3.4.8(2), p. 326. *)
Parameter C:forall (R:realType) (X:lmodType R) (NX:X->R) (hNX:is_real_norm NX)
  (n:nat) (O:Type) (e:'I_n->X) (gamma:'I_n->@analytic_germ_ring R X NX hNX 0)
  (Q:nat->set (@analytic_germ_ring R X NX hNX 0))
  (rotated:O->set (@analytic_germ_ring R X NX hNX 0)),'I_n->set O.
(** Source for [E]: the original E loci of
    3.4.8(2), p. 326. *)
Parameter E:forall (R:realType) (X:lmodType R) (NX:X->R) (hNX:is_real_norm NX)
  (n:nat) (O:Type) (e:'I_n->X) (gamma:'I_n->@analytic_germ_ring R X NX hNX 0)
  (Q:nat->set (@analytic_germ_ring R X NX hNX 0))
  (rotated:O->set (@analytic_germ_ring R X NX hNX 0)),'I_n.+1->set O.
(** Source for [laws]: all exact original reduction-locus
    equations, including the endpoints, 3.4.8(2), p. 326. *)
Parameter laws:forall (R:realType) (X:lmodType R) (NX:X->R) (hNX:is_real_norm NX)
  (n:nat) (O:Type) (e:'I_n->X) (gamma:'I_n->@analytic_germ_ring R X NX hNX 0)
  (Q:nat->set (@analytic_germ_ring R X NX hNX 0))
  (rotated:O->set (@analytic_germ_ring R X NX hNX 0)),
  is_analytic_reduction_loci e gamma Q rotated
    (@A R X NX hNX n O e gamma Q rotated) (@B R X NX hNX n O e gamma Q rotated) (@C R X NX hNX n O e gamma Q rotated) (@E R X NX hNX n O e gamma Q rotated).
End AnalyticReductionLociSignature.
Module AnalyticReductionLoci:AnalyticReductionLociSignature.
Section Selection.
Variables (R:realType) (X:lmodType R) (NX:X->R) (hNX:is_real_norm NX)
  (n:nat) (O:Type) (e:'I_n->X) (gamma:'I_n->@analytic_germ_ring R X NX hNX 0)
  (Q:nat->set (@analytic_germ_ring R X NX hNX 0))
  (rotated:O->set (@analytic_germ_ring R X NX hNX 0)).
Local Notation D:=((('I_n.+1->set O)*
  (('I_n->set O)*(('I_n->set O)*('I_n.+1->set O))))%type).
(** Source for [packed_exists]: the four original loci
    have a simultaneous witness, 3.4.8(2), p. 326. *)
Local Lemma packed_exists:exists p:D,
  is_analytic_reduction_loci e gamma Q rotated p.1 p.2.1 p.2.2.1 p.2.2.2.
Proof.
have [A [B [C [E hL]]]]:=@analytic_reduction_loci_exist R X NX hNX n O e gamma Q rotated.
by exists (A,(B,(C,E))).
Qed.
(** Source for [selected]: a private simultaneous witness
    of the proved original equations, 3.4.8(2), p. 326. *)
Local Definition selected:=cid packed_exists.
(** Source for [A]: the hidden original A loci,
    selected from existence, 3.4.8(2), p. 326. *)
Definition A:= (projT1 selected).1.
(** Source for [B]: the hidden original B loci,
    selected from existence, 3.4.8(2), p. 326. *)
Definition B:= (projT1 selected).2.1.
(** Source for [C]: the hidden original C loci,
    selected from existence, 3.4.8(2), p. 326. *)
Definition C:= (projT1 selected).2.2.1.
(** Source for [E]: the hidden original E loci,
    selected from existence, 3.4.8(2), p. 326. *)
Definition E:= (projT1 selected).2.2.2.
(** Source for [laws]: the selected sets satisfy every
    independent original equation, 3.4.8(2), p. 326. *)
Lemma laws:is_analytic_reduction_loci e gamma Q rotated A B C E.
Proof. exact:(projT2 selected). Qed.
End Selection.
End AnalyticReductionLoci.
