(** Federer (1969), 3.2.16, p. 253:
    geometric laws of the specified annular set.
    The strict half-radius law is the erratum's
    correction of the printed decreasing sequence. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import RealNormUP NormAnnularSetUP
  ShrinkingRadiusSelectionUP ShrinkingRadiusSelectionLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [norm_annular_set_excludes_center]:
    the annular T omits a, Federer
    3.2.16, p. 253. The positive-atom
    case must therefore adjoin the centre. *)
Lemma norm_annular_set_excludes_center (R : realType) (X : lmodType R)
    (NX : X -> R) (hNX : is_real_norm NX) (S : nat -> set X)
    a (rho : nat -> R) (T : set X) (P : nat -> R -> Prop) :
  is_shrinking_radius_selection P rho -> is_norm_annular_set NX S a rho T -> ~T a.
Proof.
move=> hR hT ha; have [n [_ [_ hn]]] := (hT a).1 ha.
rewrite subrr (real_seminorm_zero hNX.1) in hn.
by have := lt_trans (shrinking_radius_positive hR n.+1) hn; rewrite ltxx.
Qed.

(** Source for [norm_annular_index_near_center]:
    sufficiently small nonzero distances occur
    only in tail annuli, Federer 3.2.16,
    p. 253. This supplies both the mass
    estimate and the first-order remainder. *)
Lemma norm_annular_index_near_center (R : realType)
    (P : nat -> R -> Prop) (rho : nat -> R) J n (t : R) :
  is_shrinking_radius_selection P rho ->
  rho n.+1<t -> t<rho J -> (J<=n)%N.
Proof.
move=> hR hn hJ; rewrite leqNgt; apply/negP=> hnJ.
have hle := shrinking_radius_monotone hR hnJ.
have hbad := le_lt_trans hle (lt_trans hn hJ).
by rewrite ltxx in hbad.
Qed.
