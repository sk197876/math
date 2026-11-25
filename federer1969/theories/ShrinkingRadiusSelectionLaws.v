(** Federer (1969), 3.2.16, p. 253,
    and erratum p. 5, line 29: strict
    half-radius decrease gives radii tending to
    zero and an annular cover of the punctured
    initial ball. Use only the abstract radius laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals lra.
From Federer Require Import ShrinkingRadiusSelectionUP RecurrentContraction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [shrinking_radius_monotone]: monotone
    radii in the annular proof of Federer
    3.2.16, p. 253, derived from the
    erratum-corrected strict half-radius law. *)
Lemma shrinking_radius_monotone (R : realType)
    (P : nat -> R -> Prop) (rho : nat -> R) :
  is_shrinking_radius_selection P rho ->
  forall n k, (n<=k)%N -> rho k<=rho n.
Proof.
move=> hRho.
have hStep n : rho n.+1<=rho n.
  have hp := shrinking_radius_positive hRho n.
  have hh := shrinking_radius_half hRho n; lra.
exact: (@homo_leq R rho (fun x y : R => is_true (y<=x))
  (fun x => lexx x) (fun b a c hab hbc => le_trans hbc hab) hStep).
Qed.

(** Source for [shrinking_radius_eventually_small]:
    the shrinking annuli cover all nonzero
    distances in Federer 3.2.16, p. 253.
    The corrected decrease implies geometric decay;
    mere strict decrease would not suffice. *)
Lemma shrinking_radius_eventually_small (R : realType)
    (P : nat -> R -> Prop) (rho : nat -> R) :
  is_shrinking_radius_selection P rho ->
  forall e : R, 0<e -> exists n, rho n<e.
Proof.
move=> hRho e he.
pose q := (2 : R)^-1.
have hq0 : 0<q by rewrite /q invr_gt0 ltr0n.
have h2q : 2*q= 1 by rewrite /q mulfV // pnatr_eq0.
have hq1 : q<1 by lra.
have hq : 0<q<1 by apply/andP; split.
have hbound n : rho n<=q^+n*rho 0%N.
  elim: n=> [|n IH]; first by rewrite expr0 mul1r.
  have hhalf : rho n.+1<=q*rho n.
    rewrite /q mulrC; exact: ltW (shrinking_radius_half hRho n).
  have hh := le_trans hhalf (ler_wpM2l (ltW hq0) IH).
  by rewrite exprS -mulrA.
have [n hn] := geometric_contraction_small hq
  (ltW (shrinking_radius_positive hRho 0%N)) he.
exists n; exact: le_lt_trans (hbound n) hn.
Qed.

(** Source for [shrinking_radius_annulus_index]:
    every positive distance no greater than
    delta_1 lies in one of the annuli
    of Federer 3.2.16, p. 253. The
    outer boundary is included and the inner
    boundary is excluded, as in the printed formula. *)
Theorem shrinking_radius_annulus_index (R : realType)
    (P : nat -> R -> Prop) (rho : nat -> R) :
  is_shrinking_radius_selection P rho ->
  forall t : R, 0<t -> t<=rho 0%N ->
    exists n, rho n.+1<t /\ t<=rho n.
Proof.
move=> hRho t ht ht0.
have [N hN] := shrinking_radius_eventually_small hRho ht.
have hcross k : rho k<t -> exists n, rho n.+1<t /\ t<=rho n.
  elim: k=> [|k IH] hsmall.
  - by have := lt_le_trans hsmall ht0; rewrite ltxx.
  - case: (ltP (rho k) t)=> hk.
    + exact: IH hk.
    + exists k; by split.
exact: hcross N hN.
Qed.
