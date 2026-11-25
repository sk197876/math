(** Federer (1969), 1.6.6, pp. 26-27: characteristic and scalar factors used
    by the conjugation and volume formulas. These are consequences of the
    sealed scalar laws, not additional hypotheses. Source context are
    recorded in ComplexScalarUP.v. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import ComplexScalarUP ComplexScalarSealed ComplexScalarLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory ComplexScalarTheory.
Local Open Scope ring_scope.
Section Characteristic.
Variable R : realFieldType.
Local Notation C := (ComplexScalars.C R).
Local Notation embed := (ComplexScalars.embed R).
Local Notation ii := (ComplexScalars.ii R).
Local Notation H := (ComplexScalars.laws R).

(** Source for [real_two_nonzero]: Federer 1.6.6, pp. 26-27,
    factors 2 and 1/2 in the displayed formulas. Two is nonzero over R. *)
Lemma real_two_nonzero : (1+1 : R) != 0.
Proof. apply: lt0r_neq0; apply: addr_gt0; exact: ltr01. Qed.

(** Source for [complex_two_nonzero]: Federer 1.6.6, pp. 26-27,
    factors 2 and 1/2. Two is nonzero in the complex scalar field. *)
Lemma complex_two_nonzero : (1+1 : C) != 0.
Proof.
apply/eqP => h.
have hr := congr1 (@ComplexScalars.re R) h.
rewrite -(rmorph1 embed) -rmorphD re_embed re_zero in hr.
by move: real_two_nonzero; rewrite hr eqxx.
Qed.

(** Source for [imaginary_unit_nonzero]: Federer 1.6.6,
    pp. 26-27, imaginary multiples of basis vectors and volume factors.
    The imaginary unit is nonzero. *)
Lemma imaginary_unit_nonzero : ii != 0.
Proof.
apply/eqP=> hi; have h := complex_im_i H.
by rewrite hi im_zero in h; move: (@oner_neq0 R); rewrite -h eqxx.
Qed.

(** Source for [imaginary_half_cancels]: Federer 1.6.6,
    p. 27, first displayed volume identity. The factor i/2 inverts
    the scalar -2i from the degree-one conjugate-product formula. *)
Lemma imaginary_half_cancels : (ii / (1+1)) * (- (1+1) * ii) = 1.
Proof.
by rewrite mulNr mulrN mulrA divfK ?complex_two_nonzero //
  (complex_i_square H) opprK.
Qed.
End Characteristic.
