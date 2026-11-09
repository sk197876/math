(** Federer (1969), 3.4.2(7), pp. 312–313: lowering relative
    differentiability class in the simultaneous induction. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import RealNormUP RelativeClassUP NormRegularity
  GrassmannAbbreviations CriticalFlatPiecesUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [critical_relative_class_lower]: class k implies
    class j for j<=k, as used in 3.4.2(7), pp. 312–313. Lower
    the class of the same local ambient representatives in the
    definition of relative class from 3.1.22, p. 236. *)
Lemma critical_relative_class_lower (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (A S:set X) (f:X->Y) k j:
  (j<=k)%N ->norm_class_relative hNX hNY A S f k ->
  norm_class_relative hNX hNY A S f j.
Proof.
move=>hjk hf a ha.
have [U [F [haU [hF hAgree]]]]:=hf a ha.
exists U,F;split;first exact:haU.
split;[exact:(norm_class_lower hjk hF)|exact:hAgree].
Qed.

(** Source for [critical_flat_function_lower_class]: the function
    classes used in the class induction of 3.4.2(7), p. 313.
    Lowering class leaves the original source and zero set fixed. *)
Lemma critical_flat_function_lower_class (R:realType) m (Y:lmodType R)
    (NY:Y->R) (hNY:is_real_norm NY) S C (f:R_n R m->Y) k j:
  (j<=k)%N ->critical_flat_function_class hNY S C f k ->
  critical_flat_function_class hNY S C f j.
Proof.
move=>hjk [hf hZero];split;last exact:hZero.
exact:(critical_relative_class_lower hjk hf).
Qed.
