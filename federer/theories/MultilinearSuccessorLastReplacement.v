(** Federer (1969), 3.4.12, p. 338: retain the final
    derivative argument when evaluating a fixed higher coefficient.
    This finite-family connection complements the existing prefix rule. *)
From mathcomp Require Import all_boot all_order all_algebra fingroup perm.
From Federer Require Import FamilyUpdate MultilinearSuccessorArguments MultilinearSuccessorPermutation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [multilinear_successor_replace_last]: replacing the
    last argument gives the original recursive derivative family,
    supporting the higher complex-linearity assertion of 3.4.12,
    p. 338, including the zero-length prefix. *)
Lemma multilinear_successor_replace_last (T:Type) k (u:{ffun 'I_k->T}) (v w:T):
  @family_with k.+1 (fun _=>T) (multilinear_successor_arguments u v) ord_max w=
    multilinear_successor_arguments u w.
Proof.
apply/ffunP=>j;case:(unliftP ord_max j)=>[i|] ->.
- rewrite family_with_out;last by rewrite neq_lift.
  by rewrite !multilinear_successor_lift.
- by rewrite family_with_in multilinear_successor_last.
Qed.
