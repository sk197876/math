(** Federer (1969), 3.4.12, p. 338:
    the original recursive higher differential retains each
    earlier argument position. This finite-family connection
    transfers a scalar identity through that recursion. *)
From mathcomp Require Import all_boot all_order all_algebra fingroup perm.
From Federer Require Import FamilyUpdate MultilinearSuccessorArguments MultilinearSuccessorPermutation.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [multilinear_successor_replace_prefix]: replacement
    of an earlier argument commutes with adjoining the
    final derivative argument, supporting 3.4.12, p. 338. *)
Lemma multilinear_successor_replace_prefix (T:Type) k (u:{ffun 'I_k->T})
    (v:T) (i:'I_k) (x:T):
  multilinear_successor_arguments (@family_with k (fun _=>T) u i x) v=
    @family_with k.+1 (fun _=>T) (multilinear_successor_arguments u v) (lift ord_max i) x.
Proof.
apply/ffunP=>j;case:(unliftP ord_max j)=>[l|] ->.
- case:(eqVneq i l)=>[<-|hDifferent].
  + by rewrite multilinear_successor_lift !family_with_in.
  + rewrite family_with_out;last by rewrite (inj_eq (@lift_inj k.+1 ord_max)).
    by rewrite !multilinear_successor_lift family_with_out.
- rewrite family_with_out;last by rewrite eq_sym neq_lift.
  by rewrite !multilinear_successor_last.
Qed.
