(** Federer (1969), 3.3.20, pp. 308–309:
    finite address bounds and original corner offsets. *)
From mathcomp Require Import all_boot.
From Federer Require Import CriticalCantorAddressUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Source for [critical_cantor_address_bound]: every
    original level-j critical lower endpoint has an
    integer address below 4^j, supporting the corner
    certificates of 3.3.20, pp. 308–309. *)
Lemma critical_cantor_address_bound j a:critical_cantor_address j a ->(a<4^j)%N.
Proof.
move=>hAddress;elim:hAddress=>[|k b d hA ih /orP[/eqP->|/eqP->]];first by [].
- have hBound:=leq_mul (leqnn 4) ih.
  have hStrict:(4 * b+0<4 * b.+1)%N by rewrite mulnS (addnC 4 (4 * b)) ltn_add2l.
  rewrite expnS;exact:leq_trans hStrict hBound.
- have hBound:=leq_mul (leqnn 4) ih.
  have hStrict:(4 * b+3<4 * b.+1)%N by rewrite mulnS (addnC 4 (4 * b)) ltn_add2l.
  rewrite expnS;exact:leq_trans hStrict hBound.
Qed.

(** Source for [critical_cantor_address_zero]: the
    original endpoint zero has an address at every
    level, supporting the actual corner in 3.3.20,
    pp. 306–308. *)
Lemma critical_cantor_address_zero j:critical_cantor_address j 0.
Proof.
elim:j=>[|j ih];first exact:critical_cantor_address_root.
exact:(@critical_cantor_address_step j 0 0 ih (erefl true)).
Qed.

(** Source for [critical_cantor_address_zero_prefix]: a
    leading zero preserves each actual critical address,
    supporting the corner offsets used at arbitrarily
    late levels in 3.3.20, pp. 308–309. *)
Lemma critical_cantor_address_zero_prefix j a:
  critical_cantor_address j a ->critical_cantor_address j.+1 a.
Proof.
move=>hAddress;elim:hAddress=>[|k b d hA ih hd].
- exact:critical_cantor_address_zero.
- exact:(@critical_cantor_address_step k.+1 b d ih hd).
Qed.

(** Source for [critical_cantor_address_padding]: every
    fixed original corner offset remains an actual
    address at every later level, as used for
    the late corner-square certificates of 3.3.20,
    pp. 308–309. *)
Lemma critical_cantor_address_padding i j a:
  (i<=j)%N ->critical_cantor_address i a ->critical_cantor_address j a.
Proof.
move=>hij hA.
have hEquality:(i+(j-i)=j)%N by rewrite subnKC.
rewrite -hEquality;elim:(j-i)%N=>[|k ih];first by rewrite addn0.
rewrite addnS;exact:critical_cantor_address_zero_prefix ih.
Qed.

(** Source for [critical_cantor_two_digit_offsets]: all
    four actual inward offsets 0,3,12,15 are
    original addresses at every level j>=2,
    supporting all 40-square and smaller certificates
    in 3.3.20, pp. 308–309. *)
Lemma critical_cantor_two_digit_offsets j a:
  (2<=j)%N ->a \in [::0;3;12;15] ->critical_cantor_address j a.
Proof.
move=>hj.
have hZero:critical_cantor_address 2 0:=critical_cantor_address_zero 2.
have hThree1:critical_cantor_address 1 3.
  exact:(@critical_cantor_address_step 0 0 3 critical_cantor_address_root (erefl true)).
have hThree:critical_cantor_address 2 3.
  exact:(@critical_cantor_address_step 1 0 3 (critical_cantor_address_zero 1) (erefl true)).
have hTwelve:critical_cantor_address 2 12.
  exact:(@critical_cantor_address_step 1 3 0 hThree1 (erefl true)).
have hFifteen:critical_cantor_address 2 15.
  exact:(@critical_cantor_address_step 1 3 3 hThree1 (erefl true)).
rewrite !in_cons in_nil orbF=>/orP[/eqP->|/orP[/eqP->|/orP[/eqP->|/eqP->]]];
  exact:critical_cantor_address_padding hj _.
Qed.
