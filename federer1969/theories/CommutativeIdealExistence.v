(** Federer (1969), 3.4.5, p. 320: existence
    and uniqueness of ideals specified by their generators.
    The intersection construction supplies existence only;
    downstream arguments use the least-ideal laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets.
From Federer Require Import CommutativeIdealUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [generated_commutative_ideal_exists]: an
    original generator family determines an ideal, as used
    in 3.4.5, p. 320. Intersect all ideals
    containing the family and verify the independent laws. *)
Theorem generated_commutative_ideal_exists (A:comNzRingType) (F:set A):
  exists I:set A,is_generated_commutative_ideal F I.
Proof.
pose I:set A:=fun x=>forall J:set A,is_commutative_ideal J ->F `<=` J ->J x.
exists I;constructor.
- constructor.
  + move=>J hJ hFJ;exact:commutative_ideal_zero hJ.
  + move=>x y hx hy J hJ hFJ;exact:(@commutative_ideal_add A J hJ x y (hx J hJ hFJ) (hy J hJ hFJ)).
  + move=>x hx J hJ hFJ;exact:(@commutative_ideal_opp A J hJ x (hx J hJ hFJ)).
  + move=>x y hy J hJ hFJ;exact:(@commutative_ideal_mul A J hJ x y (hy J hJ hFJ)).
- move=>x hx J hJ hFJ;exact:hFJ x hx.
- move=>J hJ hFJ x hx;exact:hx J hJ hFJ.
Qed.

(** Source for [generated_commutative_ideal_unique]: the
    original least-ideal laws determine the generated ideal
    uniquely, supporting 3.4.5, p. 320. *)
Lemma generated_commutative_ideal_unique (A:comNzRingType) (F I J:set A):
  is_generated_commutative_ideal F I ->is_generated_commutative_ideal F J ->I=J.
Proof.
move=>hI hJ;apply/seteqP;split.
- exact:(generated_commutative_ideal_minimal hI (generated_commutative_ideal_laws hJ)
    (generated_commutative_ideal_contains hJ)).
- exact:(generated_commutative_ideal_minimal hJ (generated_commutative_ideal_laws hI)
    (generated_commutative_ideal_contains hI)).
Qed.
