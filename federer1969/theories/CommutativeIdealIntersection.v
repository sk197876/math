(** Supporting algebra for Federer (1969), 3.4.8(5),
    p. 328: intersections of original ideals are ideals.
    This supplies the intersections in the Artin–Rees
    statement; Bourbaki, Commutative Algebra (1972),
    Chapter III, section 3, no. 1, Corollary 1, p. 197. *)
From mathcomp Require Import all_boot all_order ssralg boolp classical_sets.
From Federer Require Import CommutativeIdealUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [commutative_ideal_intersection]: the
    original ideal intersection is closed under all ideal
    operations, supporting the cited Artin–Rees statement. *)
Lemma commutative_ideal_intersection (A:comNzRingType) (I J:set A):
  is_commutative_ideal I ->is_commutative_ideal J ->is_commutative_ideal (I `&` J).
Proof.
move=>hI hJ;constructor.
- split;[exact:commutative_ideal_zero hI|exact:commutative_ideal_zero hJ].
- move=>x y hx hy;split.
  + exact:(@commutative_ideal_add A I hI x y hx.1 hy.1).
  + exact:(@commutative_ideal_add A J hJ x y hx.2 hy.2).
- move=>x hx;split.
  + exact:(@commutative_ideal_opp A I hI x hx.1).
  + exact:(@commutative_ideal_opp A J hJ x hx.2).
- move=>a x hx;split.
  + exact:(@commutative_ideal_mul A I hI a x hx.1).
  + exact:(@commutative_ideal_mul A J hJ a x hx.2).
Qed.
