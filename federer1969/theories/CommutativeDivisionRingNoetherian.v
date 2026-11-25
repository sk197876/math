(** Federer (1969), 3.4.7, p. 325: the
    scalar base of the dimension induction is Noetherian
    and has unique factorization. These supporting ring proofs
    require only that every nonzero element have an inverse. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets.
From Federer Require Import CommutativeIdealUP CommutativeFactorizationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [commutative_division_ring_noetherian]:
    the scalar base case of 3.4.7, p. 325.
    A commutative nonzero ring in which every nonzero
    element is a unit has only the zero and whole ideals. *)
Theorem commutative_division_ring_noetherian (A:comNzRingType):
  (forall x:A,x<>0 ->is_commutative_unit x) ->is_noetherian_commutative_ring A.
Proof.
move=>hUnits I hI;case:(pselect (exists x,I x /\x<>0))=>[[x [hx hn]]|hZero].
- have [y hy]:=hUnits x hn.
  have hOne:I 1.
    rewrite -hy;exact:(@commutative_ideal_mul A I hI y x hx).
  exists [::1];constructor;first exact:hI.
  + move=>z;change (z \in [::1] ->I z);rewrite in_cons in_nil orbF;move/eqP=>->;exact:hOne.
  + move=>J hJ hGenerators z hz.
    have hJOne:J 1:=hGenerators 1 (mem_head 1 [::]).
    have hZ:=@commutative_ideal_mul A J hJ z 1 hJOne.
    by rewrite mulr1 in hZ.
- exists [::];constructor;first exact:hI.
  + move=>z;change (z \in [::] ->I z);by rewrite in_nil.
  + move=>J hJ hEmpty z hz.
    have hz0:z = 0.
      apply:contrapT=>hn;apply:hZero;by exists z.
    rewrite hz0;exact:commutative_ideal_zero hJ.
Qed.

(** Source for [commutative_division_ring_factorization]:
    the scalar factorization base case of 3.4.7,
    p. 325. A nonzero scalar is a unit
    times the empty product of prime factors. *)
Theorem commutative_division_ring_factorization (A:comNzRingType):
  (forall x:A,x<>0 ->is_commutative_unit x) ->
  is_unique_factorization_commutative_domain A.
Proof.
move=>hUnits;split.
- move=>x y hProduct;case:(pselect (x = 0))=>[h|h];first by left.
  right;have [u hu]:=hUnits x h.
  have hh:=congr1 (fun z:A=>u*z) hProduct.
  by rewrite mulrA hu mul1r mulr0 in hh.
- move=>x hx;exists x,[::];split;first exact:hUnits x hx.
  split;first by move=>p;rewrite in_nil.
  by rewrite big_nil mulr1.
Qed.
