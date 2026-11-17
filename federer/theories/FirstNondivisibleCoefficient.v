(** Federer (1969), 3.4.7, p. 325: the first
    coefficient not divisible by a fixed prime is
    an auxiliary witness in the Gauss argument. *)
From mathcomp Require Import all_boot all_order ssralg boolp.
From Federer Require Import CommutativeFactorizationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [first_nondivisible_coefficient]: natural-index
    minimality supplies the first coefficient not divisible
    by the original element, supporting 3.4.7, p. 325. *)
Lemma first_nondivisible_coefficient (A:comNzRingType) (p:A) (f:nat->A):
  (exists i,~commutative_divides p (f i)) ->
  exists i,(~commutative_divides p (f i)) /\
    forall j,(j<i)%N ->commutative_divides p (f j).
Proof.
move=>[i0 hi0].
have hExists:exists i,`[<~commutative_divides p (f i)>].
  exists i0;apply/asboolP;exact:hi0.
have [i /asboolP hi hMinimal]:=ex_minnP hExists.
exists i;split;first exact:hi.
move=>j hj;apply:contrapT=>hNo.
have hCandidate:`[<~commutative_divides p (f j)>] by apply/asboolP.
have hBound:=hMinimal j hCandidate.
have hContradiction:=leq_ltn_trans hBound hj.
by rewrite ltnn in hContradiction.
Qed.
