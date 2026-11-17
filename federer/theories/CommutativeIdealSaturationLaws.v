(** Federer (1969), 3.4.8(10), p. 331:
    the original delta-power condition is an
    ideal closed under removing powers of
    delta. Derive these consequences from
    the independent membership law and original
    ideal laws, without inspecting the seal. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets ring.
From Federer Require Import CommutativeIdealUP CommutativeIdealSaturationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Saturation.
Variable A:comNzRingType.
Variable I:set A.
Variable delta:A.
Variable S:set A.
Hypothesis hI:is_commutative_ideal I.
Hypothesis hS:is_commutative_ideal_saturation I delta S.

(** Source for [commutative_ideal_saturation_is_ideal]:
    sums, negatives and ring multiples retain
    the original finite delta-power condition,
    supporting the induction in 3.4.8(10), p. 331. *)
Theorem commutative_ideal_saturation_is_ideal:is_commutative_ideal S.
Proof.
constructor.
- apply/(hS 0);exists 0%N;rewrite expr0 mul1r;exact:commutative_ideal_zero hI.
- move=>x y /(hS x) [u hX] /(hS y) [v hY].
  apply/(hS (x+y));exists (u+v)%N.
  have hLeft:=@commutative_ideal_mul A I hI (delta^+v) (delta^+u*x) hX.
  have hRight:=@commutative_ideal_mul A I hI (delta^+u) (delta^+v*y) hY.
  have hSum:=@commutative_ideal_add A I hI _ _ hLeft hRight.
  have hEquation:delta^+(u+v)*(x+y) = delta^+v*(delta^+u*x)+delta^+u*(delta^+v*y).
    rewrite exprD;ring.
  by rewrite hEquation.
- move=>x /(hS x) [u hX];apply/(hS (-x));exists u.
  rewrite mulrN;exact:(@commutative_ideal_opp A I hI _ hX).
- move=>a x /(hS x) [u hX];apply/(hS (a*x));exists u.
  rewrite mulrCA;exact:(@commutative_ideal_mul A I hI a _ hX).
Qed.

(** Source for [commutative_ideal_saturation_contains]:
    every member of the original equation
    ideal already satisfies the power condition,
    supporting 3.4.8(10), p. 331. *)
Lemma commutative_ideal_saturation_contains:I `<=` S.
Proof. move=>x hX;apply/(hS x);exists 0%N;by rewrite expr0 mul1r. Qed.

(** Source for [commutative_ideal_saturation_cancel_delta]:
    removing one delta factor preserves the
    auxiliary saturation, supporting the original
    power induction in 3.4.8(10), p. 331. *)
Lemma commutative_ideal_saturation_cancel_delta x:S (delta*x) <->S x.
Proof.
split.
- move/(hS (delta*x))=>[u hMember].
  apply/(hS x);exists u.+1;by rewrite exprSr -mulrA.
- move=>hMember;exact:(@commutative_ideal_mul A S commutative_ideal_saturation_is_ideal delta x hMember).
Qed.

(** Source for [commutative_ideal_saturation_cancel_power]:
    every original finite delta power can
    be removed in the auxiliary saturation,
    supporting 3.4.8(10), p. 331. *)
Lemma commutative_ideal_saturation_cancel_power u x:S (delta^+u*x) <->S x.
Proof.
elim:u=>[|u IH];first by rewrite expr0 mul1r.
by rewrite exprS -mulrA commutative_ideal_saturation_cancel_delta IH.
Qed.

(** Source for [commutative_ideal_saturation_positive_power]:
    a positive exponent gives the same
    original membership condition printed in
    3.4.8(10), p. 331. *)
Lemma commutative_ideal_saturation_positive_power x:
  S x ->exists u:nat,(0<u)%N /\I (delta^+u*x).
Proof.
move/(hS x)=>[u hX];exists u.+1;split;first exact:ltn0Sn.
rewrite exprS -mulrA;exact:(@commutative_ideal_mul A I hI delta _ hX).
Qed.
End Saturation.
