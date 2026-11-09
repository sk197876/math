(** Federer (1969), 3.4.5, p. 321: the
    coefficient functions in the internal finite polynomial
    division carry their actual pointwise ring operations.
    This is a hierarchy adapter, not a new analytic assumption. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra boolp functions.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section FunctionRing.
Variable X:Type.
Variable K:comPzRingType.

(** Source for [scalar_function_ring]: actual scalar
    functions used as coefficients in the real polynomial
    argument for 3.4.5, p. 321. *)
Definition scalar_function_ring:Type:=X->K.
#[local] HB.instance Definition _:=Choice.copy scalar_function_ring [the choiceType of (X->K)].
#[local] HB.instance Definition _:=GRing.Zmodule.copy scalar_function_ring [the zmodType of (X->K)].

(** Source for [scalar_function_multiply_associative]: the
    actual pointwise product is associative, supporting finite
    division in 3.4.5, p. 321. *)
Lemma scalar_function_multiply_associative:
  associative (fun f g:scalar_function_ring=>fun x=>f x*g x).
Proof. move=>f g h;apply:funext=>x;exact:mulrA. Qed.

(** Source for [scalar_function_multiply_commutative]: the
    actual pointwise product is commutative, supporting finite
    division in 3.4.5, p. 321. *)
Lemma scalar_function_multiply_commutative:
  commutative (fun f g:scalar_function_ring=>fun x=>f x*g x).
Proof. move=>f g;apply:funext=>x;exact:mulrC. Qed.

(** Source for [scalar_function_multiply_one]: the
    constant unit acts as the pointwise multiplicative unit,
    supporting 3.4.5, p. 321. *)
Lemma scalar_function_multiply_one:
  left_id (fun _:X=>(1:K)) (fun f g:scalar_function_ring=>fun x=>f x*g x).
Proof. move=>f;apply:funext=>x;exact:mul1r. Qed.

(** Source for [scalar_function_multiply_distributive]: the
    actual pointwise product distributes over addition,
    supporting finite division in 3.4.5, p. 321. *)
Lemma scalar_function_multiply_distributive:
  left_distributive (fun f g:scalar_function_ring=>fun x=>f x*g x) +%R.
Proof. move=>f g h;apply:funext=>x;exact:mulrDl. Qed.
#[local] HB.instance Definition _:=@GRing.Zmodule_isComPzRing.Build scalar_function_ring
  (fun _:X=>(1:K)) (fun f g:scalar_function_ring=>fun x=>f x*g x)
  scalar_function_multiply_associative scalar_function_multiply_commutative
  scalar_function_multiply_one scalar_function_multiply_distributive.

(** Source for [scalar_function_ring_type]: the packed
    actual pointwise ring, supporting finite coefficient
    division in 3.4.5, p. 321. Its hierarchy
    instances stay local to this adapter. *)
Definition scalar_function_ring_type:comPzRingType:=
  [the comPzRingType of scalar_function_ring].
End FunctionRing.
