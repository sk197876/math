(** Federer (1969), 3.4.7, p. 325: a finite-coefficient
    existence witness for the independently specified polynomial
    ring. This construction is private to its existence
    proof and sealed interface. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order ssralg boolp functions.
From Federer Require Import NaturalConvolution NaturalConvolutionAssociativity FiniteCoefficientSupport.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Construction.
Variable A:comNzRingType.

(** Source for [finite_coefficient_carrier]: finite scalar
    coefficient functions witnessing the polynomial extension
    in 3.4.7, p. 325. *)
Definition finite_coefficient_carrier:Type:=
  {f:{classic nat->A} | `[<has_finite_coefficient_support f>]}.
HB.instance Definition _:=Choice.copy finite_coefficient_carrier
  [the choiceType of {f:{classic nat->A} | `[<has_finite_coefficient_support f>]}].

(** Source for [finite_coefficient_value]: actual coefficients
    of this private existence witness, supporting 3.4.7, p. 325. *)
Definition finite_coefficient_value (P:finite_coefficient_carrier) i:A:=val P i.

(** Source for [finite_coefficient_support]: the finite-support
    proof carried by each witness, supporting 3.4.7, p. 325. *)
Lemma finite_coefficient_support (P:finite_coefficient_carrier):
  has_finite_coefficient_support (finite_coefficient_value P).
Proof. apply/asboolP;exact:valP P. Qed.

(** Source for [finite_coefficient_extensionality]: coefficient
    uniqueness for this existence witness, supporting 3.4.7, p. 325. *)
Lemma finite_coefficient_extensionality (P Q:finite_coefficient_carrier):
  (forall i,finite_coefficient_value P i = finite_coefficient_value Q i) ->P = Q.
Proof. move=>h;apply:val_inj;exact:funext h. Qed.

(** Source for [finite_coefficient_zero]: the zero coefficient
    function, supporting the polynomial ring of 3.4.7, p. 325. *)
Definition finite_coefficient_zero:finite_coefficient_carrier:=
  Sub (fun _=>0) (introT (asboolP _) (@finite_coefficient_zero_support A)).

(** Source for [finite_coefficient_add]: pointwise coefficient
    addition, supporting 3.4.7, p. 325. *)
Definition finite_coefficient_add (P Q:finite_coefficient_carrier):finite_coefficient_carrier:=
  Sub (fun i=>finite_coefficient_value P i+finite_coefficient_value Q i)
    (introT (asboolP _) (finite_coefficient_add_support
      (finite_coefficient_support P) (finite_coefficient_support Q))).

(** Source for [finite_coefficient_opp]: pointwise coefficient
    negation, supporting 3.4.7, p. 325. *)
Definition finite_coefficient_opp (P:finite_coefficient_carrier):finite_coefficient_carrier:=
  Sub (fun i=> -finite_coefficient_value P i)
    (introT (asboolP _) (finite_coefficient_opp_support (finite_coefficient_support P))).

(** Source for [finite_coefficient_add_associative]: additive
    associativity of the witness, supporting 3.4.7, p. 325. *)
Lemma finite_coefficient_add_associative:associative finite_coefficient_add.
Proof. move=>P Q S;apply:finite_coefficient_extensionality=>i;exact:addrA. Qed.

(** Source for [finite_coefficient_add_commutative]: additive
    commutativity of the witness, supporting 3.4.7, p. 325. *)
Lemma finite_coefficient_add_commutative:commutative finite_coefficient_add.
Proof. move=>P Q;apply:finite_coefficient_extensionality=>i;exact:addrC. Qed.

(** Source for [finite_coefficient_add_zero]: the zero
    coefficient function is the additive unit, supporting 3.4.7, p. 325. *)
Lemma finite_coefficient_add_zero:left_id finite_coefficient_zero finite_coefficient_add.
Proof. move=>P;apply:finite_coefficient_extensionality=>i;exact:add0r. Qed.

(** Source for [finite_coefficient_add_negate]: coefficient
    negation gives additive inverses, supporting 3.4.7, p. 325. *)
Lemma finite_coefficient_add_negate:left_inverse finite_coefficient_zero
    finite_coefficient_opp finite_coefficient_add.
Proof. move=>P;apply:finite_coefficient_extensionality=>i;exact:addNr. Qed.
HB.instance Definition _:=GRing.isZmodule.Build finite_coefficient_carrier
  finite_coefficient_add_associative finite_coefficient_add_commutative
  finite_coefficient_add_zero finite_coefficient_add_negate.

(** Source for [finite_coefficient_constant]: the constant
    coefficient expression, supporting 3.4.7, p. 325. *)
Definition finite_coefficient_constant (a:A):finite_coefficient_carrier:=
  Sub (fun i=>if i==0%N then a else 0)
    (introT (asboolP _) (finite_coefficient_delta_support 0%N a)).

(** Source for [finite_coefficient_variable]: the degree-one
    coefficient expression, supporting 3.4.7, p. 325. *)
Definition finite_coefficient_variable:finite_coefficient_carrier:=
  Sub (fun i=>if i==1%N then 1 else 0)
    (introT (asboolP _) (finite_coefficient_delta_support 1%N (1:A))).

(** Source for [finite_coefficient_multiply]: finite convolution
    gives polynomial multiplication, supporting 3.4.7, p. 325. *)
Definition finite_coefficient_multiply (P Q:finite_coefficient_carrier):finite_coefficient_carrier:=
  Sub (natural_coefficient_convolution (finite_coefficient_value P) (finite_coefficient_value Q))
    (introT (asboolP _) (finite_coefficient_multiply_support
      (finite_coefficient_support P) (finite_coefficient_support Q))).

(** Source for [finite_coefficient_multiply_associative]: convolution
    is associative, supporting the polynomial ring of 3.4.7, p. 325. *)
Lemma finite_coefficient_multiply_associative:associative finite_coefficient_multiply.
Proof.
move=>P Q S;apply:finite_coefficient_extensionality=>i.
exact:esym (natural_convolution_associative _ _ _ i).
Qed.

(** Source for [finite_coefficient_multiply_commutative]: convolution
    is commutative, supporting 3.4.7, p. 325. *)
Lemma finite_coefficient_multiply_commutative:commutative finite_coefficient_multiply.
Proof. move=>P Q;apply:finite_coefficient_extensionality=>i;exact:natural_convolution_commutative. Qed.

(** Source for [finite_coefficient_multiply_one]: the constant
    unit is the multiplicative unit, supporting 3.4.7, p. 325. *)
Lemma finite_coefficient_multiply_one:left_id (finite_coefficient_constant 1) finite_coefficient_multiply.
Proof. move=>P;apply:finite_coefficient_extensionality=>i;exact:natural_convolution_one. Qed.

(** Source for [finite_coefficient_distributive]: convolution
    distributes over addition, supporting 3.4.7, p. 325. *)
Lemma finite_coefficient_distributive:left_distributive finite_coefficient_multiply +%R.
Proof. move=>P Q S;apply:finite_coefficient_extensionality=>i;exact:natural_convolution_add. Qed.

(** Source for [finite_coefficient_one_nonzero]: the unit
    coefficient distinguishes one from zero, supporting 3.4.7, p. 325. *)
Lemma finite_coefficient_one_nonzero:finite_coefficient_constant 1 != 0.
Proof.
apply/eqP=>h;have h0:=congr1 (fun P=>finite_coefficient_value P 0%N) h.
change ((1:A) = 0) in h0.
by move:(oner_neq0 A);rewrite h0 eqxx.
Qed.
HB.instance Definition _:=@GRing.Zmodule_isComNzRing.Build finite_coefficient_carrier
  (finite_coefficient_constant 1) finite_coefficient_multiply
  finite_coefficient_multiply_associative finite_coefficient_multiply_commutative
  finite_coefficient_multiply_one finite_coefficient_distributive finite_coefficient_one_nonzero.
End Construction.
