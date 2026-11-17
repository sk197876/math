(** Private existence adapter for Federer (1969),
    3.4.8(8), p. 329. Reuse the quotient
    algebra proved for 1.3.1, p. 13.
    The only new hierarchy work exposes its
    original commutative ring and exact ideal kernel. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets generic_quotient.
From Federer Require Import TensorUP Bilinear AlgebraUP ModuleQuotient AlgebraQuotient
  CommutativeIdealUP CommutativeQuotientUP ScalarRingAlgebraConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Construction.
Variable K:fieldType.
Variable A:comNzRingType.
Variable scalar:{rmorphism K->A}.
Variable I:set A.
Variable hI:is_commutative_ideal I.
Variable hProper:~I 1.
Local Notation AA:=(@scalar_ring_algebra K A scalar).

(** Source for [scalar_ring_ideal_subspace]: an original
    ideal is stable under the original scalar
    constants, supporting the quotient in 3.4.8(8), p. 329. *)
Definition scalar_ring_ideal_subspace:subspace AA.
Proof.
refine (@Subspace K AA (fun x=>I (x:A)) _ _ _).
- exact:commutative_ideal_zero hI.
- exact:commutative_ideal_add hI.
- move=>c x hx;change (I (scalar c*x)).
  exact:(commutative_ideal_mul hI _ hx).
Defined.

(** Source for [scalar_ring_two_sided_ideal]: the original
    commutative ideal is a two-sided algebra ideal,
    supporting 3.4.8(8), p. 329. *)
Definition scalar_ring_two_sided_ideal:two_sided_ideal AA.
Proof.
refine (@TwoSidedIdeal K AA scalar_ring_ideal_subspace _ _).
- move=>x y hy;change (I (x*y));exact:(commutative_ideal_mul hI x hy).
- move=>x y hx;change (I (x*y));rewrite mulrC;exact:(commutative_ideal_mul hI y hx).
Defined.
Local Notation AI:=scalar_ring_two_sided_ideal.

(** Source for [scalar_ideal_quotient_carrier]: the private
    witness uses the existing actual quotient algebra,
    supporting 3.4.8(8), p. 329. *)
Definition scalar_ideal_quotient_carrier:Type:=@quotient_algebra_space K AA AI.
#[local] HB.instance Definition _:=Choice.copy scalar_ideal_quotient_carrier (@quotient_algebra_space K AA AI).
#[local] HB.instance Definition _:=GRing.Zmodule.copy scalar_ideal_quotient_carrier (@quotient_algebra_space K AA AI).
Local Notation Q:=scalar_ideal_quotient_carrier.

(** Source for [scalar_ideal_projection]: the existing
    quotient projection of the actual original ring,
    3.4.8(8), p. 329. *)
Definition scalar_ideal_projection (x:A):Q:=@quotient_projection K AA AI x.

(** Source for [scalar_ideal_projection_onto]: every actual
    class has an original representative, from the
    existing quotient theorem, 3.4.8(8), p. 329. *)
Lemma scalar_ideal_projection_onto (x:Q):exists a:A,scalar_ideal_projection a = x.
Proof. exists (repr x);exact:quotient_projection_surjective. Qed.

(** Source for [scalar_ideal_product_projection]: original
    multiplication is preserved by the existing
    quotient map, 3.4.8(8), p. 329. *)
Lemma scalar_ideal_product_projection (a b:A):
  @quotient_mul K AA AI (scalar_ideal_projection a) (scalar_ideal_projection b) = scalar_ideal_projection (a*b).
Proof. exact:(@quotient_mulE K AA AI a b). Qed.

(** Source for [scalar_ideal_quotient_commutative]: original
    commutativity descends to the quotient,
    supporting 3.4.8(8), p. 329. *)
Lemma scalar_ideal_quotient_commutative:commutative (@quotient_mul K AA AI).
Proof.
move=>x y;have [a <-]:=scalar_ideal_projection_onto x;have [b <-]:=scalar_ideal_projection_onto y.
by rewrite !scalar_ideal_product_projection mulrC.
Qed.

(** Source for [scalar_ideal_quotient_distributive]: reuse
    the existing quotient algebra distributivity,
    supporting 3.4.8(8), p. 329. *)
Lemma scalar_ideal_quotient_distributive:left_distributive (@quotient_mul K AA AI) +%R.
Proof. exact:(bilDl (@quotient_mul_bilinear K AA AI)). Qed.

(** Source for [scalar_ideal_quotient_one_nonzero]: the
    original proper ideal leaves a nonzero unit
    in the quotient, 3.4.8(8), p. 329. *)
Lemma scalar_ideal_quotient_one_nonzero:@quotient_one K AA AI != (0:Q).
Proof.
apply/eqP=>hZero;apply:hProper.
apply:(@ideal_projection_zero K AA AI (1:A)).1;exact:hZero.
Qed.
#[local] HB.instance Definition _:=@GRing.Zmodule_isComNzRing.Build Q
  (@quotient_one K AA AI) (@quotient_mul K AA AI)
  (@quotient_mul_assoc K AA AI) scalar_ideal_quotient_commutative
  (@quotient_mul_unitl K AA AI) scalar_ideal_quotient_distributive scalar_ideal_quotient_one_nonzero.

(** Source for [scalar_ideal_projection_additive]: the
    existing linear quotient map preserves zero and
    addition in the original ring, 3.4.8(8), p. 329. *)
Lemma scalar_ideal_projection_additive:nmod_morphism scalar_ideal_projection.
Proof.
split.
- exact:(linear0 (@quotient_projection K AA AI)).
- move=>x y;exact:(linearD (@quotient_projection K AA AI) x y).
Qed.
#[local] HB.instance Definition _:=GRing.isNmodMorphism.Build A [the comNzRingType of Q]
  scalar_ideal_projection scalar_ideal_projection_additive.

(** Source for [scalar_ideal_projection_multiplicative]: the
    original unit and multiplication are preserved,
    3.4.8(8), p. 329. *)
Lemma scalar_ideal_projection_multiplicative:monoid_morphism scalar_ideal_projection.
Proof.
split;first by [].
move=>x y;exact:esym (scalar_ideal_product_projection x y).
Qed.
#[local] HB.instance Definition _:=GRing.isMonoidMorphism.Build A [the comNzRingType of Q]
  scalar_ideal_projection scalar_ideal_projection_multiplicative.

(** Source for [scalar_ideal_quotient_witness]: the original
    quotient ring exists with its exact kernel,
    3.4.8(8), p. 329. The implementation is
    the already proved project quotient algebra. *)
Theorem scalar_ideal_quotient_witness:exists (C:comNzRingType) (pi:{rmorphism A->C}),
  is_commutative_ideal_quotient I pi.
Proof.
exists [the comNzRingType of Q],(GRing.RMorphism.clone A [the comNzRingType of Q] scalar_ideal_projection _).
constructor;first exact:scalar_ideal_projection_onto.
move=>x;exact:(@ideal_projection_zero K AA AI x).
Qed.
End Construction.
