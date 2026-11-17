(** Federer (1969), 3.4.7, p. 325: the private finite
    coefficient ring satisfies the independent polynomial laws.
    Its construction serves only to prove existence. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order ssralg boolp.
From Federer Require Import CommutativePolynomialUP NaturalConvolution
  FiniteCoefficientSupport FiniteCoefficientConstruction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Witness.
Variable A:comNzRingType.
Local Notation B:=[the comNzRingType of (finite_coefficient_carrier A)].

(** Source for [finite_coefficient_constant_additive]: constants
    preserve addition, supporting the scalar embedding of
    the extension in 3.4.7, p. 325. *)
Lemma finite_coefficient_constant_additive:nmod_morphism (@finite_coefficient_constant A).
Proof.
split.
- apply:finite_coefficient_extensionality=>i.
  change ((if i==0%N then (0:A) else 0) = 0);by case:(i==0%N).
- move=>a b;apply:finite_coefficient_extensionality=>i.
  change ((if i==0%N then a+b else 0) =
    (if i==0%N then a else 0)+(if i==0%N then b else 0)).
  by case:(i==0%N);rewrite ?add0r.
Qed.
HB.instance Definition _:=GRing.isNmodMorphism.Build A B
  (@finite_coefficient_constant A) finite_coefficient_constant_additive.

(** Source for [finite_coefficient_constant_multiplicative]:
    constants preserve one and multiplication, supporting
    the embedding in 3.4.7, p. 325. *)
Lemma finite_coefficient_constant_multiplicative:
  monoid_morphism (@finite_coefficient_constant A).
Proof.
split;first by [].
move=>a b;apply:finite_coefficient_extensionality=>n.
change ((if n==0%N then a*b else 0) =
  natural_coefficient_convolution (fun i=>if i==0%N then a else 0)
    (fun i=>if i==0%N then b else 0) n).
rewrite /natural_coefficient_convolution big_mkord (bigD1 (ord0:'I_n.+1)) //= subn0.
have hRest:(\sum_(i<n.+1|i!=ord0)
    (if (i:nat)==0%N then a else 0)*(if (n-i)%N==0%N then b else 0)) = 0.
  apply:big1=>i hi.
  have hi0:((i:nat)==0%N) = false.
    apply/negP=>/eqP h;move:hi;by rewrite -val_eqE /= h eqxx.
  by rewrite hi0 mul0r.
rewrite hRest addr0;by case:(n==0%N);rewrite ?mulr0.
Qed.
HB.instance Definition _:=GRing.isMonoidMorphism.Build A B
  (@finite_coefficient_constant A) finite_coefficient_constant_multiplicative.

(** Source for [finite_coefficient_embedding]: the original
    coefficient ring embeds as constants, supporting 3.4.7, p. 325. *)
Definition finite_coefficient_embedding:{rmorphism A->B}:=
  GRing.RMorphism.clone A B (@finite_coefficient_constant A) _.

(** Source for [finite_coefficient_polynomial_laws]: the private
    witness satisfies all independently specified coefficient
    laws for the extension in 3.4.7, p. 325. *)
Lemma finite_coefficient_polynomial_laws:
  is_commutative_polynomial_ring finite_coefficient_embedding
    (@finite_coefficient_variable A) (@finite_coefficient_value A).
Proof.
constructor.
- by [].
- by [].
- by [].
- move=>P Q n;exact:big_mkord.
- by [].
- by [].
- exact:finite_coefficient_support.
- exact:finite_coefficient_extensionality.
Qed.
End Witness.

(** Source for [commutative_polynomial_ring_exists]: existence
    of the polynomial extension specified before construction,
    supporting the Gauss argument in 3.4.7, p. 325. *)
Theorem commutative_polynomial_ring_exists (A:comNzRingType):
  exists (B:comNzRingType) (embed:{rmorphism A->B}) (variable:B) (coefficient:B->nat->A),
    is_commutative_polynomial_ring embed variable coefficient.
Proof.
exists [the comNzRingType of (finite_coefficient_carrier A)],
  (@finite_coefficient_embedding A),(@finite_coefficient_variable A),(@finite_coefficient_value A).
exact:finite_coefficient_polynomial_laws.
Qed.
