(** Federer (1969), 3.4.12, p. 339: the original complex
    scalar field is algebraically closed. Transfer the existing
    scalar background root theorem through the unique coordinate
    isomorphism. The sealed original scalar laws remain the interface.
    This narrow background connection imports MathComp's complex
    field theorem; it imports no analytic or geometric theorem. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals complex ring.
From Federer Require Import ComplexScalarUP ComplexScalarSealed ComplexScalarLaws.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory ComplexScalarTheory.
Local Open Scope ring_scope.
Section Closure.
Variable R:realType.
Local Notation C:=(ComplexScalars.C R).
Local Notation e:=(ComplexScalars.embed R).
Local Notation ii:=(ComplexScalars.ii R).

(** Source for [complex_scalar_coordinate_transport]: the original
    real and imaginary decomposition of 1.6.6, p. 26,
    used only to connect the scalar root theorem required
    in 3.4.12, p. 339. *)
Definition complex_scalar_coordinate_transport (z:complex.complex R):C:=
  e (complex.Re z)+ii*e (complex.Im z).

(** Source for [complex_scalar_coordinate_transport_additive]: scalar
    coordinate transport preserves zero and addition, supporting
    the algebraic closedness used in 3.4.12, p. 339. *)
Lemma complex_scalar_coordinate_transport_additive:nmod_morphism complex_scalar_coordinate_transport.
Proof.
split;first by rewrite /complex_scalar_coordinate_transport /= rmorph0 mulr0 addr0.
move=>[a b] [c d];rewrite /complex_scalar_coordinate_transport /= !rmorphD.
ring.
Qed.

(** Source for [complex_scalar_coordinate_transport_multiplicative]: the
    original square relation i*i=-1 makes scalar coordinate
    transport multiplicative, supporting 3.4.12, p. 339. *)
Lemma complex_scalar_coordinate_transport_multiplicative:monoid_morphism complex_scalar_coordinate_transport.
Proof.
split;first by rewrite /complex_scalar_coordinate_transport /= rmorph0 rmorph1 mulr0 addr0.
move=>[a b] [c d];apply:coordinates_injective.
- rewrite /complex_scalar_coordinate_transport /= re_mul
    !(complex_re_add (ComplexScalars.laws R)) !re_embed !re_i_real
    !(complex_im_add (ComplexScalars.laws R)) !im_embed !im_i_real !addr0 !add0r.
  reflexivity.
- rewrite /complex_scalar_coordinate_transport /= im_mul
    !(complex_re_add (ComplexScalars.laws R)) !re_embed !re_i_real
    !(complex_im_add (ComplexScalars.laws R)) !im_embed !im_i_real !addr0 !add0r.
  reflexivity.
Qed.

(** Source for [complex_scalar_coordinate_transport_power]: original
    scalar powers are preserved by coordinate transport, supporting
    the root theorem required in 3.4.12, p. 339. *)
Lemma complex_scalar_coordinate_transport_power z n:
  complex_scalar_coordinate_transport (z^+n)=(complex_scalar_coordinate_transport z)^+n.
Proof.
elim:n=>[|n ih];first by rewrite !expr0;exact:complex_scalar_coordinate_transport_multiplicative.1.
by rewrite !exprS complex_scalar_coordinate_transport_multiplicative.2 ih.
Qed.

(** Source for [complex_scalar_coordinate_transport_surjective]: each
    original complex scalar is recovered by its original coordinates,
    supporting algebraic closedness in 3.4.12, p. 339. *)
Lemma complex_scalar_coordinate_transport_surjective:
  forall z:C,exists w:complex.complex R,complex_scalar_coordinate_transport w=z.
Proof.
move=>z;exists (complex.Complex (ComplexScalars.re z) (ComplexScalars.im z)).
exact:esym (complex_decomposition (ComplexScalars.laws R) z).
Qed.

(** Source for [complex_scalar_algebraically_closed]: every original
    nonconstant monic scalar polynomial has a root, the
    algebraic closedness used for Y_v in the complex form
    of 3.4.8(10), as stated in 3.4.12, p. 339. *)
Theorem complex_scalar_algebraically_closed:GRing.closed_field_axiom [the pzRingType of (C:Type)].
Proof.
move=>n P hn.
have [Q hQ]:=choice (fun i=>complex_scalar_coordinate_transport_surjective (P i)).
have [z hz]:=@complex.complex_acf_axiom [the rcfType of (R:Type)] n Q hn.
exists (complex_scalar_coordinate_transport z).
have h:=congr1 complex_scalar_coordinate_transport hz.
rewrite complex_scalar_coordinate_transport_power
  (big_morph complex_scalar_coordinate_transport complex_scalar_coordinate_transport_additive.2
    complex_scalar_coordinate_transport_additive.1) in h.
have hSum:(\sum_(i<n) complex_scalar_coordinate_transport (Q i*z^+i))=
    \sum_(i<n) P i*(complex_scalar_coordinate_transport z)^+i.
  apply:eq_bigr=>i _.
  by rewrite complex_scalar_coordinate_transport_multiplicative.2 hQ complex_scalar_coordinate_transport_power.
by rewrite hSum in h.
Qed.
End Closure.
