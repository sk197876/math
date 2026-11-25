(** Federer (1969), 3.4.12, p. 339, extending 3.4.8(2), p. 326:
    actual orthogonal pullback carries the original ideal
    to I_g. The independent image laws and the proved
    actual inverse give ideal closure and properness. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets functions reals.
From Federer Require Import ScalarRestriction ComplexScalarSealed ComplexNormUP HermitianUP HermitianRealImaginary HermitianComplexNorm Hom RealNormUP InnerProductUP InnerNorm HilbertFormCompactness
  LinearBasis OrthogonalGroupTopology UnitaryGroup HolomorphicGermUP HolomorphicGermRing CommutativeIdealUP
  AnalyticRotatedIdealUP AnalyticRotatedIdealSealed AnalyticIdealImageLaws
  HolomorphicUnitaryPullback HolomorphicUnitaryPullbackInverse.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section RotatedGermIdeal.
Variable R:realType.
Variable X:lmodType (ComplexScalars.C R).
Variable H:X->X->ComplexScalars.C R.
Hypothesis hH:is_hermitian_product H.
Variable n:nat.
Variable e:'I_n->restricted_space (ComplexScalars.embed R) X.
Hypothesis he:is_basis e.
Local Notation O:=(@unitary_group R X H hH n e he).
Local Notation NX:=(inner_norm (hermitian_real_inner_product hH)).
Local Notation hNX:=(complex_norm_real (hermitian_complex_norm hH)).
Local Notation G:=[the comNzRingType of (@holomorphic_germ_ring R X NX hNX 0)].
Local Notation M:=(fun g:O=>@holomorphic_unitary_germ_map R X H hH n e he g).

(** Source for [holomorphic_rotated_germ_ideal]: the original
    I_g in 3.4.8(2), p. 326. The independently
    specified image is opaque; the actual orthogonal action
    supplies its map. *)
Definition holomorphic_rotated_germ_ideal (I:set G) (g:O):set G:=
  @AnalyticIdealImage.value G G (M g) I.

(** Source for [holomorphic_rotated_germ_ideal_membership]: the
    exact original membership equation for I_g,
    3.4.8(2), p. 326. *)
Lemma holomorphic_rotated_germ_ideal_membership (I:set G) (g:O) (beta:G):
  holomorphic_rotated_germ_ideal I g beta <->exists alpha,I alpha /\M g alpha=beta.
Proof. exact:(@AnalyticIdealImage.laws G G (M g) I beta). Qed.

(** Source for [holomorphic_unitary_germ_map_injective]: the
    actual orthogonal inverse makes O_0(g) injective,
    supporting 3.4.8(2), p. 326. *)
Lemma holomorphic_unitary_germ_map_injective (g:O):injective (M g).
Proof.
have [h [hLeft hRight]]:=@holomorphic_unitary_germ_inverse_exists R X H hH n e he g.
move=>alpha beta hEqual.
by rewrite -[alpha]hLeft -[beta]hLeft hEqual.
Qed.

(** Source for [holomorphic_unitary_germ_map_onto]: the actual
    inverse gives every germ a preimage, supporting
    the original I_g in 3.4.8(2), p. 326. *)
Lemma holomorphic_unitary_germ_map_onto (g:O):forall beta:G,exists alpha:G,M g alpha=beta.
Proof.
have [h [hLeft hRight]]:=@holomorphic_unitary_germ_inverse_exists R X H hH n e he g.
move=>beta;exists (M h beta);exact:hRight.
Qed.

(** Source for [holomorphic_rotated_germ_ideal_is_ideal]: the
    original I_g is an ideal, 3.4.8(2), p. 326.
    No ideal-closure premise for the image is added. *)
Theorem holomorphic_rotated_germ_ideal_is_ideal (I:set G) (g:O):
  is_commutative_ideal I ->is_commutative_ideal (holomorphic_rotated_germ_ideal I g).
Proof.
move=>hI;exact:(@analytic_ideal_image_ideal G G (M g) I
  (holomorphic_rotated_germ_ideal I g) (@AnalyticIdealImage.laws G G (M g) I)
  (holomorphic_unitary_germ_map_onto g) hI).
Qed.

(** Source for [holomorphic_rotated_germ_ideal_proper]: the
    original proper-ideal condition is preserved by g,
    3.4.8(2), p. 326. *)
Lemma holomorphic_rotated_germ_ideal_proper (I:set G) (g:O):
  ~I 1 ->~holomorphic_rotated_germ_ideal I g 1.
Proof.
move=>hI.
exact (@analytic_ideal_image_proper G G (M g) I
  (holomorphic_rotated_germ_ideal I g) (@AnalyticIdealImage.laws G G (M g) I)
  (@holomorphic_unitary_germ_map_injective g) hI).
Qed.

(** Source for [holomorphic_rotated_germ_ideal_inverse_membership]:
    inverse orthogonal pullback tests exact membership in
    the original I, supporting 3.4.8(5), p. 328. *)
Lemma holomorphic_rotated_germ_ideal_inverse_membership (I:set G) (g h:O):
  (forall alpha:G,M h (M g alpha)=alpha) ->
  (forall alpha:G,M g (M h alpha)=alpha) ->
  forall beta:G,holomorphic_rotated_germ_ideal I g beta <->I (M h beta).
Proof.
move=>hLeft hRight beta;split.
- move/(holomorphic_rotated_germ_ideal_membership I g beta)=>[alpha [hI <-]].
  by rewrite hLeft.
- move=>hI;apply/(holomorphic_rotated_germ_ideal_membership I g beta).
  exists (M h beta);by split.
Qed.
End RotatedGermIdeal.
