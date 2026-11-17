(** Federer (1969), 3.4.8(2), p. 326:
    actual orthogonal pullback carries the original ideal
    to I_g. The independent image laws and the proved
    actual inverse give ideal closure and properness. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP InnerProductUP InnerNorm HilbertFormCompactness
  LinearBasis OrthogonalGroupTopology AnalyticGermUP AnalyticGermRing CommutativeIdealUP
  AnalyticRotatedIdealUP AnalyticRotatedIdealSealed AnalyticIdealImageLaws
  AnalyticOrthogonalPullback AnalyticOrthogonalPullbackInverse.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section RotatedGermIdeal.
Variable R:realType.
Variable X:lmodType R.
Variable B:X->X->R.
Hypothesis hB:is_inner_product B.
Variable n:nat.
Variable e:'I_n->X.
Hypothesis he:is_basis e.
Local Notation O:=(@orthogonal_group R X B hB n e he).
Local Notation NX:=(inner_norm hB).
Local Notation hNX:=(inner_norm_real_norm hB).
Local Notation G:=[the comNzRingType of (@analytic_germ_ring R X NX hNX 0)].
Local Notation M:=(fun g:O=>@analytic_orthogonal_germ_map R X B hB n e he g).

(** Source for [analytic_rotated_germ_ideal]: the original
    I_g in 3.4.8(2), p. 326. The independently
    specified image is opaque; the actual orthogonal action
    supplies its map. *)
Definition analytic_rotated_germ_ideal (I:set G) (g:O):set G:=
  @AnalyticIdealImage.value G G (M g) I.

(** Source for [analytic_rotated_germ_ideal_membership]: the
    exact original membership equation for I_g,
    3.4.8(2), p. 326. *)
Lemma analytic_rotated_germ_ideal_membership (I:set G) (g:O) (beta:G):
  analytic_rotated_germ_ideal I g beta <->exists alpha,I alpha /\M g alpha=beta.
Proof. exact:(@AnalyticIdealImage.laws G G (M g) I beta). Qed.

(** Source for [analytic_orthogonal_germ_map_injective]: the
    actual orthogonal inverse makes O_0(g) injective,
    supporting 3.4.8(2), p. 326. *)
Lemma analytic_orthogonal_germ_map_injective (g:O):injective (M g).
Proof.
have [h [hLeft hRight]]:=@analytic_orthogonal_germ_inverse_exists R X B hB n e he g.
move=>alpha beta hEqual.
by rewrite -[alpha]hLeft -[beta]hLeft hEqual.
Qed.

(** Source for [analytic_orthogonal_germ_map_onto]: the actual
    inverse gives every germ a preimage, supporting
    the original I_g in 3.4.8(2), p. 326. *)
Lemma analytic_orthogonal_germ_map_onto (g:O):forall beta:G,exists alpha:G,M g alpha=beta.
Proof.
have [h [hLeft hRight]]:=@analytic_orthogonal_germ_inverse_exists R X B hB n e he g.
move=>beta;exists (M h beta);exact:hRight.
Qed.

(** Source for [analytic_rotated_germ_ideal_is_ideal]: the
    original I_g is an ideal, 3.4.8(2), p. 326.
    No ideal-closure premise for the image is added. *)
Theorem analytic_rotated_germ_ideal_is_ideal (I:set G) (g:O):
  is_commutative_ideal I ->is_commutative_ideal (analytic_rotated_germ_ideal I g).
Proof.
move=>hI;exact:(@analytic_ideal_image_ideal G G (M g) I
  (analytic_rotated_germ_ideal I g) (@AnalyticIdealImage.laws G G (M g) I)
  (analytic_orthogonal_germ_map_onto g) hI).
Qed.

(** Source for [analytic_rotated_germ_ideal_proper]: the
    original proper-ideal condition is preserved by g,
    3.4.8(2), p. 326. *)
Lemma analytic_rotated_germ_ideal_proper (I:set G) (g:O):
  ~I 1 ->~analytic_rotated_germ_ideal I g 1.
Proof.
move=>hI.
exact (@analytic_ideal_image_proper G G (M g) I
  (analytic_rotated_germ_ideal I g) (@AnalyticIdealImage.laws G G (M g) I)
  (@analytic_orthogonal_germ_map_injective g) hI).
Qed.

(** Source for [analytic_rotated_germ_ideal_inverse_membership]:
    inverse orthogonal pullback tests exact membership in
    the original I, supporting 3.4.8(5), p. 328. *)
Lemma analytic_rotated_germ_ideal_inverse_membership (I:set G) (g h:O):
  (forall alpha:G,M h (M g alpha)=alpha) ->
  (forall alpha:G,M g (M h alpha)=alpha) ->
  forall beta:G,analytic_rotated_germ_ideal I g beta <->I (M h beta).
Proof.
move=>hLeft hRight beta;split.
- move/(analytic_rotated_germ_ideal_membership I g beta)=>[alpha [hI <-]].
  by rewrite hLeft.
- move=>hI;apply/(analytic_rotated_germ_ideal_membership I g beta).
  exists (M h beta);by split.
Qed.
End RotatedGermIdeal.
