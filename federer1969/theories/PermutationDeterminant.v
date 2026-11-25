(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order ssralg fingroup perm.
From Federer Require Import ExteriorBases Shuffles InversionCount.
From Federer Require Import ExteriorDeterminant ExteriorPermutation.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.3.4, last paragraph: phi(lambda) takes e_i to e_lambda(i).
    MathComp writes permutations acting on the right: sigma*tau applies
    sigma first and tau second. The composition formula states this
    convention explicitly. *)
Section PermutationEndomorphisms.
Variable K : fieldType.
Variable n : nat.
Variable V : lmodType K.
Variable e : 'I_n -> V.
Hypothesis he : is_basis e.

(** Source for [phi]: Federer (1969), 1.3.4, p. 16, last paragraph,
    permutation endomorphisms. In words: The endomorphism sending each basis
    vector to its permuted basis vector has determinant equal to the
    permutation index; consequently index is multiplicative. Definition or
    construction used to formalise this passage. *)
Definition phi (sigma : 'S_n) : {linear V -> V} :=
  linear_comp (basis_synthesis (fun i => e (sigma i))) (basis_coordinates he).
(** Source for [phiE]: Federer (1969), 1.3.4, p. 16, last paragraph,
    permutation endomorphisms. In words: The endomorphism sending each basis
    vector to its permuted basis vector has determinant equal to the
    permutation index; consequently index is multiplicative. Formalises the
    indicated part of the passage under the hypotheses in the statement
    below. *)
Lemma phiE sigma i : phi sigma (e i) = e (sigma i).
Proof. by rewrite /phi /= basis_coordinatesE basis_synthesisE. Qed.
(** Source for [phi_comp]: Federer (1969), 1.3.4, p. 16, last paragraph,
    permutation endomorphisms. In words: The endomorphism sending each basis
    vector to its permuted basis vector has determinant equal to the
    permutation index; consequently index is multiplicative. Formalises the
    indicated part of the passage under the hypotheses in the statement
    below. *)
Theorem phi_comp sigma tau x : phi (sigma*tau)%g x = phi tau (phi sigma x).
Proof.
apply: (basis_linear_ext he (phi (sigma*tau)%g) (linear_comp (phi tau) (phi sigma))) x.
by move=> i; change (phi (sigma*tau)%g (e i) = phi tau (phi sigma (e i))); rewrite !phiE permM.
Qed.
(** Source for [phi_id]: Federer (1969), 1.3.4, p. 16, last paragraph,
    permutation endomorphisms. In words: The endomorphism sending each basis
    vector to its permuted basis vector has determinant equal to the
    permutation index; consequently index is multiplicative. Formalises the
    indicated part of the passage under the hypotheses in the statement
    below. *)
Lemma phi_id x : phi 1%g x = x.
Proof.
apply: (basis_linear_ext he (phi 1%g) (linear_id V)) x => i.
by rewrite phiE perm1.
Qed.

Hypothesis h2 : (1 + 1 : K) != 0.

(** Source for [phi_top]: Federer (1969), 1.3.4, p. 16, last paragraph,
    permutation endomorphisms. In words: The endomorphism sending each basis
    vector to its permuted basis vector has determinant equal to the
    permutation index; consequently index is multiplicative. Formalises the
    indicated part of the passage under the hypotheses in the statement
    below. *)
Lemma phi_top sigma : exterior_power_map (phi sigma) n (top_vector e) =
  FedererPermutation.index K sigma *: top_vector e.
Proof.
apply: val_inj.
change (exterior_algebra_map (phi sigma) (exterior_word [seq e i | i <- enum 'I_n]) =
  FedererPermutation.index K sigma *: exterior_word [seq e i | i <- enum 'I_n]).
rewrite exterior_algebra_map_word -map_comp.
have hm : [seq phi sigma (e i) | i <- enum 'I_n] =
    [seq e i | i <- permutation_sequence sigma].
  change ([seq phi sigma (e i) | i <- enum 'I_n] =
    [seq e i | i <- [seq sigma i | i <- enum 'I_n]]).
  rewrite -(map_comp e sigma (enum 'I_n)); apply: eq_map => i; exact: phiE.
rewrite hm; exact: exterior_word_permutation.
Qed.

(** Source for [det_phi]: Federer (1969), 1.3.4, p. 16, last paragraph,
    permutation endomorphisms. In words: The endomorphism sending each basis
    vector to its permuted basis vector has determinant equal to the
    permutation index; consequently index is multiplicative. Formalises the
    indicated part of the passage under the hypotheses in the statement
    below. *)
Theorem det_phi sigma : det h2 he (phi sigma) = FedererPermutation.index K sigma.
Proof.
apply: (@top_scalar_injective K h2 n V e he).
by rewrite -detE phi_top.
Qed.

(** Source for [permutation_index_multiplicative]: Federer (1969), 1.3.4, p.
    16, last paragraph, permutation endomorphisms. In words: The
    endomorphism sending each basis vector to its permuted basis vector has
    determinant equal to the permutation index; consequently index is
    multiplicative. Supporting lemma for this passage; not separately stated
    in the book. *)
Theorem permutation_index_multiplicative (sigma tau : 'S_n) :
  FedererPermutation.index K (sigma*tau)%g =
    FedererPermutation.index K sigma * FedererPermutation.index K tau.
Proof.
rewrite -(det_phi (sigma*tau)%g) -(det_phi sigma) -(det_phi tau).
have hf : phi (sigma*tau)%g =1 linear_comp (phi tau) (phi sigma).
  move=> x; exact: phi_comp.
by rewrite (det_ext h2 he hf) det_comp mulrC.
Qed.
(** Source for [permutation_index_one]: Federer (1969), 1.3.4, p. 16, last
    paragraph, permutation endomorphisms. In words: The endomorphism sending
    each basis vector to its permuted basis vector has determinant equal to
    the permutation index; consequently index is multiplicative. Supporting
    lemma for this passage; not separately stated in the book. *)
Lemma permutation_index_one : FedererPermutation.index K (1%g : 'S_n) = 1.
Proof.
rewrite -(det_phi 1%g).
have hf : phi 1%g =1 linear_id V := phi_id.
by rewrite (det_ext h2 he hf) det_id.
Qed.
End PermutationEndomorphisms.

(** Federer 1.3.4: index is multiplicative for every permutation. The
    coordinate space supplies a basis without an extra existence premise. *)
(** Source for [index_multiplicative]: Federer (1969), 1.3.4, p. 16, last
    paragraph, permutation endomorphisms. In words: The endomorphism sending
    each basis vector to its permuted basis vector has determinant equal to
    the permutation index; consequently index is multiplicative. Formalises
    the indicated part of the passage under the hypotheses in the statement
    below. *)
Theorem index_multiplicative (K : fieldType) (h2 : (1 + 1 : K) != 0)
    n (sigma tau : 'S_n) :
  FedererPermutation.index K (sigma*tau)%g =
    FedererPermutation.index K sigma * FedererPermutation.index K tau.
Proof.
exact: (@permutation_index_multiplicative K n (coordinate_space K n)
  (@coordinate_basis K n) (coordinate_basisP K n) h2 sigma tau).
Qed.

(** Source for [index_one]: Federer (1969), 1.3.4, p. 16, last paragraph,
    permutation endomorphisms. In words: The endomorphism sending each basis
    vector to its permuted basis vector has determinant equal to the
    permutation index; consequently index is multiplicative. Formalises the
    indicated part of the passage under the hypotheses in the statement
    below. *)
Theorem index_one (K : fieldType) (h2 : (1 + 1 : K) != 0) n :
  FedererPermutation.index K (1%g : 'S_n) = 1.
Proof.
exact: (@permutation_index_one K n (coordinate_space K n)
  (@coordinate_basis K n) (coordinate_basisP K n) h2).
Qed.
