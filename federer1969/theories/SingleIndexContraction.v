(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import InteriorDecomposition.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.6.1, multiplying by e_i: the one-element increasing
    index and the vanishing contraction when i is absent from lambda. *)
(** Source for [Lambda_single]: Federer (1969), 1.6.1, p. 23, last
    paragraph, basis extension and the Grassmann-coordinate argument. In
    words: Extend a basis of the associated space to an ambient finite
    basis; multiplying the Grassmann expansion by e_i forces every
    coefficient omitting i to vanish. Definition or construction used to
    formalise this passage. *)
Definition Lambda_single n (i : 'I_n) : Lambda n 1 := Sub [tuple i] isT.
(** Source for [Lambda_single_set]: Federer (1969), 1.6.1, p. 23, last
    paragraph, basis extension and the Grassmann-coordinate argument. In
    words: Extend a basis of the associated space to an ambient finite
    basis; multiplying the Grassmann expansion by e_i forces every
    coefficient omitting i to vanish. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma Lambda_single_set n (i : 'I_n) : Lambda_set (Lambda_single i) = [set i].
Proof. by apply/setP=> j; rewrite /Lambda_set /Lambda_single !inE /=. Qed.
(** Source for [e_lambda_single_val]: Federer (1969), 1.6.1, p. 23, last
    paragraph, basis extension and the Grassmann-coordinate argument. In
    words: Extend a basis of the associated space to an ambient finite
    basis; multiplying the Grassmann expansion by e_i forces every
    coefficient omitting i to vanish. Supporting lemma for this passage; not
    separately stated in the book. *)
Lemma e_lambda_single_val (K : fieldType) (V : lmodType K) n (e : 'I_n -> V) i :
  component_val (e_lambda e (val (Lambda_single i))) = exterior_generator (e i).
Proof. by rewrite e_lambdaE /= exterior_word_cons exterior_word_nil wedge_unitr. Qed.

Section Contraction.
Variable K : fieldType.
Hypothesis h2 : (1+1 : K) != 0.
Variable V : lmodType K.
Variable n : nat.
Variable e : 'I_n -> V.
Variable omega : 'I_n -> A_m V K^o 1.
Hypothesis he : is_basis e.
Hypothesis hdual : forall i j, omega i [tuple e j] = if i == j then 1 else 0.
(** Source for [basis_covector_absent]: Federer (1969), 1.6.1, p. 23, last
    paragraph, basis extension and the Grassmann-coordinate argument. In
    words: Extend a basis of the associated space to an ambient finite
    basis; multiplying the Grassmann expansion by e_i forces every
    coefficient omitting i to vanish. Supporting lemma for this passage; not
    separately stated in the book. *)
Theorem basis_covector_absent m (lambda : Lambda n m) i :
  i \notin Lambda_set lambda ->
  right_interior_hom (exterior_generator (e i)) (form_homogeneous (omega_lambda h2 omega lambda)) = 0.
Proof.
case: m lambda => [|m] lambda hi; first exact: v_interior_zero_degree.
have hn : ~~ (Lambda_set (Lambda_single i) \subset Lambda_set lambda).
  by rewrite Lambda_single_set sub1set.
have hz := @right_interior_basis_zero K h2 V n 1 m.+1 e omega he hdual
  (leq0n m) (Lambda_single i) lambda hn.
apply: hom_ext => x; rewrite right_interior_homE hom_zeroE.
have hx := congr1 (fun f : A_m V K^o (m.+1-1) => form_homogeneous f x) hz.
by rewrite right_interior_homogeneousE e_lambda_single_val form_hom_zeroE in hx.
Qed.
End Contraction.

(** Federer 1.6.1: a covector with zero contraction at v annihilates
    every xi with xi wedge v=0. This follows from 1.5.3 and will be used
    to extract the coefficients in the displayed basis expansion. *)
Section Annihilation.
Variable K : fieldType.
Hypothesis h2 : (1+1 : K) != 0.
Variable V : lmodType K.
Variable v : V.
Variable alpha : A_m V K^o 1.
Hypothesis hv : one_hom alpha v = 1.
Variable phi : Hom (exterior_space V) K^o.
Hypothesis hphi : right_interior_hom (exterior_generator v) phi = 0.
(** Source for [annihilator_pairing_zero]: Federer (1969), 1.6.1, p. 23,
    last paragraph, basis extension and the Grassmann-coordinate argument.
    In words: Extend a basis of the associated space to an ambient finite
    basis; multiplying the Grassmann expansion by e_i forces every
    coefficient omitting i to vanish. Supporting lemma for this passage; not
    separately stated in the book. *)
Theorem annihilator_pairing_zero (xi : exterior_space V) :
  wedge xi (exterior_generator v) = 0 -> phi xi = 0.
Proof.
move=> hz.
have h :
    convolution (scalar_bilinear K) (Psi h2 V) phi (form_homogeneous alpha)
      (wedge xi (exterior_generator v)) =
    one_hom alpha v * phi xi -
      convolution (scalar_bilinear K) (Psi h2 V)
        (right_interior_hom (exterior_generator v) phi) (form_homogeneous alpha) xi.
  exact: (@right_covector_product K h2 V alpha phi v xi).
rewrite hz in h.
rewrite linear0 in h.
rewrite hv mul1r in h.
rewrite hphi in h.
rewrite (bil0l (@convolution_bilinear K (exterior_space V) K^o _
  (scalar_bilinear K) (Psi h2 V))) in h.
rewrite hom_zeroE subr0 in h.
exact: esym h.
Qed.
End Annihilation.
