(** Federer (1969), 3.2.23, p. 260: the Jacobian of a product
    factors because its two families of differential vectors occupy
    orthogonal coordinate blocks. This supporting consequence of the
    equality criterion in 1.7.5, p. 32 includes dependent families. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import InnerProductUP ExteriorNorm ExteriorGrading FiniteExteriorPowers
  ExteriorHomogeneousProducts SimpleElementary SimpleWedgeEquality
  ProductAssociatedOrthogonality Bilinear.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [orthogonal_words_wedge_norm]: supporting product
    Jacobian equality in Federer 3.2.23, p. 260, by the exact
    orthogonal-space equality criterion of 1.7.5, p. 32.
    A zero word is handled separately rather than applying the
    nonzero criterion to a dependent family. Empty words are retained. *)
Theorem orthogonal_words_wedge_norm (R:rcfType) (h2:(1+1:R)!=0)
    (V:lmodType R) (B:V->V->R) (hB:is_inner_product B) p q
    (e:'I_p->V) (f:'I_q->V):
  (forall i j,B (e i) (f j)=0) ->
  exterior_norm h2 hB (exterior_product (e_lambda e (ord_tuple p))
    (e_lambda f (ord_tuple q)))=
  exterior_norm h2 hB (e_lambda e (ord_tuple p))*
    exterior_norm h2 hB (e_lambda f (ord_tuple q)).
Proof.
move=>hCross.
case:(eqVneq (e_lambda e (ord_tuple p)) 0)=>[he|he].
- by rewrite he (bil0l (@exterior_product_bilinear R V p q)) !exterior_norm_zero mul0r.
case:(eqVneq (e_lambda f (ord_tuple q)) 0)=>[hf|hf].
- by rewrite hf (bil0r (@exterior_product_bilinear R V p q)) !exterior_norm_zero mulr0.
apply:(simple_wedge_norm_equality h2 hB he hf (product_simple e) (product_simple f)).2.
exact:((product_associated_orthogonality h2 hB he hf).2 hCross).
Qed.
