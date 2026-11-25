(** Federer (1969), 4.1.8, p. 360: the original
    separated-test characterisation uses the factor pairing
    for the canonical direct sum. The supporting algebra below
    applies the proved inverse maps of 1.3.2, p. 14,
    and the original covector product of 1.4.2, p. 18. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import BoundedHom HomogeneousHom GradedComponents Hom Tensor TensorUP TensorMaps AlgebraUP ExteriorAlgebra ExteriorGrading
  ExteriorHomogeneousProducts ExteriorMaps ExteriorDirectSum ExteriorDiagonal
  AlternatingForms AlternatingExtension AlternatingSum AlternatingDual AlternatingProduct
  ScalarCoefficients Convolution ExteriorBlockDiagonal PairedTensorSeparateMaps.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section CovectorBlockProductPairing.
Variable K:fieldType.
Hypothesis h2:(1+1:K)!=0.
Variables V X Y:lmodType K.
Variables (p:{linear V->X}) (q:{linear V->Y}).

(** Source for [covector_block_product_include]: the separated
    covector product is the two original covectors applied
    after the direct-sum exterior map, supporting Federer
    4.1.8, p. 360, by 1.3.2 and 1.4.2.
    The equality holds on the full exterior algebra. *)
Theorem covector_block_product_include k l (a:A_m X K^o k) (b:A_m Y K^o l) z:
  form_include (form_wedge h2 (scalar_bilinear K) (A_m_dual p a) (A_m_dual q b)) z=
    paired_tensor (scalar_bilinear K) (form_include a) (form_include b)
      (@ExteriorDirectSum.alpha K h2 V X Y p q z).
Proof.
have hp:hom_comp (form_include a) (hom_of_linear (exterior_algebra_map p))=
    (form_include (A_m_dual p a):Hom (exterior_space V) K^o).
  apply:hom_ext=>x.
  change (form_include a (exterior_algebra_map p x)=form_include (A_m_dual p a) x).
  by rewrite -A_star_dual_include A_star_dualE.
have hq:hom_comp (form_include b) (hom_of_linear (exterior_algebra_map q))=
    (form_include (A_m_dual q b):Hom (exterior_space V) K^o).
  apply:hom_ext=>x.
  change (form_include b (exterior_algebra_map q x)=form_include (A_m_dual q b) x).
  by rewrite -A_star_dual_include A_star_dualE.
by rewrite form_wedge_include alternating_wedgeE -exterior_diagonal_block_map
  paired_tensor_separate_maps hp hq.
Qed.

Variables (P:{linear X->V}) (Q:{linear Y->V}).
Hypotheses (hP:cancel P p) (hQ:cancel Q q)
  (hDecomposition:forall v,P (p v)+Q (q v)=v).

(** Source for [covector_block_product_factorisation]: evaluating
    the original pulled-back covector product on the exterior
    product of the two included multivectors factors exactly,
    supporting Federer 4.1.8, p. 360. All four degrees
    are independent, so off-diagonal vanishing is retained. *)
Theorem covector_block_product_factorisation i j k l
    (a:A_m X K^o k) (b:A_m Y K^o l)
    (xi:exterior_power X i) (eta:exterior_power Y j):
  form_include (form_wedge h2 (scalar_bilinear K) (A_m_dual p a) (A_m_dual q b))
    (wedge (exterior_algebra_map P (component_val xi))
      (exterior_algebra_map Q (component_val eta)))=
    form_include a (component_val xi)*form_include b (component_val eta).
Proof.
rewrite covector_block_product_include.
have hBlock:=@alpha_beta K h2 V X Y p P q Q hP hQ hDecomposition
  (tensor_inj (component_val xi) (component_val eta)).
rewrite betaE in hBlock.
by rewrite hBlock paired_tensorE.
Qed.
End CovectorBlockProductPairing.
