(** Federer (1969), 4.1.6, pp. 352–353: the signed
    omission formula for a scalar coordinate covector.
    The existing 1.5.3 contraction identity gives the
    induction; no shuffle bijection or exterior algebra
    construction is repeated. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions.
From Federer Require Import AlgebraUP Bilinear Hom Exterior Alternating
  OneFormLinear ScalarTensorContraction LeftInteriorHom LeftCovectorContraction.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section ScalarCovectorWordContraction.
Variable K:fieldType.
Hypothesis h2:(1+1:K)!=0.
Variable V:lmodType K.
Variable alpha:A_m V K^o 1.
Local Notation a := (form_homogeneous alpha).
Local Notation C := (fun z=>left_interior_hom h2 z a).

(** Source for [scalar_covector_unit_contraction]: a
    one-covector contracts the empty word to zero,
    supporting the original omission formula in
    Federer 4.1.6, p. 352. *)
Lemma scalar_covector_unit_contraction:C (exterior_unit V)=0.
Proof.
have hA:a (exterior_unit V)=0.
  apply:(hom_m_degree a _ (exterior_unit_homogeneous V)); by [].
rewrite /left_interior_hom (algebra_map_one (Psi h2 V)).
change (@contract_tensor K (exterior_space V) (exterior_space V) a (tensor_inj (exterior_unit V) (exterior_unit V))=0).
by rewrite contract_tensorE hA scale0r.
Qed.

(** Source for [scalar_covector_word_contraction]: deleting
    each original factor gives the signed coordinate
    contraction formula used for d phi in Federer
    4.1.6, pp. 352–353. The empty word, repeated
    factors and arbitrary ambient dimension are retained. *)
Theorem scalar_covector_word_contraction (s:seq V):
  C (exterior_word s)=\sum_(i< size s)
    (((-1:K)^+(val i))*one_hom alpha (nth 0 s i)) *:
      exterior_word (take i s++drop i.+1 s).
Proof.
elim:s=>[|v s ih].
- by rewrite exterior_word_nil scalar_covector_unit_contraction big_ord0.
- rewrite exterior_word_cons left_covector_product ih big_ord_recl /= expr0 mul1r drop0.
  congr (_+_).
  rewrite (big_morph (fun z=>wedge (exterior_generator v) z)
    (bilDr (wedge_bilinear V) (exterior_generator v))
    (bil0r (wedge_bilinear V) (exterior_generator v))) -sumrN.
  apply:eq_bigr=>i _.
  by rewrite /bump leq0n add1n add0n exterior_word_cons (bilZr (wedge_bilinear V)) exprS mulN1r mulNr scaleNr.
Qed.
End ScalarCovectorWordContraction.
