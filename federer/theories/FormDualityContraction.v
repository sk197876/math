(** Federer (1969), 4.1.6, p. 354: the
    last product law of 1.5.2 turns a one-covector
    contraction into exterior multiplication after
    duality. Use the proved inverse and product laws;
    equal degree expressions are identified explicitly. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions.
From Federer Require Import Hom Exterior Alternating AlternatingCoordinates InteriorMultiplication
  DualityMaps DualityIsomorphism DualityInverse DualityProductLaws DualProductContraction
  ProductContraction OneCovectorInterior ComassWedgeSymmetry ScalarCoefficients.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section FormDualityContraction.
Variable K:fieldType.
Hypothesis h2:(1+1:K)!=0.
Variable V:lmodType K.
Variable n:nat.
Variable e:'I_n->V.
Variable omega:'I_n->A_m V K^o 1.
Hypothesis he:is_basis e.
Hypothesis hDual:forall i j,omega i [tuple e j]=if i==j then 1 else 0.
Local Notation top:=(e_lambda e (val (Lambda_top n))).
Local Notation volume:=(omega_lambda h2 omega (Lambda_top n)).

(** Source for [equal_degree_forms_from_top_contraction]:
    the original top duality is injective, so comparing
    its values proves equality of forms,
    supporting Federer 4.1.6, p. 354. *)
Lemma equal_degree_forms_from_top_contraction r s (h:r=s) (hs:(s<=n)%N)
    (a:A_m V K^o r) (b:A_m V K^o s):
  left_interior_hom h2 (component_val top) (form_homogeneous a)=
    left_interior_hom h2 (component_val top) (form_homogeneous b)->
  form_include a=form_include b.
Proof.
move=>hValue.
have hEqual:form_reindex h a=b.
  apply:(bij_inj (@D_upper_isomorphism K h2 V n e omega he hDual s hs)).
  apply:val_inj.
  change (left_interior_hom h2 (component_val top) (form_homogeneous (form_reindex h a))=
    left_interior_hom h2 (component_val top) (form_homogeneous b)).
  rewrite form_reindex_Hom; exact:hValue.
have hIncluded:=congr1 (@form_include K V K^o s) hEqual.
by rewrite form_reindex_include in hIncluded.
Qed.

(** Source for [duality_one_covector_contraction]: the
    original identity D_p(xi) wedge alpha equals
    D_(p-1)(xi contracted by alpha),
    used in Federer 4.1.6, p. 354.
    Write the positive input degree as p+1. *)
Theorem duality_one_covector_contraction p (hp:(p.+1<=n)%N)
    (xi:exterior_power V p.+1) (a:A_m V K^o 1):
  form_include (form_wedge h2 (scalar_bilinear K) (D_p volume hp xi) a)=
    form_include (D_p volume (leq_trans (leqnSn p) hp)
      (positive_one_covector_interior h2 xi a)).
Proof.
have hDegree:(n-p.+1+1)%N=(n-p)%N by rewrite addn1; exact:subnSK hp.
apply:(equal_degree_forms_from_top_contraction hDegree (leq_subr p n)).
rewrite form_wedge_hom left_interior_hom_associative
  (@duality_inverse_interior K h2 V n e omega he hDual p.+1 hp xi)
  (@duality_inverse_interior K h2 V n e omega he hDual p (leq_trans (leqnSn p) hp)
    (positive_one_covector_interior h2 xi a)).
by rewrite positive_one_covector_interior_value.
Qed.
End FormDualityContraction.
