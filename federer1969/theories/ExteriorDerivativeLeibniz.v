(** Federer (1969), 4.1.6, p. 353: the
    graded Leibniz identity for differentiable real
    forms in the actual induced multilinear norms.
    Boundedness of the original alternating product
    is proved from its existing shuffle bound;
    no extra continuity hypothesis is imposed. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions reals.
From Federer Require Import Hom Bilinear RealNormUP NormDifferentialUP
  NormDifferentialBilinearProduct NormBilinearDifferentialAlgebra
  InnerNorm HilbertFormCompactness EuclideanInnerProduct GrassmannAbbreviations Alternating AlternatingProduct
  ScalarCoefficients ScalarTensorContraction AlternatingFormNormUP
  MixedAlternatingProduct MixedAlternatingProductNorm MixedOrdinaryFormProduct
  ExteriorDifferentialUP ExteriorDifferentialSealed ExteriorDerivativeUP
  ExteriorDifferentialLeibnizAlgebra.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [exterior_derivative_leibniz]: the third
    original displayed identity on p. 353,
    Federer 4.1.6. Its two homogeneous terms
    are compared in the original full alternating
    algebra, with exactly the printed sign. *)
Theorem exterior_derivative_leibniz (R:realType) (h2:(1+1:R)!=0) n p q
    (P:A_m (R_n R n) R^o p->R) (Q:A_m (R_n R n) R^o q->R)
    (T:A_m (R_n R n) R^o (p+q)->R)
    (hNP:is_real_norm P) (hNQ:is_real_norm Q) (hNT:is_real_norm T)
    (hP:is_alternating_form_norm (inner_norm (@euclidean_inner_productP R n)) (fun c:R^o=>`|c|) P)
    (hQ:is_alternating_form_norm (inner_norm (@euclidean_inner_productP R n)) (fun c:R^o=>`|c|) Q)
    (hT:is_alternating_form_norm (inner_norm (@euclidean_inner_productP R n)) (fun c:R^o=>`|c|) T)
    (U:R_n R n->Prop) (phi:R_n R n->A_m (R_n R n) R^o p)
    (psi:R_n R n->A_m (R_n R n) R^o q) a
    (b:A_m (R_n R n) R^o p.+1) (c:A_m (R_n R n) R^o q.+1):
  has_exterior_derivative (inner_norm (@euclidean_inner_productP R n)) P U phi a b->
  has_exterior_derivative (inner_norm (@euclidean_inner_productP R n)) Q U psi a c->
  exists d: A_m (R_n R n) R^o (p+q).+1,
    has_exterior_derivative (inner_norm (@euclidean_inner_productP R n)) T U
      (fun x=>form_wedge h2 (scalar_bilinear R) (phi x) (psi x)) a d /\
    form_include d=
      alternating_wedge h2 (scalar_bilinear R) (form_include b) (form_include (psi a))+
      (-1:R)^+p*:alternating_wedge h2 (scalar_bilinear R) (form_include (phi a)) (form_include c).
Proof.
move=>[L [hL hB]] [M [hM hC]].
pose B:=@form_wedge R h2 (R_n R n) R^o _ (scalar_bilinear R) p q.
pose hBi:=@form_wedge_bilinear R h2 (R_n R n) R^o _ (scalar_bilinear R) p q.
have hBound:forall u v,T (B u v)<='C(p+q,p)%:R*(P u*Q v).
  move=>u v.
  have hCoeff:forall u v:R^o,`|u*v|<=1*(`|u|*`|v|) by move=>u' v'; rewrite mul1r normrM.
  have h:=@mixed_alternating_product_norm_bound R h2 (R_n R n) R^o R^o R^o
    (@euclidean_inner_product R n) (@euclidean_inner_productP R n)
    (fun c:R^o=>`|c|) (fun c:R^o=>`|c|) (fun c:R^o=>`|c|)
    (@scalar_absolute_value_norm R) (@scalar_absolute_value_norm R) (@scalar_absolute_value_norm R)
    (fun x y:R^o=>x*y) (scalar_bilinear R) 1 ler01 hCoeff p q P Q T hP hQ hT u v.
  rewrite mixed_same_form_product mulr1 in h; exact:h.
pose DP:=norm_bilinear_product_linear_term hBi (phi a) (psi a) L M.
have hDP:=@norm_differential_bilinear_product R (R_n R n)
  (A_m (R_n R n) R^o p) (A_m (R_n R n) R^o q) (A_m (R_n R n) R^o (p+q))
  (inner_norm (@euclidean_inner_productP R n)) P Q T
  (inner_norm_real_norm (@euclidean_inner_productP R n)) hNP hNQ hNT
  B hBi ('C(p+q,p)%:R) U phi psi a L M (ler0n R _) hBound hL hM.
exists (@ExteriorDifferential.value R h2 n R^o (p+q) DP); split.
- exists DP; split; first exact:hDP. exact:ExteriorDifferential.laws.
- have hBE:=exterior_differential_value_unique (@ExteriorDifferential.laws R h2 n R^o p L) hB.
  have hCE:=exterior_differential_value_unique (@ExteriorDifferential.laws R h2 n R^o q M) hC.
  rewrite -hBE -hCE; exact:exterior_differential_product_linearization.
Qed.
