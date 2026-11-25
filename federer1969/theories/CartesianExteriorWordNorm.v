(** Federer (1969), 1.7.11, p. 36: exterior
    words in separate Cartesian factors have multiplicative
    norms. Supporting the vertical/horizontal Jacobian blocks
    in 3.2.48, pp. 285–286, including singular words. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom TensorUP Bilinear InnerProductUP ProductInner ProductLinearMaps
  OrthogonalMaps ExteriorMaps ExteriorNorm ExteriorNormNaturality ExteriorGrading
  FiniteExteriorPowers CovectorProductNaturality ExteriorHomogeneousProducts OrthogonalWordsWedgeNorm.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [cartesian_exterior_word_norm]: the product
    inner metric in 1.7.11, p. 36, makes the
    exterior words of the two factors orthogonal. The
    equality supports the two Jacobian blocks of 3.2.48,
    p. 286, without a linear-independence or rank premise. *)
Theorem cartesian_exterior_word_norm (R:realType) (h2:(1+1:R)!=0)
    (V W:lmodType R) BV BW
    (hV:@is_inner_product R V BV) (hW:@is_inner_product R W BW)
    r s (e:'I_r->V) (f:'I_s->W):
  exterior_norm h2 (product_inner_productP hV hW)
    (exterior_product
      (exterior_power_map (GRing.Linear.clone _ _ _ _ (@product_left R V W) _) r
        (e_lambda e (ord_tuple r)))
      (exterior_power_map (GRing.Linear.clone _ _ _ _ (@product_right R V W) _) s
        (e_lambda f (ord_tuple s))))=
  exterior_norm h2 hV (e_lambda e (ord_tuple r))*
    exterior_norm h2 hW (e_lambda f (ord_tuple s)).
Proof.
pose P:lmodType R:=[the lmodType R of (V*W)%type].
pose i:{linear V->P}:=GRing.Linear.clone _ _ _ _ (@product_left R V W) _.
pose j:{linear W->P}:=GRing.Linear.clone _ _ _ _ (@product_right R V W) _.
have hi:is_orthogonal_map BV (product_inner hV hW) i.
  move=>x y; by rewrite product_innerE /i /product_left
    (bil0l (inner_bilinear hW)) addr0.
have hj:is_orthogonal_map BW (product_inner hV hW) j.
  move=>x y; by rewrite product_innerE /j /product_right
    (bil0l (inner_bilinear hV)) add0r.
have hCross a b:product_inner hV hW (i (e a)) (j (f b))=0.
  by rewrite product_innerE /i /j /product_left /product_right
    (bil0r (inner_bilinear hV)) (bil0l (inner_bilinear hW)) add0r.
have hFirst:exterior_power_map i r (e_lambda e (ord_tuple r))=
    e_lambda (fun a=>i (e a)) (ord_tuple r).
  exact:exterior_basis_product_natural.
have hSecond:exterior_power_map j s (e_lambda f (ord_tuple s))=
    e_lambda (fun b=>j (f b)) (ord_tuple s).
  exact:exterior_basis_product_natural.
change (exterior_norm h2 (product_inner_productP hV hW)
  (exterior_product (exterior_power_map i r (e_lambda e (ord_tuple r)))
    (exterior_power_map j s (e_lambda f (ord_tuple s))))=
  exterior_norm h2 hV (e_lambda e (ord_tuple r))*
    exterior_norm h2 hW (e_lambda f (ord_tuple s))).
rewrite hFirst hSecond (@orthogonal_words_wedge_norm R h2 P _
  (product_inner_productP hV hW) r s _ _ hCross) -hFirst -hSecond.
by rewrite (exterior_norm_orthogonal_natural h2 hV (product_inner_productP hV hW) hi)
  (exterior_norm_orthogonal_natural h2 hW (product_inner_productP hV hW) hj).
Qed.
