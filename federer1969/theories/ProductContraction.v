(** Federer (1969), 1.6.5, pp. 25-26. The two sides of the product-space
    contraction identity, including their degrees, bilinearity and
    dependence on the chosen top vector and form. The operations used below
    are the existing sealed exterior algebra and the characterised interior
    products. No assertion of the identity is built into a definition. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import SimpleVectors ProductSpaceMaps.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [product_contraction_bound]: Federer 1.6.5, p. 25,
    hypothesis k+l>=n and exponent 2n-k-l. Supporting degree bound
    ensuring that the duality map D^(2n-k-l) is defined. *)
Lemma product_contraction_bound n k l (hk : (k <= n)%N)
  (hl : (l <= n)%N) (hkl : (n <= k+l)%N) : ((n-k)+(n-l) <= n)%N.
Proof.
by rewrite -(@leq_subRL (n-k) (n-l) n (leq_subr k n)) (subKn hk) leq_subLR addnC.
Qed.

(** Source for [product_contraction_degree]: Federer 1.6.5, p. 25,
    output degree k+l-n in the displayed identity. Supporting
    equality of the natural-number degree expressions. *)
Lemma product_contraction_degree n k l (hk : (k <= n)%N) (hl : (l <= n)%N) :
  (n-((n-k)+(n-l)) = k+l-n)%N.
Proof. by rewrite subnDA (subKn hk) (subnBA _ hl). Qed.

Import FedererProduct.
Module FedererProductContraction.
Section Contraction.
Variable K : fieldType.
Hypothesis h2 : (1+1 : K) != 0.
Variable V : lmodType K.
Variables n k l : nat.
Hypotheses (hk : (k <= n)%N) (hl : (l <= n)%N) (hkl : (n <= k+l)%N).
Local Notation W := (GRing.Lmodule.clone K (V * V)%type _).
Variable volume : A_m V K^o n.
Variable top : exterior_power V n.

(** Source for [product_contraction]: Federer 1.6.5, p. 25,
    left member of the displayed identity. Definition: include the
    two multivectors into opposite factors, take their product, and
    contract by the pullback of the volume under the difference map. *)
Definition product_contraction (xi : exterior_power V k) (eta : exterior_power V l) :=
  left_interior h2 hkl
    (exterior_product (exterior_power_map (P_map V) k xi)
      (exterior_power_map (Q_map V) l eta))
    (A_m_dual (f_map V) volume).

(** Source for [diagonal_dual_product]: Federer 1.6.5, p. 25,
    right member of the displayed identity. Definition: take the
    dual product, apply upper duality and the induced diagonal map,
    with the printed sign. The explicit reindexing only reconciles
    the equal degrees n-(n-k+n-l) and k+l-n. *)
Definition diagonal_dual_product (xi : exterior_power V k) (eta : exterior_power V l) :=
  (-1 : K)^+((n-k) * l) *:
    exterior_power_map (g_map V) (k+l-n)
      (exterior_reindex (product_contraction_degree hk hl)
        (D_upper h2 top (product_contraction_bound hk hl hkl)
          (form_wedge h2 (scalar_bilinear K)
            (D_p volume hk xi) (D_p volume hl eta)))).

(** Source for [product_contraction_bilinear]: Federer 1.6.5,
    pp. 25-26, extension of the displayed computation to arbitrary
    multivectors. Supporting bilinearity of the left member. *)
Lemma product_contraction_bilinear : bilinear product_contraction.
Proof.
split.
- move=> eta c x y; rewrite /product_contraction linearP
    (proj1 (exterior_product_bilinear W k l))
    (proj1 (left_interior_bilinear h2 W hkl)); by [].
- move=> xi c x y; rewrite /product_contraction linearP
    (proj2 (exterior_product_bilinear W k l))
    (proj1 (left_interior_bilinear h2 W hkl)); by [].
Qed.

(** Source for [diagonal_dual_product_bilinear]: Federer 1.6.5,
    pp. 25-26, extension to arbitrary multivectors. Supporting
    bilinearity of the right member, using the linear duality maps. *)
Lemma diagonal_dual_product_bilinear : bilinear diagonal_dual_product.
Proof.
split.
- move=> eta c x y; rewrite /diagonal_dual_product linearP
    (proj1 (form_wedge_bilinear h2 V (scalar_bilinear K) (n-k) (n-l))) !linearP; by [].
- move=> xi c x y; rewrite /diagonal_dual_product linearP
    (proj2 (form_wedge_bilinear h2 V (scalar_bilinear K) (n-k) (n-l))) !linearP; by [].
Qed.
End Contraction.
End FedererProductContraction.
