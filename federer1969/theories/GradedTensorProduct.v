(** Federer, Geometric measure theory (1969); page numbers are printed book
    pages. Scalar fields, generalisations and exceptional cases are governed
    by the explicit hypotheses below. Supporting steps are distinguished
    from statements printed in the book. Erratum reference:
    docs/references/federer-erratum.tex (May 1987), cited by erratum page
    and book page/line. *)

From HB Require Import structures.
From mathcomp Require Import all_boot all_order ssralg.
From Federer Require Import Tensor Bilinear AlgebraUP GradedAlgebra GradedSums
  TensorBilinear Koszul GradedTensor.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Federer 1.2.2. The parameter [s] selects the signed product when true
    and the ordinary product when false. No unit or associativity is assumed. *)
Section Products.
Variable K : fieldType.
Variables A B : graded_algebra K.
Variable s : bool.
Local Notation GA := (algebra_grading A).
Local Notation GB := (algebra_grading B).
Local Notation T := (tensor_space A B).
Local Notation ma := (@graded_mul K A).
Local Notation mb := (@graded_mul K B).

(** Source for [product_factor]: Federer (1969), 1.2.2, p. 12, item (2) and
    the following explanation. In words: The signed tensor-product
    multiplication inserts (-1)^(qr) when the middle factors have degrees q
    and r; signed tensor products of anticommutative algebras are
    anticommutative. Definition or construction used to formalise this
    passage. *)
Definition product_factor a c d b : T := tensor_inj (ma a c) (mb b d).
(** Source for [product_factor_linear]: Federer (1969), 1.2.2, p. 12, item
    (2) and the following explanation. In words: The signed tensor-product
    multiplication inserts (-1)^(qr) when the middle factors have degrees q
    and r; signed tensor products of anticommutative algebras are
    anticommutative. Supporting lemma for this passage; not separately
    stated in the book. *)
Lemma product_factor_linear a c d : linear (product_factor a c d).
Proof.
by move=> k b b'; rewrite /product_factor (proj1 (@graded_bilinear K B) d)
  tensor_inj_addr tensor_inj_scaler.
Qed.
HB.instance Definition _ a c d := GRing.isLinear.Build K B T *:%R
  (product_factor a c d) (product_factor_linear a c d).
(** Source for [product_component]: Federer (1969), 1.2.2, p. 12, item (2)
    and the following explanation. In words: The signed tensor-product
    multiplication inserts (-1)^(qr) when the middle factors have degrees q
    and r; signed tensor products of anticommutative algebras are
    anticommutative. Definition or construction used to formalise this
    passage. *)
Definition product_component a c d q : {linear B -> T} :=
  GRing.Linear.clone _ _ _ _ (product_factor a (degree_sign GA s q c) d) _.
(** Source for [product_pure]: Federer (1969), 1.2.2, p. 12, item (2) and
    the following explanation. In words: The signed tensor-product
    multiplication inserts (-1)^(qr) when the middle factors have degrees q
    and r; signed tensor products of anticommutative algebras are
    anticommutative. Definition or construction used to formalise this
    passage. *)
Definition product_pure a b c d := graded_sum GB (product_component a c d) b.

(** Source for [product_pure_bilinear_ab]: Federer (1969), 1.2.2, p. 12,
    item (2) and the following explanation. In words: The signed
    tensor-product multiplication inserts (-1)^(qr) when the middle factors
    have degrees q and r; signed tensor products of anticommutative algebras
    are anticommutative. Supporting lemma for this passage; not separately
    stated in the book. *)
Lemma product_pure_bilinear_ab c d : bilinear (fun a b => product_pure a b c d).
Proof.
split; last by move=> a; exact: linearP.
move=> b; apply: graded_sum_parameter_linear => q b'.
change (linear (fun a => tensor_inj (ma a (degree_sign GA s q c)) (mb b' d))).
by move=> k a a'; rewrite (proj1 (@graded_bilinear K A) _)
  tensor_inj_addl tensor_inj_scalel.
Qed.
(** Source for [product_pure_bilinear_cd]: Federer (1969), 1.2.2, p. 12,
    item (2) and the following explanation. In words: The signed
    tensor-product multiplication inserts (-1)^(qr) when the middle factors
    have degrees q and r; signed tensor products of anticommutative algebras
    are anticommutative. Supporting lemma for this passage; not separately
    stated in the book. *)
Lemma product_pure_bilinear_cd a b : bilinear (product_pure a b).
Proof.
split=> [d|c]; apply: graded_sum_parameter_linear => q b'.
- change (linear (fun c => tensor_inj (ma a (degree_sign GA s q c)) (mb b' d))).
  by move=> k c c'; rewrite linearP (proj2 (@graded_bilinear K A) a)
    tensor_inj_addl tensor_inj_scalel.
- change (linear (fun d => tensor_inj (ma a (degree_sign GA s q c)) (mb b' d))).
  by move=> k d d'; rewrite (proj2 (@graded_bilinear K B) b')
    tensor_inj_addr tensor_inj_scaler.
Qed.

(** Source for [graded_tensor_mul]: Federer (1969), 1.2.2, p. 12, item (2)
    and the following explanation. In words: The signed tensor-product
    multiplication inserts (-1)^(qr) when the middle factors have degrees q
    and r; signed tensor products of anticommutative algebras are
    anticommutative. Definition or construction used to formalise this
    passage. *)
Definition graded_tensor_mul :=
  tensor_bilinear_extension product_pure_bilinear_ab product_pure_bilinear_cd.
(** Source for [graded_tensor_bilinear]: Federer (1969), 1.2.2, p. 12, item
    (2) and the following explanation. In words: The signed tensor-product
    multiplication inserts (-1)^(qr) when the middle factors have degrees q
    and r; signed tensor products of anticommutative algebras are
    anticommutative. Supporting lemma for this passage; not separately
    stated in the book. *)
Lemma graded_tensor_bilinear : bilinear graded_tensor_mul.
Proof. exact: tensor_bilinear_extension_bilinear. Qed.

(** Source for [graded_tensor_mulE]: Federer (1969), 1.2.2, p. 12, item (2)
    and the following explanation. In words: The signed tensor-product
    multiplication inserts (-1)^(qr) when the middle factors have degrees q
    and r; signed tensor products of anticommutative algebras are
    anticommutative. Formalises the indicated part of the passage under the
    hypotheses in the statement below. *)
Lemma graded_tensor_mulE q r a b c d : homogeneous GB q b -> homogeneous GA r c ->
  graded_tensor_mul (tensor_inj a b) (tensor_inj c d) =
  koszul K s q r *: tensor_inj (ma a c) (mb b d).
Proof.
move=> hb hc; rewrite /graded_tensor_mul tensor_bilinear_extensionE /product_pure
  (graded_sum_homogeneous _ hb).
change (tensor_inj (ma a (degree_sign GA s q c)) (mb b d) =
  koszul K s q r *: tensor_inj (ma a c) (mb b d)).
by rewrite (degree_signE s q hc) (bilZr (@graded_bilinear K A)) tensor_inj_scalel.
Qed.

(** Source for [graded_tensor_mul_degree]: Federer (1969), 1.2.2, p. 12,
    item (2) and the following explanation. In words: The signed
    tensor-product multiplication inserts (-1)^(qr) when the middle factors
    have degrees q and r; signed tensor products of anticommutative algebras
    are anticommutative. Formalises the indicated part of the passage under
    the hypotheses in the statement below. *)
Lemma graded_tensor_mul_degree :
  graded_product (tensor_grading_product GA GB) graded_tensor_mul.
Proof.
move=> m n x y hx hy.
move: x hx; apply: tensor_component_induction => [|x x' hx hx'|k x hx|p q a b hpq ha hb].
- rewrite (bil0l graded_tensor_bilinear); exact: homogeneous0.
- rewrite (bilDl graded_tensor_bilinear); exact: homogeneousD hx hx'.
- rewrite (bilZl graded_tensor_bilinear); exact: homogeneousZ hx.
move: y hy; apply: tensor_component_induction => [|y y' hy hy'|k y hy|r t c d hrt hc hd].
- rewrite (bil0r graded_tensor_bilinear); exact: homogeneous0.
- rewrite (bilDr graded_tensor_bilinear); exact: homogeneousD hy hy'.
- rewrite (bilZr graded_tensor_bilinear); exact: homogeneousZ hy.
rewrite (graded_tensor_mulE a d hb hc); apply: homogeneousZ.
have e : (m+n = (p+r)+(q+t))%N by rewrite -hpq -hrt addnACA.
rewrite e.
exact: tensor_homogeneous_pure (graded_mul_degree ha hc) (graded_mul_degree hb hd).
Qed.

(** Source for [graded_tensor]: Federer (1969), 1.2.2, p. 12, item (2) and
    the following explanation. In words: The signed tensor-product
    multiplication inserts (-1)^(qr) when the middle factors have degrees q
    and r; signed tensor products of anticommutative algebras are
    anticommutative. Definition or construction used to formalise this
    passage. *)
Definition graded_tensor : graded_algebra K :=
  @GradedAlgebra K T (tensor_grading_product GA GB) graded_tensor_mul
    graded_tensor_bilinear graded_tensor_mul_degree.
End Products.

Section OrdinaryAndUniqueness.
Variable K : fieldType.
Variables A B : graded_algebra K.
Local Notation GA := (algebra_grading A).
Local Notation GB := (algebra_grading B).
(** Source for [ordinary_tensor_mulE]: Federer (1969), 1.2.2, p. 11, item
    (1), ordinary tensor-product multiplication. In words: The ordinary
    product of a tensor b and c tensor d is the tensor of the two products
    ac and bd. Formalises the indicated part of the passage under the
    hypotheses in the statement below. *)
Lemma ordinary_tensor_mulE a b c d :
  @graded_tensor_mul K A B false (tensor_inj a b) (tensor_inj c d) =
  tensor_inj (@graded_mul K A a c) (@graded_mul K B b d).
Proof.
rewrite /graded_tensor_mul tensor_bilinear_extensionE /product_pure /graded_sum.
under eq_bigr do rewrite /product_component /product_factor /= degree_sign_false.
change (\sum_(i < grade_bound GB b)
  product_factor a c d (grade GB i b) = product_factor a c d b).
exact: (graded_sum_constant GB (GRing.Linear.clone _ _ _ _ (product_factor a c d) _) b).
Qed.
(** Source for [graded_tensor_mul_unique]: Federer (1969), 1.2.2, p. 12,
    item (2) and the following explanation. In words: The signed
    tensor-product multiplication inserts (-1)^(qr) when the middle factors
    have degrees q and r; signed tensor products of anticommutative algebras
    are anticommutative. Formalises the indicated part of the passage under
    the hypotheses in the statement below. *)
Lemma graded_tensor_mul_unique s
  (m : tensor_space A B -> tensor_space A B -> tensor_space A B) (hm : bilinear m) :
  (forall p q r t a b c d, homogeneous GA p a -> homogeneous GB q b ->
    homogeneous GA r c -> homogeneous GB t d ->
    m (tensor_inj a b) (tensor_inj c d) = koszul K s q r *:
      tensor_inj (@graded_mul K A a c) (@graded_mul K B b d)) ->
  forall x y, m x y = graded_tensor_mul s x y.
Proof.
move=> h; apply: (tensor_homogeneous_bilinear_ext (GA:=GA) (GB:=GB) (GC:=GA) (GD:=GB)
  hm (graded_tensor_bilinear A B s)) => p q r t a b c d ha hb hc hd.
by rewrite (h p q r t a b c d ha hb hc hd) (graded_tensor_mulE s a d hb hc).
Qed.
End OrdinaryAndUniqueness.
