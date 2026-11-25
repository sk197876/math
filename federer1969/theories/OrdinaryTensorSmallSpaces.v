(** Federer 1.4.5, p. 20: zero-factor and line-factor exceptions. The
    ordinary multiplication is identified with the existing degree-zero
    sign choice of 1.2.2. No tensor algebra or exterior algebra is rebuilt. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import Graded AlternatingCoordinates
  OrdinaryTensorLowDegrees ZeroGradedTensorSigns ExteriorAnticommutativity TraceBasisProduct.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Section Exceptions.
Variable K : fieldType.
Hypothesis h2 : (1+1 : K) != 0.
Variables V W : lmodType K.
Local Notation U := (alternating_unital_algebra h2 V (scalar_algebra K)).
Local Notation E := (exterior_algebra W).
Local Notation T := (algebra_tensor U E).
Local Notation A := (@alternating_algebra K h2 V K^o
  (fun x y : K^o => x*y) (scalar_bilinear K)).
Local Notation B := (@graded_exterior_algebra K W).
Local Notation GA := (A_star_grading V K^o).
Local Notation GB := (exterior_grading W).
Local Notation G := (tensor_grading_product GA GB).

(** Source for [ordinary_tensor_graded_product_agreement]: supporting
    connection for Federer 1.4.5, p. 20. Its ordinary algebra tensor
    multiplication is exactly the unsigned product of 1.2.2(1), p. 11.
    Apply bilinear tensor extensionality and the two existing pure formulas. *)
Lemma ordinary_tensor_graded_product_agreement : forall x y : T,
    alg_mul T x y = @graded_tensor_mul K A B false x y.
Proof.
apply: (tensor_bilinear_ext (alg_bilinear T)
  (graded_tensor_bilinear A B false)) => a b c d.
by rewrite ordinary_tensor_productE ordinary_tensor_mulE.
Qed.

(** Source for [ordinary_tensor_zero_left_anticommutative]: corrected
    zero-factor exception in Federer 1.4.5, p. 20. If V=0, the left
    grading has no positive components. The two products agree, and the
    signed anticommutativity theorem of 1.2.2(2), p. 12, applies. *)
Theorem ordinary_tensor_zero_left_anticommutative :
    (forall v : V, v=0) -> graded_anticommutative G (alg_mul T).
Proof.
move=> hV.
have he := zero_space_empty_basis hV.
have hz p (x : A) : (0<p)%N -> homogeneous GA p x -> x=0.
  move=> hp hx.
  exact: (@finite_covector_homogeneous_above_dimension K h2 V 0
    (fun _ => 0) he p x hp hx).
have hs := @zero_left_grade_tensor_signs_agree K A B hz.
have ha : graded_anticommutative (algebra_grading A) (@graded_mul K A).
  exact: (@alternating_wedge_anticommutative K h2 V K^o
    (fun x y : K^o => x*y) (scalar_bilinear K) (@mulrC K)).
have hb : graded_anticommutative (algebra_grading B) (@graded_mul K B).
  exact: exterior_anticommutative.
move=> m n x y hx hy.
rewrite !ordinary_tensor_graded_product_agreement !hs.
exact: (@signed_tensor_anticommutative K A B ha hb m n x y hx hy).
Qed.

(** Source for [ordinary_tensor_zero_right_anticommutative]: corrected
    zero-factor exception in Federer 1.4.5, p. 20. If W=0, the right
    grading has only degree zero, so the signed theorem applies to the
    original ordinary product, including infinite-dimensional V. *)
Theorem ordinary_tensor_zero_right_anticommutative :
    (forall w : W, w=0) -> graded_anticommutative G (alg_mul T).
Proof.
move=> hW.
have he := zero_space_empty_basis hW.
have hz p (x : B) : (0<p)%N -> homogeneous GB p x -> x=0.
  move=> hp hx.
  exact: (@finite_exterior_homogeneous_above_dimension K h2 W 0
    (fun _ => 0) he p x hp hx).
have hs := @zero_right_grade_tensor_signs_agree K A B hz.
have ha : graded_anticommutative (algebra_grading A) (@graded_mul K A).
  exact: (@alternating_wedge_anticommutative K h2 V K^o
    (fun x y : K^o => x*y) (scalar_bilinear K) (@mulrC K)).
have hb : graded_anticommutative (algebra_grading B) (@graded_mul K B).
  exact: exterior_anticommutative.
move=> m n x y hx hy.
rewrite !ordinary_tensor_graded_product_agreement !hs.
exact: (@signed_tensor_anticommutative K A B ha hb m n x y hx hy).
Qed.

(** Source for [ordinary_tensor_small_factors_commutative]: corrected
    line and zero-space exceptions in Federer 1.4.5, p. 20. If both
    original spaces have dimension at most one, both factor algebras are
    commutative and so is their ordinary tensor product, by 1.2.2(1). *)
Theorem ordinary_tensor_small_factors_commutative n m
    (e : 'I_n -> V) (d : 'I_m -> W) :
    is_basis e -> is_basis d -> (n<=1)%N -> (m<=1)%N ->
    commutative (alg_mul T).
Proof.
move=> he hd hn hm.
apply: algebra_tensor_commutative.
- exact (@small_covector_algebra_commutative K h2 V n e he hn).
- exact (@small_exterior_algebra_commutative K h2 W m d hd hm).
Qed.
End Exceptions.
