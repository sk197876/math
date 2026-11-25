(** Federer (1969), 3.4.6, p. 324: finite scalar
    operations preserve the original transverse polynomial degrees,
    by the symmetric-form laws of 1.10.4, p. 46. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import TensorUP Bilinear Hom SymmetricForms HomogeneousPolynomialFunctions
  SymmetricFormProduct SymmetricPolynomialProduct.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section Arithmetic.
Variable R:realType.
Variable K:lmodType R.

(** Source for [weierstrass_homogeneous_zero]: the zero
    coefficient has every original homogeneous degree,
    supporting 3.4.6, p. 324. *)
Lemma weierstrass_homogeneous_zero j:
  @is_homogeneous_polynomial R K R^o j (fun _=>0).
Proof.
exists (0:S_m K R^o j)=>z.
have hh:=congr1 (fun f:K->R^o=>f z) (linear0 (@sform_polynomial_value R K R^o j)).
exact:esym hh.
Qed.

(** Source for [weierstrass_homogeneous_add]: addition
    preserves the original transverse degree, supporting the
    finite recursion in 3.4.6, p. 324. *)
Lemma weierstrass_homogeneous_add j (P Q:K->R):
  @is_homogeneous_polynomial R K R^o j P ->
  @is_homogeneous_polynomial R K R^o j Q ->
  @is_homogeneous_polynomial R K R^o j (fun z=>P z+Q z).
Proof.
move=>[F hF] [G hG];exists (F+G)=>z.
have hh:=congr1 (fun f:K->R^o=>f z) (linearD (@sform_polynomial_value R K R^o j) F G).
change (sform_polynomial_value (F+G) z=sform_polynomial_value F z+sform_polynomial_value G z) in hh.
by rewrite hh hF hG.
Qed.

(** Source for [weierstrass_homogeneous_negate]: negation
    preserves the original transverse degree, supporting the
    subtractions in 3.4.6, p. 324. *)
Lemma weierstrass_homogeneous_negate j (P:K->R):
  @is_homogeneous_polynomial R K R^o j P ->
  @is_homogeneous_polynomial R K R^o j (fun z=>-P z).
Proof.
move=>[F hF];exists (-F)=>z.
have hh:=congr1 (fun f:K->R^o=>f z) (linearD (@sform_polynomial_value R K R^o j) F (-F)).
change (sform_polynomial_value (F+ -F) z=sform_polynomial_value F z+sform_polynomial_value (-F) z) in hh.
have hZero:=congr1 (fun f:K->R^o=>f z) (linear0 (@sform_polynomial_value R K R^o j)).
rewrite addrN hZero in hh.
apply:(addrI (sform_polynomial_value F z)).
by rewrite hF addrN -hh.
Qed.

(** Source for [weierstrass_homogeneous_sum]: an actual
    finite sum of degree-j coefficient functions remains
    degree j, supporting 3.4.6, p. 324. *)
Lemma weierstrass_homogeneous_sum j (I:finType) (P:I->K->R):
  (forall t,@is_homogeneous_polynomial R K R^o j (P t)) ->
  @is_homogeneous_polynomial R K R^o j (fun z=>\sum_t P t z).
Proof.
move=>hP.
have hFinite:forall s:seq I,@is_homogeneous_polynomial R K R^o j
    (fun z=>\sum_(t<-s) P t z).
  elim=>[|t s ih].
    have hEmpty:(fun z=>\sum_(t<-[::]) P t z)=(fun _=>0).
      by apply:funext=>z;rewrite big_nil.
    rewrite hEmpty;exact:weierstrass_homogeneous_zero.
  have hFunction:(fun z=>\sum_(u<-t::s) P u z)=
      (fun z=>P t z+\sum_(u<-s) P u z).
    by apply:funext=>z;rewrite big_cons.
  rewrite hFunction;exact:weierstrass_homogeneous_add (hP t) ih.
have hEnum:(fun z=>\sum_t P t z)=(fun z=>\sum_(t<-enum I) P t z).
  by apply:funext=>z;rewrite -big_enum.
rewrite hEnum;exact:(hFinite (enum I)).
Qed.

(** Source for [weierstrass_homogeneous_multiply]: pointwise
    multiplication adds the original transverse degrees,
    supporting both convolution sums in 3.4.6, p. 324.
    The product is represented by the proved symmetric product. *)
Lemma weierstrass_homogeneous_multiply p q (P Q:K->R):
  @is_homogeneous_polynomial R K R^o p P ->
  @is_homogeneous_polynomial R K R^o q Q ->
  @is_homogeneous_polynomial R K R^o (p+q)%N (fun z=>P z*Q z).
Proof.
move=>[F hF] [G hG].
have hMul:bilinear (fun a b:R^o=>a*b).
  split.
  - move=>y a x z;change ((a*x+z)*y=a*(x*y)+z*y);by rewrite mulrDl mulrA.
  - move=>x a y z;change (x*(a*y+z)=a*(x*y)+x*z);by rewrite mulrDr mulrCA.
exists (sform_product hMul F G)=>z.
rewrite (@homogeneous_polynomial_product R (@pchar_num R) K R^o (fun a b:R^o=>a*b) hMul p q F G z).
by rewrite hF hG.
Qed.
End Arithmetic.
