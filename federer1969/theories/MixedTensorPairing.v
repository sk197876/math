(** Federer (1969), 1.10.2, p. 45: arbitrary bilinear coefficient pairings
    W1 x W2 -> W3. The construction uses the project's abstract binary
    tensor universal property. *)
From mathcomp Require Import all_boot all_order ssralg.
From Federer Require Import Tensor Bilinear Hom.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section CoefficientProduct.
Variable K : fieldType.
Variables X Y W1 W2 W3 : lmodType K.
Variable mu : W1 -> W2 -> W3.
Hypothesis hmu : bilinear mu.
(** Source for [mixed_nu]: Federer 1.10.2, p. 45,
    final paragraph allowing an arbitrary bilinear coefficient map.
    Supporting definition or lemma, in words: The bilinear coefficient map W1 x W2 -> W3 induces a linear map on W1 tensor W2. *)
Definition mixed_nu : {linear tensor_space W1 W2 -> W3} := tensor_lift hmu.
(** Source for [mixed_nuE]: Federer 1.10.2, p. 45,
    final paragraph allowing an arbitrary bilinear coefficient map.
    Supporting definition or lemma, in words: The induced coefficient map evaluates on pure tensors as the prescribed bilinear map. *)
Lemma mixed_nuE s t : mixed_nu (tensor_inj s t) = mu s t.
Proof. exact: tensor_liftE. Qed.

(** Source for [mixed_paired_tensor_bilinear]: Federer 1.10.2, p. 45,
    final paragraph allowing an arbitrary bilinear coefficient map.
    Supporting definition or lemma, in words: Supporting bilinearity after composing each input with its linear map. *)
Lemma mixed_paired_tensor_bilinear (a : Hom X W1) (b : Hom Y W2) :
  bilinear (fun x y => mu (a x) (b y)).
Proof.
split.
- by move=> y c x x'; rewrite (hom_linear a) (proj1 hmu).
- by move=> x c y y'; rewrite (hom_linear b) (proj2 hmu).
Qed.
(** Source for [mixed_paired_tensor]: Federer 1.10.2, p. 45,
    final paragraph allowing an arbitrary bilinear coefficient map.
    Supporting definition or lemma, in words: Pair the two linear maps through the arbitrary bilinear coefficient map. *)
Definition mixed_paired_tensor (a : Hom X W1) (b : Hom Y W2) : {linear tensor_space X Y -> W3} :=
  tensor_lift (mixed_paired_tensor_bilinear a b).
(** Source for [mixed_paired_tensorE]: Federer 1.10.2, p. 45,
    final paragraph allowing an arbitrary bilinear coefficient map.
    Supporting definition or lemma, in words: On a pure tensor, apply each linear map and then the coefficient pairing. *)
Lemma mixed_paired_tensorE a b x y : mixed_paired_tensor a b (tensor_inj x y) = mu (a x) (b y).
Proof. exact: tensor_liftE. Qed.
(** Source for [mixed_paired_tensor_factorisation]: Federer 1.10.2, p. 45,
    final paragraph allowing an arbitrary bilinear coefficient map.
    Supporting definition or lemma, in words: The pairing factors through the tensor product of the two linear maps. *)
Lemma mixed_paired_tensor_factorisation a b x :
  mixed_paired_tensor a b x = mixed_nu (tensor_map (hom_as_linear a) (hom_as_linear b) x).
Proof.
apply: (tensor_ext (tensor_exists X Y) (mixed_paired_tensor a b)
  (linear_comp mixed_nu (tensor_map (hom_as_linear a) (hom_as_linear b)))) x => u v.
by rewrite mixed_paired_tensorE /linear_comp /= tensor_mapE mixed_nuE.
Qed.
(** Source for [mixed_paired_tensor_parameter_bilinear]: Federer 1.10.2, p. 45,
    final paragraph allowing an arbitrary bilinear coefficient map.
    Supporting definition or lemma, in words: The resulting tensor evaluation depends bilinearly on the two linear maps. *)
Lemma mixed_paired_tensor_parameter_bilinear x :
  bilinear (fun (a : Hom X W1) (b : Hom Y W2) => mixed_paired_tensor a b x).
Proof.
elim/tensor_induction: x => [|x y [hxl hxr] [hyl hyr]|c x [hxl hxr]|u v]; split.
- by move=> b c a a'; rewrite !linear0 add0r.
- by move=> a c b b'; rewrite !linear0 add0r.
- move=> b c a a'.
  rewrite (linD (linearP (mixed_paired_tensor (c *: a + a') b)) x y)
    (linD (linearP (mixed_paired_tensor a b)) x y)
    (linD (linearP (mixed_paired_tensor a' b)) x y).
  change (mixed_paired_tensor (c *: a + a') b x + mixed_paired_tensor (c *: a + a') b y =
    c *: (mixed_paired_tensor a b x + mixed_paired_tensor a b y) +
    (mixed_paired_tensor a' b x + mixed_paired_tensor a' b y)).
  by rewrite hxl hyl scalerDr addrACA.
- move=> a c b b'.
  rewrite (linD (linearP (mixed_paired_tensor a (c *: b + b'))) x y)
    (linD (linearP (mixed_paired_tensor a b)) x y)
    (linD (linearP (mixed_paired_tensor a b')) x y).
  change (mixed_paired_tensor a (c *: b + b') x + mixed_paired_tensor a (c *: b + b') y =
    c *: (mixed_paired_tensor a b x + mixed_paired_tensor a b y) +
    (mixed_paired_tensor a b' x + mixed_paired_tensor a b' y)).
  by rewrite hxr hyr scalerDr addrACA.
- move=> b d a a'.
  rewrite (linZ (linearP (mixed_paired_tensor (d *: a + a') b)) c x)
    (linZ (linearP (mixed_paired_tensor a b)) c x)
    (linZ (linearP (mixed_paired_tensor a' b)) c x).
  by rewrite hxl scalerDr !scalerA [c * d]mulrC.
- move=> a d b b'.
  rewrite (linZ (linearP (mixed_paired_tensor a (d *: b + b'))) c x)
    (linZ (linearP (mixed_paired_tensor a b)) c x)
    (linZ (linearP (mixed_paired_tensor a b')) c x).
  by rewrite hxr scalerDr !scalerA [c * d]mulrC.
- by move=> b c a a'; rewrite !mixed_paired_tensorE hom_addE hom_scaleE (proj1 hmu).
- by move=> a c b b'; rewrite !mixed_paired_tensorE hom_addE hom_scaleE (proj2 hmu).
Qed.
End CoefficientProduct.
