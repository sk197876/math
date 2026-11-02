(** Federer (1969), 1.10.2, p. 45: degree addition for an arbitrary bilinear
    coefficient pairing. The grading argument is stated abstractly for use
    with the symmetric diagonal. *)
From mathcomp Require Import all_boot all_order ssralg.
From mathcomp.classical Require Import boolp.
From Federer Require Import Graded Bilinear Hom HomogeneousHom MixedTensorPairing.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Homogeneous.
Variable K : fieldType.
Variables X W1 W2 W3 : lmodType K.
Variable G : grading X.
Variable mu : W1 -> W2 -> W3.
Hypothesis hmu : bilinear mu.
Variable D : {linear X -> tensor_space X X}.
Hypothesis hD : preserves_grading G (tensor_grading_product G G) D.

(** Source for [mixed_paired_tensor_degree]: Federer 1.10.2,
    p. 45, final displayed bilinear map. Supporting degree calculation:
    pairing a p-map with a q-map vanishes in all degrees except p+q. *)
Lemma mixed_paired_tensor_degree p q (a : Hom_m W1 G p) (b : Hom_m W2 G q) n x :
  n != (p+q)%N -> homogeneous (tensor_grading_product G G) n x ->
  mixed_paired_tensor hmu a b x = 0.
Proof.
move=> hn; move: x; apply: tensor_component_induction =>
  [|x y hx hy|c x hx|r s x y hrs hx hy].
- exact: linear0.
- by rewrite linearD hx hy add0r.
- rewrite linearZ; change (c *: mixed_paired_tensor hmu a b x = 0).
  by rewrite hx scaler0.
- rewrite mixed_paired_tensorE; case hr: (r == p).
  + have hs : s != q.
      apply/eqP=> hs; move/eqP: hr=> hr.
      by move: hn; rewrite -hrs hr hs eqxx.
    rewrite (hom_m_degree b hs hy); exact: bil0r.
  + rewrite (hom_m_degree a (negbT hr) hx); exact: bil0l.
Qed.

(** Source for [mixed_convolution]: Federer 1.10.2, p. 45,
    final paragraph. Compose the diagonal with the paired linear maps
    and the arbitrary coefficient pairing. *)
Definition mixed_convolution (a : Hom X W1) (b : Hom X W2) : Hom X W3 :=
  hom_of_linear (linear_comp (mixed_paired_tensor hmu a b) D).

(** Source for [mixed_convolutionE]: Federer 1.10.2, p. 45,
    supporting evaluation formula for this composite. *)
Lemma mixed_convolutionE a b x :
  mixed_convolution a b x = mixed_paired_tensor hmu a b (D x).
Proof. by []. Qed.

(** Source for [mixed_convolution_degree]: Federer 1.10.2,
    p. 45, the displayed target has degree p+q. *)
Lemma mixed_convolution_degree p q (a : Hom_m W1 G p) (b : Hom_m W2 G q) :
  hom_degree G (p+q) (mixed_convolution a b).
Proof. move=> n x hn hx; apply: mixed_paired_tensor_degree hn (hD hx). Qed.

(** Source for [mixed_homogeneous_convolution]: Federer 1.10.2,
    p. 45, package the composite as a homogeneous map of degree p+q. *)
Definition mixed_homogeneous_convolution p q (a : Hom_m W1 G p) (b : Hom_m W2 G q) :
    Hom_m W3 G (p+q) :=
  @HomogeneousHom K X W3 G (p+q) (mixed_convolution a b)
    (introT (asboolP _) (mixed_convolution_degree a b)).

(** Source for [mixed_homogeneous_convolutionE]: Federer 1.10.2,
    p. 45, the packaged homogeneous map evaluates as the same composite. *)
Lemma mixed_homogeneous_convolutionE p q (a : Hom_m W1 G p) (b : Hom_m W2 G q) x :
  mixed_homogeneous_convolution a b x = mixed_paired_tensor hmu a b (D x).
Proof. by []. Qed.
End Homogeneous.
