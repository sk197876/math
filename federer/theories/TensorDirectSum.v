(** Federer 1.1.2, p. 10: tensoring the maps of a direct-sum splitting
    preserves all three displayed splitting identities, in arbitrary
    dimension. The maps and the original splitting are specified by laws. *)
From mathcomp Require Import all_boot all_order all_algebra.
From Federer Require Import TensorUP TensorProduct TensorMaps TensorSpan TensorMapIsomorphism.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

Section DirectSum.
Variable K : fieldType.
Variables V P Q W : lmodType K.
Variables (f : {linear V -> P}) (phi : {linear P -> V})
          (g : {linear V -> Q}) (psi : {linear Q -> V}).
Hypotheses (hf : cancel phi f) (hg : cancel psi g)
  (hdecomp : forall v, phi (f v) + psi (g v) = v).

(** Source for [tensor_direct_sum_left_cancel]: Federer 1.1.2, p. 10,
    (f tensor identity) composed with (phi tensor identity) is identity. *)
Lemma tensor_direct_sum_left_cancel :
  cancel (tensor_map phi (linear_id W)) (tensor_map f (linear_id W)).
Proof. apply: tensor_map_cancel; [exact: hf | by []]. Qed.

(** Source for [tensor_direct_sum_right_cancel]: Federer 1.1.2, p. 10,
    (g tensor identity) composed with (psi tensor identity) is identity. *)
Lemma tensor_direct_sum_right_cancel :
  cancel (tensor_map psi (linear_id W)) (tensor_map g (linear_id W)).
Proof. apply: tensor_map_cancel; [exact: hg | by []]. Qed.

(** Source for [tensor_direct_sum_decomposition]: Federer 1.1.2, p. 10,
    the sum of the two injection-projection composites is identity on
    V tensor W. No finite-dimensional hypothesis is needed. *)
Theorem tensor_direct_sum_decomposition (t : tensor_space V W) :
  tensor_map phi (linear_id W) (tensor_map f (linear_id W) t) +
  tensor_map psi (linear_id W) (tensor_map g (linear_id W) t) = t.
Proof.
elim/tensor_induction: t=> [|x y hx hy|a x hx|v w].
- by rewrite !linear0 addr0.
- by rewrite !linearD /= addrACA hx hy.
- by rewrite !linearZ /= -scalerDr hx.
- by rewrite !tensor_mapE /= -tensor_inj_addl hdecomp.
Qed.

(** Source for [direct_sum_cross_left]: Federer 1.1.2, p. 10;
    the three printed splitting laws imply the first mixed composite zero.
    Supporting deduction for the direct-sum isomorphism. *)
Lemma direct_sum_cross_left q : f (psi q) = 0.
Proof.
have h := hdecomp (psi q); rewrite hg in h.
have hz : phi (f (psi q)) = 0.
  have hh := congr1 (fun v : V => v - psi q) h.
  by rewrite addrK subrr in hh.
by rewrite -(hf (f (psi q))) hz linear0.
Qed.

(** Source for [direct_sum_cross_right]: Federer 1.1.2, p. 10;
    the second mixed composite is zero. Supporting deduction. *)
Lemma direct_sum_cross_right p : g (phi p) = 0.
Proof.
have h := hdecomp (phi p); rewrite hf in h.
have hz : psi (g (phi p)) = 0.
  have hh := congr1 (fun v : V => v - phi p) h.
  by rewrite [phi p + _]addrC addrK subrr in hh.
by rewrite -(hg (g (phi p))) hz linear0.
Qed.

(** Source for [tensor_direct_sum_cross_left]: Federer 1.1.2, p. 10;
    the mixed tensor composite vanishes, certifying directness. *)
Lemma tensor_direct_sum_cross_left (t : tensor_space Q W) :
  tensor_map f (linear_id W) (tensor_map psi (linear_id W) t) = 0.
Proof.
elim/tensor_induction: t=> [|x y hx hy|a x hx|q w].
- by rewrite !linear0.
- by rewrite !linearD /= hx hy addr0.
- by rewrite !linearZ /= hx scaler0.
- by rewrite !tensor_mapE /= direct_sum_cross_left tensor_inj0l.
Qed.

(** Source for [tensor_direct_sum_cross_right]: Federer 1.1.2, p. 10;
    the other mixed tensor composite vanishes. *)
Lemma tensor_direct_sum_cross_right (t : tensor_space P W) :
  tensor_map g (linear_id W) (tensor_map phi (linear_id W) t) = 0.
Proof.
elim/tensor_induction: t=> [|x y hx hy|a x hx|p w].
- by rewrite !linear0.
- by rewrite !linearD /= hx hy addr0.
- by rewrite !linearZ /= hx scaler0.
- by rewrite !tensor_mapE /= direct_sum_cross_right tensor_inj0l.
Qed.

(** Source for [tensor_direct_sum_projection_linear]: Federer 1.1.2,
    p. 10; the two tensor projections form a linear map into the direct sum. *)
Lemma tensor_direct_sum_projection_linear : linear
  (fun t : tensor_space V W =>
    (tensor_map f (linear_id W) t, tensor_map g (linear_id W) t)).
Proof. by move=> a x y; rewrite !linearP. Qed.

(** Source for [tensor_direct_sum_bijection]: Federer 1.1.2, p. 10,
    V tensor W is isomorphic to (P tensor W) direct sum (Q tensor W).
    The displayed map consists of the two original tensor projections. *)
Theorem tensor_direct_sum_bijection : bijective
  (fun t : tensor_space V W =>
    (tensor_map f (linear_id W) t, tensor_map g (linear_id W) t)).
Proof.
exists (fun t => tensor_map phi (linear_id W) t.1 +
                 tensor_map psi (linear_id W) t.2).
- exact: tensor_direct_sum_decomposition.
- move=> [x y] /=.
  by rewrite !linearD /= tensor_direct_sum_left_cancel
    tensor_direct_sum_right_cancel tensor_direct_sum_cross_left
    tensor_direct_sum_cross_right addr0 add0r.
Qed.
End DirectSum.
