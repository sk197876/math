(** Federer (1969), 2.6.4, p. 118: the separated-variable tensor map is a
    monomorphism. This supporting algebraic proof works for arbitrary
    injective linear representations as functions. It uses the project's
    finite tensor separation argument and formal finite linear combinations
    of evaluation points; no dimensional hypothesis is added. *)
From HB Require Import structures.
From mathcomp Require Import all_boot all_order all_algebra boolp functions.
From Federer Require Import FreeVector Hom TensorUP TensorProduct TensorSpan
  TensorEvaluation FunctionProductBilinear.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section Separation.
Variable K : fieldType.
Variables X Y : choiceType.
Variables U V : lmodType K.
Variables (u : {linear U -> (X -> K^o)}) (v : {linear V -> (Y -> K^o)}).

(** Source for [function_finite_evaluation]: supporting linear
    extension of point evaluation for the monomorphism in Federer
    2.6.4, p. 118. The auxiliary free space consists of
    formal finite combinations of evaluation points. *)
Definition function_finite_evaluation (f : V) : Hom (@free_vector K Y) K^o :=
  hom_of_linear (GRing.Linear.clone _ _ _ _ (free_extend (v f)) _).

(** Source for [function_finite_evaluation_linear]: supporting
    linearity in the represented function for Federer 2.6.4,
    p. 118. Equality is checked on the free generators. *)
Lemma function_finite_evaluation_linear : linear function_finite_evaluation.
Proof.
move=> c f g; apply: hom_ext.
apply: (free_linear_ext (hom_as_linear (function_finite_evaluation (c *: f+g)))
  (hom_as_linear (c *: function_finite_evaluation f+function_finite_evaluation g)))=> y.
rewrite !hom_as_linearE hom_addE hom_scaleE /function_finite_evaluation !hom_of_linearE /= !free_extend_delta.
by rewrite linearP.
Qed.
HB.instance Definition _ := GRing.isLinear.Build K V (Hom (@free_vector K Y) K^o)
  *:%R function_finite_evaluation function_finite_evaluation_linear.

(** Source for [function_finite_evaluation_injective]: supporting
    separation by points for Federer 2.6.4, p. 118.
    Injectivity of the original function representation suffices. *)
Lemma function_finite_evaluation_injective : injective v -> injective function_finite_evaluation.
Proof.
move=> hv f g he; apply: hv; apply: funext=> y.
have hh := congr1 (fun F : Hom (@free_vector K Y) K^o => F (@delta K Y y)) he.
by rewrite /function_finite_evaluation !hom_of_linearE /= !free_extend_delta in hh.
Qed.
Local Notation F := (GRing.Linear.clone _ _ _ _ function_finite_evaluation _).

(** Source for [function_tensor_point_evaluation]: supporting
    tensor contraction against a formal finite combination of points
    for the monomorphism in Federer 2.6.4, p. 118. *)
Definition function_tensor_point_evaluation (t : tensor_space U V) (h : @free_vector K Y) :=
  @tensor_evaluation K (@free_vector K Y) U V F h t.

(** Source for [function_tensor_evaluation_linear]: supporting
    linear dependence on a finite combination of points for the
    monomorphism in Federer 2.6.4, p. 118. *)
Lemma function_tensor_evaluation_linear (t : tensor_space U V) :
  linear (function_tensor_point_evaluation t).
Proof.
rewrite /function_tensor_point_evaluation; move=> c h k; elim/tensor_induction: t=> [|t s ht hs|a t ht|f g].
- by rewrite !linear0 addr0.
- rewrite !linearD /= ht hs; by rewrite addrACA.
- rewrite !linearZ /= ht scalerDr; congr (_+_); by rewrite !scalerA mulrC.
- rewrite !tensor_evaluationE hom_linear scalerDl scalerA; by [].
Qed.

HB.instance Definition _ t := GRing.isLinear.Build K (@free_vector K Y) U
  *:%R (function_tensor_point_evaluation t) (function_tensor_evaluation_linear t).

(** Source for [function_tensor_evaluation_point]: supporting
    point evaluation of the separated-variable tensor map in Federer
    2.6.4, p. 118. The identity extends from pure tensors
    by the already proved tensor spanning principle. *)
Lemma function_tensor_evaluation_point (t : tensor_space U V) x y :
  u (@tensor_evaluation K (@free_vector K Y) U V F (@delta K Y y) t) x =
  function_tensor_map u v t (x,y).
Proof.
elim/tensor_induction: t=> [|t s ht hs|a t ht|f g].
- by rewrite !linear0.
- by rewrite !linearD ?fctE /= ht hs.
- rewrite !linearZ /= !scalrfctE /=.
  change (a * u (@tensor_evaluation K (@free_vector K Y) U V F (@delta K Y y) t) x =
    a * function_tensor_map u v t (x,y)).
  by rewrite ht.
- rewrite tensor_evaluationE function_tensor_map_generator linearZ ?fctE /=.
  rewrite /function_finite_evaluation /= ?hom_of_linearE /= free_extend_delta.
  exact: mulrC.
Qed.

(** Source for [function_tensor_map_injective]: the algebraic
    monomorphism assertion in Federer 2.6.4, p. 118,
    for any two injective function representations. No measure or
    almost-everywhere equivalence is used in this supporting theorem. *)
Theorem function_tensor_map_injective :
  injective u -> injective v -> injective (function_tensor_map u v).
Proof.
move=> hu hv.
have hzero (t : tensor_space U V) : function_tensor_map u v t=0 -> t=0.
  move=> ht; apply: (tensor_evaluation_separates (function_finite_evaluation_injective hv)).
  pose e := GRing.Linear.clone _ _ _ _ (function_tensor_point_evaluation t) _.
  apply: (free_linear_ext e (hom_as_linear (0 : Hom (@free_vector K Y) U)))=> y.
  apply: hu; apply: funext=> x; rewrite linear0 /=.
  by rewrite /e /function_tensor_point_evaluation /= function_tensor_evaluation_point ht.
move=> t s he; apply/eqP; rewrite -subr_eq0; apply/eqP; apply: hzero.
by rewrite linearB /= he subrr.
Qed.
End Separation.
