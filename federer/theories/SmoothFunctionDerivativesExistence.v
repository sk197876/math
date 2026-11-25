(** Federer (1969), 4.1.1, pp. 343–344: existence of linear
    derivative operators on the smooth-function space. The proof
    reuses the existing exact higher-differential graphs, continuity,
    uniqueness and arithmetic, and never opens their sealed carrier. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP NormClassOneUP NormRegularity
  ContinuousMultilinearUP ContinuousMultilinearSealed NormHigherDifferentialUP
  NormHigherDifferentialUnique NormHigherDifferentialArithmetic
  NormClassHigherDerivative
  SmoothFunctionSpaceUP SmoothFunctionDerivativesUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

Section SmoothDerivativeExistence.
Variable R:realType.
Variables X Y:lmodType R.
Variables (NX:X->R) (NY:Y->R).
Hypothesis hNX:is_real_norm NX.
Hypothesis hNY:is_real_norm NY.
Variable U:set X.
Variable E:lmodType R.
Variable value:E->X->Y.
Hypothesis hE:is_smooth_function_space hNX hNY U value.
Local Notation Z := (fun k=>@ContinuousMultilinear.space R k X Y NX NY hNX hNY).
Local Notation ev := (fun k=>@ContinuousMultilinear.evaluation R k X Y NX NY hNX hNY).
Local Notation ZN := (fun k=>@ContinuousMultilinear.norm R k X Y NX NY hNX hNY).
Local Notation hZ := (fun k=>@ContinuousMultilinear.laws R k X Y NX NY hNX hNY).

(** Source for [smooth_derivative_normalized_field_exists]:
    continuous representatives of each original derivative on U,
    supporting Federer 4.1.1, p. 343. Normalization outside U
    changes no derivative value on its actual domain. *)
Lemma smooth_derivative_normalized_field_exists k f :
  exists G:X->Z k,
    (forall x,U x -> has_norm_higher_differential NX ev ZN U (value f) k x (G x)) /\
    norm_class_zero NX (@ZN k) U G /\ forall x,~U x -> G x=0.
Proof.
have [hc [D [hD hCont]]]:=smooth_function_evaluation_smooth hE f k.
pose G x:=if asbool (U x) then D x else 0.
have hEq x:U x -> G x=D x.
  move=>hx; rewrite /G; case:asboolP=>[h|h] //; exact:False_ind _ (h hx).
have hZero x:~U x -> G x=0.
  move=>hx; rewrite /G; case:asboolP=>[h|h] //; exact:False_ind _ (hx h).
exists G; split.
- by move=>x hx; rewrite (hEq x hx); exact:hD.
- split; last exact hZero.
  exact:(norm_class_zero_domain_agreement (fun x hx=>esym (hEq x hx)) hCont).
Qed.

(** Source for [smooth_derivative_field_witness]: private choice
    of the proved derivative representative, supporting the operators
    in Federer 4.1.1, p. 343. *)
Definition smooth_derivative_field_witness k f : X->Z k :=
  projT1 (cid (smooth_derivative_normalized_field_exists k f)).

(** Source for [smooth_derivative_field_witness_laws]: the private
    representative has its exact derivative, continuity and actual
    domain laws, Federer 4.1.1, p. 343. *)
Lemma smooth_derivative_field_witness_laws k f :
  (forall x,U x -> has_norm_higher_differential NX ev ZN U (value f) k x
    (smooth_derivative_field_witness k f x)) /\
  norm_class_zero NX (@ZN k) U (smooth_derivative_field_witness k f) /\
  forall x,~U x -> smooth_derivative_field_witness k f x=0.
Proof. exact:(projT2 (cid (smooth_derivative_normalized_field_exists k f))). Qed.

(** Source for [smooth_derivative_field_witness_linear]:
    differentiation is linear in the smooth function, supporting
    the seminorms in Federer 4.1.1, p. 343. This follows from the
    existing higher-differential arithmetic and uniqueness. *)
Lemma smooth_derivative_field_witness_linear k x :
  linear (fun f=>smooth_derivative_field_witness k f x).
Proof.
move=>c f g; case:(pselect (U x))=>[hx|hx].
- have hF:=@norm_higher_differential_field_scale R X Y NX NY hNX hNY
    Z ev ZN hZ U k (value f) (smooth_derivative_field_witness k f) c
    (smooth_derivative_field_witness_laws k f).1.
  have hSum:=@norm_higher_differential_field_add R X Y NX NY hNX hNY
    Z ev ZN hZ U k (fun y=>c*:value f y) (value g)
    (fun y=>c*:smooth_derivative_field_witness k f y)
    (smooth_derivative_field_witness k g) hF
    (smooth_derivative_field_witness_laws k g).1 x hx.
  have hValue:value (c*:f+g)=(fun y=>c*:value f y+value g y).
    apply:funext=>y.
    change (value (c*:f+g) y=c*:value f y+value g y).
    exact:(@smooth_function_evaluation_linear R X Y NX NY hNX hNY U E value hE c f g y).
  rewrite -hValue in hSum.
  exact:(norm_higher_differential_unique hNX hNY hZ
    ((smooth_derivative_field_witness_laws k (c*:f+g)).1 x hx) hSum).
- by rewrite !((smooth_derivative_field_witness_laws k _).2.2 x hx) scaler0 addr0.
Qed.

(** Source for [smooth_function_derivatives_exist]: proved
    existence of all linear derivative operators, with continuous
    exact fields on U, Federer 4.1.1, pp. 343–344. *)
Theorem smooth_function_derivatives_exist :
  exists D,@is_smooth_function_derivatives R X Y NX NY hNX hNY U E value D.
Proof.
pose D k x:=@HomMap R E (Z k) (fun f=>smooth_derivative_field_witness k f x)
  (introT (asboolP _) (smooth_derivative_field_witness_linear k x)).
exists D; constructor.
- move=>k f x hx; exact:((smooth_derivative_field_witness_laws k f).1 x hx).
- move=>k f; exact:(smooth_derivative_field_witness_laws k f).2.1.
- move=>k f x hx; exact:((smooth_derivative_field_witness_laws k f).2.2 x hx).
Qed.
End SmoothDerivativeExistence.
