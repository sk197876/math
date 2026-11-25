(** Federer (1969), 3.1.18, p. 230: vanishing derivatives along the
    convex W fibres imply f composed with g inverse=psi composed with r.
    This supporting theorem is intrinsic to arbitrary normed spaces. *)
From mathcomp Require Import all_boot all_order all_algebra classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormDifferentialLinear
  NormDifferentialArithmetic NormDifferentialChain NormDifferentialLocal
  InnerConvex NormDifferentialConvexBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.

(** Source for [norm_differential_affine_left]: supporting the affine
    fibre parametrisation (v,w) at fixed v in Federer 3.1.18, p. 230.
    Translation does not change the bounded linear differential. *)
Lemma norm_differential_affine_left (R:realType) (W X:lmodType R)
    (NW:W->R) (NX:X->R) (hNW:is_real_norm NW) (hNX:is_real_norm NX)
    (A:W->Prop) (J:Hom W X) c a :
  norm_domain_interior NW A a -> norm_bounded_linear NW NX J ->
  has_norm_differential NW NX A (fun w=>c+J w) a J.
Proof.
move=>hA hJ.
have hc:=@norm_differential_constant R W X NW NX hNW hNX A a c hA.
have hL:=@norm_differential_linear R W X NW NX hNW hNX A a J hA hJ.
have hh:=norm_differential_add hNX hc hL.
by rewrite add0r in hh.
Qed.

(** Source for [norm_affine_fibre_constant]: constancy along each
    convex fibre from its zero derivative, the middle argument of
    Federer 3.1.18, p. 230. Openness is required only of the actual
    fibre domain; completeness and finite dimension are unnecessary. *)
Theorem norm_affine_fibre_constant (R:realType) (W X Y:lmodType R)
    (NW:W->R) (NX:X->R) (NY:Y->R)
    (hNW:is_real_norm NW) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (U:W->Prop) (A:X->Prop) (J:Hom W X) c (F:X->Y) (D:X->Hom X Y) :
  is_inner_convex U ->
  (forall w, U w -> norm_domain_interior NW U w) ->
  norm_bounded_linear NW NX J ->
  (forall w, U w -> A (c+J w)) ->
  (forall x, A x -> has_norm_differential NX NY A F x (D x)) ->
  (forall w, U w -> forall z, D (c+J w) (J z)=0) ->
  forall w z, U w -> U z -> F (c+J w)=F (c+J z).
Proof.
move=>hU hopen hJ hmap hD hzero.
pose f:=fun w=>F (c+J w).
have hfield w (hw:U w) : exists L:Hom W Y,
    has_norm_differential NW NY U f w L /\ forall z, NY (L z)<=0*NW z.
  exists (hom_comp (D (c+J w)) J); split.
  - have haff:=@norm_differential_affine_left R W X NW NX hNW hNX U J c w
      (hopen w hw) hJ.
    have hchain:=@norm_differential_chain R W X Y NW NX NY hNW hNX hNY U A
      (fun z=>c+J z) F w J (D (c+J w)) haff (hD _ (hmap w hw)).
    exact (@norm_differential_restrict R W Y NW NY (fun z=>U z /\ A (c+J z))
      U f w (hom_comp (D (c+J w)) J) (fun z hz=>conj hz (hmap z hz))
      (hopen w hw) hchain).
  - move=>z; rewrite hom_compE (hzero w hw z) (real_seminorm_zero hNY.1) mul0r.
    exact: lexx.
have hb:=@norm_differential_convex_bound R W Y NW NY hNW hNY U U f 0 hU (lexx 0) hfield.
move=>w z hw hz.
have hh:=hb w z hw hz; rewrite mul0r in hh.
have he:NY (f w-f z)=0.
  by apply/eqP; rewrite eq_le hh (real_seminorm_nonnegative hNY.1) andbT.
apply/eqP; rewrite -subr_eq0; apply/eqP; exact: hNY.2 he.
Qed.
