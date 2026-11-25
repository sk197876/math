(** Federer (1969), 4.1.6, pp. 354–355:
    degree zero, addition, alternating multiplication
    and contravariant composition of the original
    pullback. Every analytic statement uses actual
    norm differentials on the original domains. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions reals.
From Federer Require Import Hom TensorUP Bilinear RealNormUP NormDifferentialUP
  NormDifferentialDirectional NormDifferentialChain NormDifferentialLocal
  Alternating AlternatingProduct FormPullbackProduct DifferentialFormPullbackUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [original_linear_pullback_composition]:
    the original contravariant exterior maps compose
    in reverse order, supporting the last equation
    of Federer 4.1.6, p. 355. *)
Lemma original_linear_pullback_composition (K:fieldType) (X Y Z W:lmodType K)
    (f:Hom X Y) (g:Hom Y Z) m (phi:A_m Z W m):
  A_m_dual (hom_as_linear (hom_comp g f)) phi=
    A_m_dual (hom_as_linear f) (A_m_dual (hom_as_linear g) phi).
Proof.
apply:form_ext=>t; rewrite !A_m_dualE.
congr (phi _); apply:val_inj.
change (map ((fun y:Y=>g y) \o (fun x:X=>f x)) t=map g (map f t)).
exact:map_comp.
Qed.

(** Source for [differential_form_pullback_degree_zero]:
    f# phi=phi composed with f in degree zero,
    Federer 4.1.6, p. 354, under the
    actual earlier A^0=W identification. *)
Theorem differential_form_pullback_degree_zero (R:realType) (X Y W:lmodType R)
    (NX:X->R) (NY:Y->R) (A:X->Prop) (B:Y->Prop) (f:X->Y)
    (phi:Y->W) a (L:Hom X Y):
  B (f a)->has_norm_differential NX NY A f a L->
  has_differential_form_pullback NX NY A B f (fun y=>@zero_form R Y W (phi y)) a
    (@zero_form R X W (phi (f a))).
Proof.
move=>hB hL; split=>//; exists L; split=>//.
apply:form_ext=>t; by rewrite A_m_dualE !zero_formE.
Qed.

(** Source for [differential_form_pullback_add]: the
    original f# commutes with addition,
    Federer 4.1.6, p. 354. *)
Theorem differential_form_pullback_add (R:realType) (X Y W:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (A:X->Prop) (B:Y->Prop) (f:X->Y) m (phi psi:Y->A_m Y W m) a b c:
  has_differential_form_pullback NX NY A B f phi a b->
  has_differential_form_pullback NX NY A B f psi a c->
  has_differential_form_pullback NX NY A B f (fun y=>phi y+psi y) a (b+c).
Proof.
move=>[hB [L [hL ->]]] [_ [M [hM ->]]].
have hEqual:=norm_differential_unique hNX hNY hM hL.
rewrite hEqual; split=>//; exists L; split=>//.
exact:esym (linearD _ _ _).
Qed.

(** Source for [differential_form_pullback_product]: the
    original f# commutes with alternating multiplication,
    Federer 4.1.6, p. 354, for every
    coefficient multiplication present in the book. *)
Theorem differential_form_pullback_product (R:realType) (h2:(1+1:R)!=0)
    (X Y W:lmodType R) (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (mu:W->W->W) (hmu:bilinear mu) (A:X->Prop) (B:Y->Prop) (f:X->Y) p q
    (phi:Y->A_m Y W p) (psi:Y->A_m Y W q) a b c:
  has_differential_form_pullback NX NY A B f phi a b->
  has_differential_form_pullback NX NY A B f psi a c->
  has_differential_form_pullback NX NY A B f (fun y=>form_wedge h2 hmu (phi y) (psi y)) a
    (form_wedge h2 hmu b c).
Proof.
move=>[hB [L [hL ->]]] [_ [M [hM ->]]].
have hEqual:=norm_differential_unique hNX hNY hM hL.
rewrite hEqual; split=>//; exists L; split=>//.
exact:(esym (@form_pullback_product R h2 X Y W (hom_as_linear L) mu hmu p q (phi (f a)) (psi (f a)))).
Qed.

(** Source for [differential_form_pullback_composition]:
    (g composed with f)# phi=f#(g# phi),
    Federer 4.1.6, p. 355. The actual
    pointwise chain rule already proves this for
    differentiable maps, hence in the stated smooth case. *)
Theorem differential_form_pullback_composition (R:realType) (X Y Z W:lmodType R)
    (NX:X->R) (NY:Y->R) (NZ:Z->R)
    (hNX:is_real_norm NX) (hNY:is_real_norm NY) (hNZ:is_real_norm NZ)
    (A:X->Prop) (B:Y->Prop) (C:Z->Prop) (f:X->Y) (g:Y->Z)
    m (phi:Z->A_m Z W m) a (L:Hom X Y) (M:Hom Y Z):
  (forall x,A x->B (f x))->C (g (f a))->
  has_norm_differential NX NY A f a L->has_norm_differential NY NZ B g (f a) M->
  has_differential_form_pullback NX NZ A C (fun x=>g (f x)) phi a
    (A_m_dual (hom_as_linear L) (A_m_dual (hom_as_linear M) (phi (g (f a))))).
Proof.
move=>hImage hC hL hM; split=>//; exists (hom_comp M L); split.
- have hChain:=norm_differential_chain hNX hNY hNZ hL hM.
  exact:(norm_differential_restrict (fun x hx=>conj hx (hImage x hx))
    (norm_differential_interior hL) hChain).
- exact:esym (original_linear_pullback_composition _ _ _).
Qed.
