(** Federer (1969), 3.1.11, p. 222: the general
    composition formula for higher differentials. The proof compares
    the actual differentials with the composition of the two jets,
    expands by the multinomial theorem, and uses polarization. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import Hom HomogeneousHom RealNormUP SymmetricAlgebra
  SymmetricForms SymmetricFormExtension HomogeneousPolynomialFunctions
  PolynomialFunctions PolynomialTaylor PolynomialCompositionMap
  PolynomialLineCoefficient ContinuousMultilinearUP NormHigherDifferentialUP
  NormHigherSymmetricFormUP NormClassHigherUP NormJetUP NormJetSealed
  NormJetCompositionDifferentials NormCompositionJetLineExpansion
  CompositionMultinomial CompositionFormCoefficient.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [norm_higher_composition_formula]: the displayed
    formula D^p(g composed with f)(a), summed over S(p),
    Federer 3.1.11, p. 222. The coefficient on the right
    is the symmetric-form sum defined above, with outer degree
    sum alpha and denominator alpha!. The source, intermediate and
    target spaces are arbitrary normed real vector spaces. *)
Theorem norm_higher_composition_formula (R : realType)
    (X Y T : lmodType R) (NX : X->R) (NY : Y->R) (NT : T->R)
    (hNX : is_real_norm NX) (hNY : is_real_norm NY) (hNT : is_real_norm NT)
    (Z W U : nat->lmodType R)
    (ez : forall i, {ffun 'I_i->X}->Hom (Z i) Y) (ZN : forall i, Z i->R)
    (ew : forall i, {ffun 'I_i->Y}->Hom (W i) T) (WN : forall i, W i->R)
    (eu : forall i, {ffun 'I_i->X}->Hom (U i) T) (UN : forall i, U i->R)
    (hZ : forall i, is_continuous_multilinear_space NX NY (@ez i) (@ZN i))
    (hW : forall i, is_continuous_multilinear_space NY NT (@ew i) (@WN i))
    (hU : forall i, is_continuous_multilinear_space NX NT (@eu i) (@UN i))
    (A : X->Prop) (B : Y->Prop) (f : X->Y) (g : Y->T) k a
    (phi : forall i, S_m X Y i) (psi : forall i, S_m Y T i) :
  (1<=k)%N -> A a -> B (f a) ->
  norm_class_higher NX NY ez ZN A f k ->
  norm_class_higher NY NT ew WN B g k ->
  (forall i, (i<=k)%N -> is_norm_higher_differential_form NX ez ZN A f i a (phi i)) ->
  (forall i, (i<=k)%N -> is_norm_higher_differential_form NY ew WN B g i (f a) (psi i)) ->
  forall p, (1<=p<=k)%N -> forall eta : S_m X T p,
    is_norm_higher_differential_form NX eu UN
      (fun x=>A x /\ B (f x)) (fun x=>g (f x)) p a eta ->
    eta=composition_differential_form_coefficient k phi psi p.
Proof.
move=>hk ha hb hf hg hphi hpsi p /andP [hp0 hpk] eta [z [hz hze]].
have [zf [hzf _]] := hphi k (leqnn k).
have [zg [hzg _]] := hpsi k (leqnn k).
pose P := @NormJet.value R X Y NX NY hNX hNY Z ez ZN hZ A f k a zf hzf.
pose Q := @NormJet.value R Y T NY NT hNY hNT W ew WN hW B g k (f a) zg hzg.
have hP := @NormJet.laws R X Y NX NY hNX hNY Z ez ZN hZ A f k a zf hzf.
have hQ := @NormJet.laws R Y T NY NT hNY hNT W ew WN hW B g k (f a) zg hzg.
pose H := polynomial_composite (@pchar_num R) P Q.
have heta : eta=polynomial_taylor_coefficient H p a.
  have hc := @norm_composition_jet_differential_coefficients R X Y T NX NY NT hNX hNY hNT
    Z W U ez ZN ew WN eu UN hZ hW hU A B f g k a P Q
    hk ha hb hf hg hP hQ p hpk z hz.
  apply: symmetric_form_finite_family_extensional=>u; rewrite -hze; exact: hc.
apply: (@sform_polynomial_injective R X T p (@pchar_num R)); apply: funext=>v.
rewrite heta (@composition_differential_form_coefficient_value R X Y T k phi psi (@pchar_num R) p v hpk).
pose c : 'I_k->Y := fun i=>sform_polynomial_value (phi (val i).+1) v.
pose L j : Hom (symmetric_space Y) T := sform_homogeneous (psi j).
have hline t : H (a+t*:v)=\sum_(j<(k*k).+1) t^+j*:composition_weight_coefficient c L j.
  exact (@norm_composition_jet_line_expansion R X Y T NX NY NT hNX hNY hNT
    Z W ez ZN ew WN hZ hW A B f g k a P Q phi psi hP hQ hphi hpsi v t).
have hk2 : (k<=k*k)%N.
  have hh := leq_mul (leqnn k) hk; by rewrite muln1 in hh.
have hpm : (p<(k*k).+1)%N by rewrite ltnS; exact: leq_trans hpk hk2.
exact (@polynomial_line_expansion_coefficient R (@pchar_num R) X T H a v
  (k*k).+1 (composition_weight_coefficient c L) hline p hpm).
Qed.
