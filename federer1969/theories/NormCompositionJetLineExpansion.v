(** Federer (1969), 3.1.11, p. 222: the exact
    multinomial expansion of Q_b composed with P_a on a line.
    The constant terms and both base points are retained. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom HomogeneousHom RealNormUP SymmetricAlgebra
  SymmetricForms SymmetricFormExtension SymmetricFormIsomorphism HomogeneousPolynomialFunctions PolynomialFunctions
  ContinuousMultilinearUP NormHigherSymmetricFormUP NormJetUP
  NormJetFormExpansion CompositionMultinomial.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [norm_composition_jet_line_expansion]: the
    computation of Q_b(P_a(a+t v)) by weighted degree, Federer
    3.1.11, p. 222. Here c_i is D^i f(a) evaluated
    on v^i/i!, and the outer forms act linearly on the
    symmetric algebra, exactly as specified in the book. *)
Theorem norm_composition_jet_line_expansion (R : realType)
    (X Y T : lmodType R) (NX : X->R) (NY : Y->R) (NT : T->R)
    (hNX : is_real_norm NX) (hNY : is_real_norm NY) (hNT : is_real_norm NT)
    (Z W : nat->lmodType R)
    (ez : forall i, {ffun 'I_i->X}->Hom (Z i) Y) (ZN : forall i, Z i->R)
    (ew : forall i, {ffun 'I_i->Y}->Hom (W i) T) (WN : forall i, W i->R)
    (hZ : forall i, is_continuous_multilinear_space NX NY (@ez i) (@ZN i))
    (hW : forall i, is_continuous_multilinear_space NY NT (@ew i) (@WN i))
    (A : X->Prop) (B : Y->Prop) (f : X->Y) (g : Y->T) k a
    (P : PolynomialFunction X Y) (Q : PolynomialFunction Y T)
    (phi : forall i, S_m X Y i) (psi : forall i, S_m Y T i) :
  is_norm_jet_polynomial NX ez ZN A f k a P ->
  is_norm_jet_polynomial NY ew WN B g k (f a) Q ->
  (forall i, (i<=k)%N -> is_norm_higher_differential_form NX ez ZN A f i a (phi i)) ->
  (forall i, (i<=k)%N -> is_norm_higher_differential_form NY ew WN B g i (f a) (psi i)) ->
  forall v t, Q (P (a+t*:v))=
    \sum_(p<(k*k).+1) t^+p*:
      composition_weight_coefficient
        (fun i : 'I_k=>sform_polynomial_value (phi (val i).+1) v)
        (fun j=>(sform_homogeneous (psi j) : Hom (symmetric_space Y) T)) p.
Proof.
move=>hP hQ hphi hpsi v t.
have hPe := norm_jet_positive_expansion_forms hNX hNY hZ hP hphi (t*:v).
have hPline : P (a+t*:v)=f a+
    \sum_(i<k) t^+(val i).+1*:sform_polynomial_value (phi (val i).+1) v.
  rewrite hPe; congr (f a+_); apply: eq_bigr=>i _.
  exact: sform_polynomial_scale_argument.
rewrite hPline (norm_jet_expansion_forms hNY hNT hW hQ hpsi).
exact (@composition_multinomial_collected R (@pchar_num R) Y T k
  (fun i : 'I_k=>sform_polynomial_value (phi (val i).+1) v)
  (fun j=>(sform_homogeneous (psi j) : Hom (symmetric_space Y) T)) t).
Qed.
