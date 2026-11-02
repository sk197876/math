(** Federer (1969), 3.1.11, pp. 221–222: the jet
    expansion expressed with the Chapter 1 symmetric forms. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom RealNormUP SymmetricForms PolynomialFunctions
  HomogeneousPolynomialFunctions PolynomialDiagonalNorm ContinuousMultilinearUP
  NormHigherDifferentialUP NormHigherDifferentialUnique NormHigherSymmetricFormUP
  NormTaylorRemainderBound NormJetUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [norm_zeroth_differential_form_value]: the
    constant Taylor coefficient is f(a), including in the composition
    calculation of Federer 3.1.11, pp. 221–222. *)
Lemma norm_zeroth_differential_form_value (R : realType)
    (X Y : lmodType R) (NX : X->R)
    (Z : nat->lmodType R)
    (ev : forall i, {ffun 'I_i->X}->Hom (Z i) Y) (ZN : forall i, Z i->R)
    (A : X->Prop) (f : X->Y) a (phi : S_m X Y 0) :
  is_norm_higher_differential_form NX ev ZN A f 0%N a phi ->
  forall v, sform_polynomial_value phi v=f a.
Proof.
move=>[z [hz he]] v.
rewrite sform_polynomial_diagonal_value fact0 invr1 scale1r.
have hh := he [ffun _ : 'I_0=>v].
have ht : [tuple [ffun _ : 'I_0=>v] j | j<0]=[tuple v | j<0].
  by apply: eq_from_tnth=>j; rewrite !tnth_mktuple ffunE.
rewrite ht in hh; rewrite -hh.
have he0 : [ffun _ : 'I_0=>v]=[ffun _ : 'I_0=>(0:X)].
  by apply/ffunP=>i; case:i.
by rewrite he0; exact hz.2.
Qed.

(** Source for [norm_jet_expansion_forms]: the displayed
    formula defining the kth jet, Federer 3.1.11, p. 221,
    in the symmetric-form notation used on p. 222. *)
Theorem norm_jet_expansion_forms (R : realType)
    (X Y : lmodType R) (NX : X->R) (NY : Y->R)
    (hNX : is_real_norm NX) (hNY : is_real_norm NY)
    (Z : nat->lmodType R)
    (ev : forall i, {ffun 'I_i->X}->Hom (Z i) Y) (ZN : forall i, Z i->R)
    (hZ : forall i, is_continuous_multilinear_space NX NY (@ev i) (@ZN i))
    (A : X->Prop) (f : X->Y) k a (P : PolynomialFunction X Y)
    (phi : forall i, S_m X Y i) :
  is_norm_jet_polynomial NX ev ZN A f k a P ->
  (forall i, (i<=k)%N -> is_norm_higher_differential_form NX ev ZN A f i a (phi i)) ->
  forall v, P (a+v)=\sum_(i<k.+1) sform_polynomial_value (phi i) v.
Proof.
move=>hP hphi v.
have [D [hD he]] := norm_jet_polynomial_expansion hP.
rewrite he /norm_taylor_value.
have hshift : a+v-a=v by rewrite addrAC subrr add0r.
rewrite hshift.
apply: eq_bigr=>i _.
have hi : (i<=k)%N by move:(ltn_ord i); rewrite ltnS.
have [z [hz hzE]] := hphi i hi.
have hDz := norm_higher_differential_unique hNX hNY hZ (hD i hi) hz.
rewrite hDz sform_polynomial_diagonal_value hzE.
congr (_*:phi i _); apply: eq_from_tnth=>j.
by rewrite !tnth_mktuple ffunE.
Qed.

(** Source for [norm_jet_positive_expansion_forms]: separating
    f(a) from the positive-degree terms of the jet, as in
    the composition calculation of Federer 3.1.11, p. 222.
    The base point need not be translated to zero in the statement. *)
Theorem norm_jet_positive_expansion_forms (R : realType)
    (X Y : lmodType R) (NX : X->R) (NY : Y->R)
    (hNX : is_real_norm NX) (hNY : is_real_norm NY)
    (Z : nat->lmodType R)
    (ev : forall i, {ffun 'I_i->X}->Hom (Z i) Y) (ZN : forall i, Z i->R)
    (hZ : forall i, is_continuous_multilinear_space NX NY (@ev i) (@ZN i))
    (A : X->Prop) (f : X->Y) k a (P : PolynomialFunction X Y)
    (phi : forall i, S_m X Y i) :
  is_norm_jet_polynomial NX ev ZN A f k a P ->
  (forall i, (i<=k)%N -> is_norm_higher_differential_form NX ev ZN A f i a (phi i)) ->
  forall v, P (a+v)=f a+\sum_(i<k) sform_polynomial_value (phi (val i).+1) v.
Proof.
move=>hP hphi v.
rewrite (norm_jet_expansion_forms hNX hNY hZ hP hphi) big_ord_recl /=.
by rewrite (norm_zeroth_differential_form_value (hphi 0%N (leq0n k))).
Qed.
