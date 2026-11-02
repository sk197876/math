(** Federer (1969), 3.1.11, p. 222: the general Leibniz
    formula on the intersection of the two actual domains.
    Both differentiability and the coefficient identity are proved. *)
From mathcomp Require Import all_boot all_order all_algebra reals.
From Federer Require Import Hom TensorUP BoundedHom Bilinear RealNormUP NormDifferentialUP
  SymmetricForms SymmetricFormSum SymmetricFormProduct
  ContinuousMultilinearUP NormHigherDifferentialUP NormHigherDifferentialLocal
  NormHigherSymmetricFormUP NormClassHigherUP NormClassHigherRestriction
  NormBoundedBilinearUP NormClassHigherBilinear NormHigherLeibniz.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [norm_higher_leibniz_intersection]: the hypotheses
    a in dmn f intersect dmn g and f,g of class k, followed by
    the displayed Leibniz formula, Federer 3.1.11, p. 222.
    Restricting the exact differential graphs to this open intersection
    introduces no extra hypothesis. The result covers noncommutative
    normed-algebra multiplication and includes order zero. *)
Theorem norm_higher_leibniz_intersection (R : realType)
    (X Y : lmodType R) (NX : X->R) (NY : Y->R)
    (hNX : is_real_norm NX) (hNY : is_real_norm NY)
    (Z : nat->lmodType R)
    (ev : forall i, {ffun 'I_i->X}->Hom (Z i) Y)
    (ZN : forall i, Z i->R)
    (hZ : forall i, is_continuous_multilinear_space NX NY (@ev i) (@ZN i))
    (mu : Y->Y->Y) (hmu : bilinear mu)
    (hM : forall x y, NY (mu x y)<=NY x*NY y)
    (A B : X->Prop) (f g : X->Y) k a
    (phi psi : forall i, S_m X Y i) :
  A a -> B a ->
  norm_class_higher NX NY ev ZN A f k ->
  norm_class_higher NX NY ev ZN B g k ->
  (forall i, (i<=k)%N -> is_norm_higher_differential_form NX ev ZN A f i a (phi i)) ->
  (forall i, (i<=k)%N -> is_norm_higher_differential_form NX ev ZN B g i a (psi i)) ->
  norm_class_higher NX NY ev ZN (fun x=>A x /\ B x) (fun x=>mu (f x) (g x)) k /\
  forall i, (i<=k)%N -> forall eta : S_m X Y i,
    is_norm_higher_differential_form NX ev ZN (fun x=>A x /\ B x)
      (fun x=>mu (f x) (g x)) i a eta ->
    sform_include eta=\sum_(j<i.+1) symmetric_forms_product hmu
      (sform_include (phi (i-j)%N)) (sform_include (psi j)).
Proof.
move=>ha hb hf hg hphi hpsi.
pose O x := A x /\ B x.
have hOA x (hx : O x) : A x := hx.1.
have hOB x (hx : O x) : B x := hx.2.
have hopen x (hx : O x) : norm_domain_interior NX O x.
  have [r [hr hAr]] := (hf.1 x hx.1).1.
  have [s [hs hBs]] := (hg.1 x hx.2).1.
  exists (Num.min r s); split; first by rewrite lt_min hr hs.
  move=>v; rewrite lt_min=>/andP [hvr hvs].
  exact (conj (hAr v hvr) (hBs v hvs)).
have hfa := @norm_class_higher_open_restriction R X Y NX NY hNX hNY
  Z ev ZN hZ A O f k hOA hopen hf.
have hga := @norm_class_higher_open_restriction R X Y NX NY hNX hNY
  Z ev ZN hZ B O g k hOB hopen hg.
have hprod : norm_bounded_bilinear NY NY NY mu.
  split; first exact hmu.
  exists 1; split; first exact: ler01.
  by move=>x y; rewrite mul1r; exact: hM.
split.
- exact (@norm_class_higher_bilinear R X NX hNX k Y Y Y NY NY NY
    hNY hNY hNY Z Z Z ev ZN ev ZN ev ZN hZ hZ hZ O f g mu hprod hfa hga).
- have hph i (hi : (i<=k)%N) :
      is_norm_higher_differential_form NX ev ZN O f i a (phi i).
    have [z [hz he]] := hphi i hi; exists z; split; last exact he.
    exact ((@norm_higher_differential_open_restriction R X Y NX NY hNX hNY
      Z ev ZN hZ i A O f hOA hopen a (conj ha hb) z).1 hz).
  have hps i (hi : (i<=k)%N) :
      is_norm_higher_differential_form NX ev ZN O g i a (psi i).
    have [z [hz he]] := hpsi i hi; exists z; split; last exact he.
    exact ((@norm_higher_differential_open_restriction R X Y NX NY hNX hNY
      Z ev ZN hZ i B O g hOB hopen a (conj ha hb) z).1 hz).
  exact (@norm_higher_leibniz R X Y NX NY hNX hNY Z ev ZN hZ
    mu hmu hM O f g k a phi psi (conj ha hb) hfa hga hph hps).
Qed.
