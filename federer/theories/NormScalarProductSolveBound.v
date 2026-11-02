(** Federer (1969), 3.1.13, p. 225:
    the actual highest derivative in a scalar
    product sigma*v=u is controlled by lower
    derivatives when sigma>=1. *)
From mathcomp Require Import all_boot all_order all_algebra reals constructive_ereal.
From Federer Require Import Hom ScalarCoefficients RealNormUP SymmetricForms SymmetricOperatorNorm
  ContinuousMultilinearUP NormHigherDifferentialUP NormHigherDifferentialLocal
  NormHigherDifferentialSymmetricForm NormHigherSymmetricFormUP NormHigherSymmetricFormFamilies
  NormClassHigherUP NormHigherLeibniz ScalarSymmetricProductLaws ScalarSymmetricProductSolveBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [norm_scalar_product_solve_bound]:
    a quantitative induction step for the
    normalized derivative bounds in Federer
    3.1.13, p. 225.
    The product identity and actual differential
    laws discharge the abstract form identity;
    no bound on the highest derivative of
    v is assumed. *)
Theorem norm_scalar_product_solve_bound (R : realType)
    (X : lmodType R) (NX : X->R) (hNX : is_real_norm NX)
    (Z : nat->lmodType R)
    (ev : forall i, {ffun 'I_i->X}->Hom (Z i) R^o)
    (ZN : forall i, Z i->R)
    (hZ : forall i, is_continuous_multilinear_space NX
      (fun t : R^o=>`|t|%R) (@ev i) (@ZN i))
    (A : X->Prop) (sigma v u : X->R) n a
    (Ds Dv : forall i, Z i) (Du : Z n) H (F G : nat->R) :
  A a ->
  norm_class_higher NX (fun t : R^o=>`|t|%R) ev ZN A sigma n ->
  norm_class_higher NX (fun t : R^o=>`|t|%R) ev ZN A v n ->
  (forall x, A x -> sigma x*v x=u x) ->
  1<=sigma a ->
  (forall i, (i<=n)%N -> has_norm_higher_differential NX ev ZN A sigma i a (Ds i)) ->
  (forall i, (i<=n)%N -> has_norm_higher_differential NX ev ZN A v i a (Dv i)) ->
  has_norm_higher_differential NX ev ZN A u n a Du ->
  @ZN n Du<=H ->
  (forall i, (i<=n)%N -> @ZN i (Ds i)<=F i) ->
  (forall i, (i<n)%N -> @ZN i (Dv i)<=G i) ->
  @ZN n (Dv n)<=H+\sum_(j<n) ('C(n,n-j))%:R*(F (n-j)%N*G j).
Proof.
move=>ha hs hv hproduct hlower hDs hDv hDu hH hF hG.
have [phi hphi] := norm_higher_differential_point_forms hNX
  (@scalar_absolute_value_norm R) hZ hDs.
have [psi hpsi] := norm_higher_differential_point_forms hNX
  (@scalar_absolute_value_norm R) hZ hDv.
have [eta [heta hnorm]] := norm_higher_differential_symmetric_form_exists
  hNX (@scalar_absolute_value_norm R) hZ hDu.
have hA x (hx : A x) := (hs.1 x hx).1.
have hdom x (_ : A x) : (A x<->A x) by [].
have heq x (hx : A x) (_ : A x) : sigma x*v x=u x := hproduct x hx.
have hprodD := (@norm_higher_differential_local_agreement R X R^o NX
  (fun t : R^o=>`|t|%R) hNX (@scalar_absolute_value_norm R) Z ev ZN hZ
  n A A A (fun x=>sigma x*v x) u hA hdom heq a ha Du).2 hDu.
have hprodform : is_norm_higher_differential_form NX ev ZN A
    (fun x=>sigma x*v x) n a eta.
  exists Du; split; first exact hprodD.
  move=>w; rewrite heta; congr (@ev n _ Du).
  by apply/ffunP=>j; rewrite ffunE tnth_mktuple.
have hsub (x y : R^o) : `|x*y|<=`|x|*`|y| by rewrite normrM.
have hidentity := @norm_higher_leibniz R X R^o NX
  (fun t : R^o=>`|t|%R) hNX (@scalar_absolute_value_norm R) Z ev ZN hZ
  (fun x y : R=>x*y) (ScalarCoefficients.scalar_bilinear R) hsub
  A sigma v n a phi psi ha hs hv
  (fun i hi=>(hphi i hi).1) (fun i hi=>(hpsi i hi).1)
  n (leqnn n) eta hprodform.
have hzero := norm_zeroth_differential_form_value (hphi 0%N (leq0n n)).1.
have hopH : (symmetric_operator_norm hNX.1 (fun t : R^o=>`|t|%R) eta<=H%:E)%E.
  by rewrite hnorm lee_fin.
have hopF i (hi : (i<=n)%N) :
    (symmetric_operator_norm hNX.1 (fun t : R^o=>`|t|%R) (phi i)<=(F i)%:E)%E.
  by rewrite (hphi i hi).2 lee_fin; exact: hF.
have hopG i (hi : (i<n)%N) :
    (symmetric_operator_norm hNX.1 (fun t : R^o=>`|t|%R) (psi i)<=(G i)%:E)%E.
  by rewrite (hpsi i (leqW hi)).2 lee_fin; exact: hG.
have hb := scalar_symmetric_product_solve_bound
  hlower hzero hidentity hopH hopF hopG.
by rewrite (hpsi n (leqnn n)).2 lee_fin in hb.
Qed.
