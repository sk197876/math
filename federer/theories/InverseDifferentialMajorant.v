(** Federer (1969), 3.1.24, pp. 239–240: the differential
    bounds for a smooth inverse follow by induction from the
    exact composition identity and the scalar majorant recurrence. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals constructive_ereal.
From Federer Require Import Hom TensorUP HomogeneousHom RealNormUP NormDifferentialUP
  ContinuousMultilinearUP ContinuousMultilinearSealed ContinuousMultilinearNorm
  NormDifferentialInverseIdentities NormDifferentialLinear NormDifferentialEnlarge NormRegularity NormSmoothFields
  NormHigherDifferentialUP NormHigherDifferentialUnique NormHigherDifferentialLocal NormHigherSymmetricFormUP
  NormHigherSymmetricFormFamilies NormHigherCompositionFormula NormLinearHigherVanishing
  SymmetricAlgebra SymmetricForms SymmetricOperatorNorm SymmetricFirstDerivativeMap SymmetricFormExtension
  InverseMajorantUP InverseMajorantNonnegative InverseCompositionFormBound.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Source for [inverse_differential_majorant]: the assertion
    ||D^p f(x)||<=lambda_p p! in Federer 3.1.24, p. 240.
    First derivatives have the prescribed bound, and higher outer
    derivatives have gamma^m m!. The two original inverse domains
    are retained when deriving the first differential identities.
    No completeness assumption is needed. *)
Theorem inverse_differential_majorant (R:realType) (X Y:lmodType R)
    (NX:X->R) (NY:Y->R) (hNX:is_real_norm NX) (hNY:is_real_norm NY)
    (A:X->Prop) (B:Y->Prop) (V:X->Prop) (U:Y->Prop) (f:X->Y) (g:Y->X)
    b gamma (lambda:nat->R) :
  (forall x,A x -> B (f x)) -> (forall y,B y -> A (g y)) ->
  (forall x,A x -> g (f x)=x) -> (forall y,B y -> f (g y)=y) ->
  (forall x,V x -> A x /\ U (f x)) -> (forall y,U y -> B y) ->
  norm_class_all_orders hNX hNY V f -> norm_class_all_orders hNY hNX U g ->
  0<b -> 0<gamma -> is_inverse_majorant_sequence b gamma lambda ->
  (forall x,V x -> forall z:@ContinuousMultilinear.space R 1 X Y NX NY hNX hNY,
    has_norm_higher_differential NX
      (fun j=>@ContinuousMultilinear.evaluation R j X Y NX NY hNX hNY)
      (fun j=>@ContinuousMultilinear.norm R j X Y NX NY hNX hNY) V f 1 x z ->
    @ContinuousMultilinear.norm R 1 X Y NX NY hNX hNY z<=lambda 1%N) ->
  (forall m,(2<=m)%N -> forall y,U y -> forall z:@ContinuousMultilinear.space R m Y X NY NX hNY hNX,
    has_norm_higher_differential NY
      (fun j=>@ContinuousMultilinear.evaluation R j Y X NY NX hNY hNX)
      (fun j=>@ContinuousMultilinear.norm R j Y X NY NX hNY hNX) U g m y z ->
    @ContinuousMultilinear.norm R m Y X NY NX hNY hNX z<=gamma^+m*(m`!)%:R) ->
  forall p,(1<=p)%N -> forall x,V x -> forall z:@ContinuousMultilinear.space R p X Y NX NY hNX hNY,
    has_norm_higher_differential NX
      (fun j=>@ContinuousMultilinear.evaluation R j X Y NX NY hNX hNY)
      (fun j=>@ContinuousMultilinear.norm R j X Y NX NY hNX hNY) V f p x z ->
    @ContinuousMultilinear.norm R p X Y NX NY hNX hNY z<=lambda p*(p`!)%:R.
Proof.
move=>hfmap hgmap hgf hfg hV hU hf hg hb hgamma hLambda hFirst hOuter.
pose Z i:=@ContinuousMultilinear.space R i X Y NX NY hNX hNY.
pose ez i:=@ContinuousMultilinear.evaluation R i X Y NX NY hNX hNY.
pose ZN i:=@ContinuousMultilinear.norm R i X Y NX NY hNX hNY.
pose hZ i:=@ContinuousMultilinear.laws R i X Y NX NY hNX hNY.
pose W i:=@ContinuousMultilinear.space R i Y X NY NX hNY hNX.
pose ew i:=@ContinuousMultilinear.evaluation R i Y X NY NX hNY hNX.
pose WN i:=@ContinuousMultilinear.norm R i Y X NY NX hNY hNX.
pose hW i:=@ContinuousMultilinear.laws R i Y X NY NX hNY hNX.
pose P i:=@ContinuousMultilinear.space R i X X NX NX hNX hNX.
pose ep i:=@ContinuousMultilinear.evaluation R i X X NX NX hNX hNX.
pose PN i:=@ContinuousMultilinear.norm R i X X NX NX hNX hNX.
pose hP i:=@ContinuousMultilinear.laws R i X X NX NX hNX hNX.
have hOpen x (hx:V x):norm_domain_interior NX V x:=((hf 0%N).1 x hx).1.
have hUOpen y (hy:U y):norm_domain_interior NY U y:=((hg 0%N).1 y hy).1.
have [F hF]:=@norm_smooth_fields_exist R X Y NX NY hNX hNY V f hf.
have [G hG]:=@norm_smooth_fields_exist R Y X NY NX hNY hNX U g hg.
have hNonneg:=inverse_majorant_sequence_nonnegative hb hgamma hLambda.
elim/ltn_ind=>p ih hp x hx z hz.
case:p ih hp z hz=>[|[|p]] ih hp z hz; first by [].
- rewrite mulr1; exact (hFirst x hx z hz).
- have hp2:(2<=p.+2)%N by [].
  have hpp:(1<=p.+2<=p.+2)%N by rewrite leqnn andbT.
  have hxA:=(hV x hx).1.
  have hfx:=(hV x hx).2.
  have [phi hphi]:=@norm_higher_differential_point_forms R X Y NX NY hNX hNY Z ez ZN hZ
    V f p.+2 x (fun i=>F i x) (fun i _=>(hF i).1 x hx).
  have [psi hpsi]:=@norm_higher_differential_point_forms R Y X NY NX hNY hNX W ew WN hW
    U g p.+2 (f x) (fun i=>G i (f x)) (fun i _=>(hG i).1 (f x) hfx).
  have hPhi i (hi:(i<=p.+2)%N):= (hphi i hi).1.
  have hPsi i (hi:(i<=p.+2)%N):= (hpsi i hi).1.
  have hPhiOne:=hPhi 1%N (leq0n p.+1).
  have hPsiOne:=hPsi 1%N (leq0n p.+1).
  pose L:=symmetric_first_derivative_map (phi 1%N).
  pose M:=symmetric_first_derivative_map (psi 1%N).
  have hDf:=norm_first_form_map_actual hNX hNY hZ hPhiOne.
  have hDg:=norm_first_form_map_actual hNY hNX hW hPsiOne.
  have hDfA:has_norm_differential NX NY A f x L.
    exact (norm_differential_enlarge
      (fun t ht=>(hV t ht).1) hDf).
  have hDgB:has_norm_differential NY NX B g (f x) M.
    exact (norm_differential_enlarge hU hDg).
  have hDfg:has_norm_differential NX NY A f (g (f x)) L by rewrite hgf.
  have hInv:=@norm_differentials_left_inverse R Y X NY NX hNY hNX B A g f (f x) M L
    hgmap hfg hDgB hDfg.
  have hLinv y:L (sform_homogeneous (psi 1%N) (symmetric_generator y))=y.
    have hh:=congr1 (fun H:Hom Y Y=>H y) hInv.
    change (L (M y)=y) in hh; exact hh.
  have hOne:(symmetric_operator_norm hNX.1 NY (phi 1%N)<=(lambda 1%N)%:E)%E.
    rewrite (hphi 1%N (leq0n p.+1)).2 lee_fin.
    exact (hFirst x hx (F 1%N x) ((hF 1%N).1 x hx)).
  have hLb:=@symmetric_first_derivative_map_bound R X Y NX NY hNX hNY (phi 1%N) (lambda 1%N) hOne.
  pose C:=fun i:'I_p.+2=>ZN (val i).+1 (F (val i).+1 x).
  have hC i:0<=C i:=multilinear_operator_nonnegative
    (continuous_multilinear_norm_laws (hZ (val i).+1) (F (val i).+1 x)).
  have hCB i:(symmetric_operator_norm hNX.1 NY (phi (val i).+1)<=(C i)%:E)%E.
    by rewrite (hphi (val i).+1 (ltn_ord i)).2.
  have hLower i (hi:((val i).+1<p.+2)%N):C i<=lambda (val i).+1*((val i).+1`!)%:R.
    exact (ih (val i).+1 hi (leq0n (val i)) x hx (F (val i).+1 x) ((hF (val i).+1).1 x hx)).
  have hPB j (hj:(2<=j<=p.+2)%N):
      (symmetric_operator_norm hNY.1 NX (psi j)<=(gamma^+j*(j`!)%:R)%:E)%E.
    rewrite (hpsi j (andP hj).2).2 lee_fin.
    exact (hOuter j (andP hj).1 (f x) hfx (G j (f x)) ((hG j).1 (f x) hfx)).
  pose D:=fun t=>V t /\ U (f t).
  have hDOpen t (ht:D t):norm_domain_interior NX D t.
    have [r [hr hrV]]:=hOpen t ht.1.
    exists r; split; first exact hr.
    move=>v hv; have hh:=hrV v hv; exact (conj hh (hV (t+v) hh).2).
  have hidBound:norm_bounded_linear NX NX (hom_of_linear (linear_id X)).
    exists 1; split; first exact:ler01.
    by move=>v; rewrite hom_of_linearE mul1r.
  have hdId:=@norm_linear_higher_vanishing R X X NX NX hNX hNX P ep PN hP D hDOpen
    (hom_of_linear (linear_id X)) hidBound p.+2 hp2 x (conj hx hfx).
  have hdComp:has_norm_higher_differential NX ep PN D (fun v=>g (f v)) p.+2 x 0.
    apply:(proj1 (@norm_higher_differential_local_agreement R X X NX NX hNX hNX P ep PN hP
      p.+2 D D D (hom_of_linear (linear_id X)) (fun v=>g (f v)) hDOpen
      (fun _ _=>iff_refl _) _ x (conj hx hfx) 0)) hdId.
    by move=>v hv _; rewrite hom_of_linearE hgf //; exact (hV v hv.1).1.
  have hZero:is_norm_higher_differential_form NX ep PN D (fun v=>g (f v)) p.+2 x 0.
    exists 0; split; first exact hdComp.
    by move=>u; rewrite linear0 sform_zeroE.
  have hComp:=@norm_higher_composition_formula R X Y X NX NY NX hNX hNY hNX Z W P
    ez ZN ew WN ep PN hZ hW hP V U f g p.+2 x phi psi (leq0n p.+1) hx hfx (hf p.+2) (hg p.+2)
    hPhi hPsi p.+2 hpp 0 hZero.
  have hbnd:=@inverse_composition_form_bound R X Y NX NY hNX hNY p.+2 phi psi C lambda gamma L
    hp2 (ltW hgamma) hNonneg hC hCB hLower hPB hLb hLinv (esym hComp).
  rewrite (hphi p.+2 (leqnn _)).2 lee_fin in hbnd.
  have heq:=norm_higher_differential_unique hNX hNY hZ hz ((hF p.+2).1 x hx).
  rewrite heq (hLambda.2.2 p.+2 hp2) mulrAC.
  exact hbnd.
Qed.
