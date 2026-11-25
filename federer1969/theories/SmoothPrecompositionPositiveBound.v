(** Federer (1969), 4.1.7, p. 359:
    each positive derivative of actual smooth
    precomposition is bounded by finitely many
    original outer derivatives. Reuse the exact
    composition formula of 3.1.11, p. 222,
    and its already proved finite bound. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals constructive_ereal.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormRegularity
  ContinuousMultilinearUP ContinuousMultilinearSealed NormHigherDifferentialUP NormHigherDifferentialLocal
  NormHigherDifferentialSymmetricForm NormHigherSymmetricFormUP NormHigherSymmetricFormFamilies
  NormHigherCompositionFormula SymmetricForms SymmetricOperatorNorm
  SymmetricMultiIndices SymmetricDividedMonomials CompositionMultiIndices CompositionFormCoefficient
  CompositionFiniteOuterBound SmoothFunctionSpaceUP SmoothFunctionDerivativesUP SmoothPrecompositionUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section SmoothPrecompositionPositiveBound.
Variable R:realType.
Variables X Y T:lmodType R.
Variables (NX:X->R) (NY:Y->R) (NT:T->R).
Hypotheses (hNX:is_real_norm NX) (hNY:is_real_norm NY) (hNT:is_real_norm NT).
Variables (A:X->Prop) (B:Y->Prop).
Variables E F:lmodType R.
Variables (ev:E->Y->T) (fv:F->X->T).
Hypothesis hE:is_smooth_function_space hNY hNT B ev.
Local Notation Z := (fun j=>@ContinuousMultilinear.space R j X Y NX NY hNX hNY).
Local Notation ez := (fun j=>@ContinuousMultilinear.evaluation R j X Y NX NY hNX hNY).
Local Notation ZN := (fun j=>@ContinuousMultilinear.norm R j X Y NX NY hNX hNY).
Local Notation hZ := (fun j=>@ContinuousMultilinear.laws R j X Y NX NY hNX hNY).
Local Notation W := (fun j=>@ContinuousMultilinear.space R j Y T NY NT hNY hNT).
Local Notation ew := (fun j=>@ContinuousMultilinear.evaluation R j Y T NY NT hNY hNT).
Local Notation WN := (fun j=>@ContinuousMultilinear.norm R j Y T NY NT hNY hNT).
Local Notation hW := (fun j=>@ContinuousMultilinear.laws R j Y T NY NT hNY hNT).
Local Notation V := (fun j=>@ContinuousMultilinear.space R j X T NX NT hNX hNT).
Local Notation eq := (fun j=>@ContinuousMultilinear.evaluation R j X T NX NT hNX hNT).
Local Notation VN := (fun j=>@ContinuousMultilinear.norm R j X T NX NT hNX hNT).
Local Notation hV := (fun j=>@ContinuousMultilinear.laws R j X T NX NT hNX hNT).
Variable D:forall j,Y->Hom E (W j).
Variable G:forall j,X->Hom F (V j).
Hypothesis hD:@is_smooth_function_derivatives R Y T NY NT hNY hNT B E ev D.
Hypothesis hG:@is_smooth_function_derivatives R X T NX NT hNX hNT A F fv G.
Variable f:X->Y.
Hypothesis hImage:forall x,A x->B (f x).
Arguments hImage : clear implicits.
Hypothesis hf:norm_class_all_orders hNX hNY A f.
Variable P:Hom E F.
Hypothesis hP:is_smooth_precomposition A ev fv f P.

(** Source for [smooth_precomposition_positive_bound]:
    a bound on the original inner
    derivatives gives one finite coefficient
    controlling the positive derivative of
    precomposition, supporting Federer 4.1.7,
    p. 359. The coefficient is
    uniform in the outer function and
    the source point; its existence follows
    from the original finite composition sum. *)
Theorem smooth_precomposition_positive_bound p C:
  (1<=p)%N->0<=C->exists L:R,0<=L /\
  forall (df:forall j,X->Z j),
    (forall j x,A x->has_norm_higher_differential NX ez ZN A f j x (df j x))->
    forall x,A x->
    (forall j,(1<=j<=p)%N->@ZN j (df j x)<=C)->
    forall h b,0<=b->
      (forall j,(1<=j<=p)%N->@WN j (@D j (f x) h)<=b)->
      @VN p (@G p x (P h))<=L*b.
Proof.
move=>hp hC.
pose M:R:=\sum_(alpha:composition_indices p p)
  ((p`!)%:R/(symmetric_multi_factorial (composition_indices_unbound alpha))%:R)*
    symmetric_scalar_monomial (fun i:'I_p=>C/((val i).+1`!)%:R)
      (composition_indices_unbound alpha).
exists `|M|;split;first exact:normr_ge0.
move=>df hdf x hx hInner h b hb hOuter.
have [phi hPhi]:=@norm_higher_differential_point_forms R X Y NX NY hNX hNY
  Z ez ZN hZ A f p x (fun j=>df j x) (fun j _=>hdf j x hx).
have [psi hPsi]:=@norm_higher_differential_point_forms R Y T NY NT hNY hNT
  W ew WN hW B (ev h) p (f x) (fun j=>@D j (f x) h)
  (fun j _=>smooth_derivative_exact hD j h (hImage x hx)).
have hActual:has_norm_higher_differential NX eq VN
    (fun z=>A z /\ B (f z)) (fun z=>ev h (f z)) p x (@G p x (P h)).
  have hOld:has_norm_higher_differential NX eq VN A (fv (P h)) p x (@G p x (P h)).
    exact:(@smooth_derivative_exact R X T NX NT hNX hNT A F fv G hG p (P h) x hx).
  have hLocal:=@norm_higher_differential_local_agreement R X T NX NT hNX hNT V eq VN hV p
    A (fun z=>A z /\ B (f z)) A (fv (P h)) (fun z=>ev h (f z))
    (fun z hz=>((hf 0%N).1 z hz).1)
    (fun z hz=>conj (fun ha=>conj ha (hImage z ha)) (fun hBoth:A z /\ B (f z)=>proj1 hBoth))
    (fun z hz _=>@hP h z hz) x hx (@G p x (P h)).
  exact:(hLocal.1 hOld).
have [eta [hEta hEtaNorm]]:=@norm_higher_differential_symmetric_form_exists R p X T
  NX NT hNX hNT V eq VN hV (fun z=>A z /\ B (f z)) (fun z=>ev h (f z)) x
  (@G p x (P h)) hActual.
have hEtaActual:is_norm_higher_differential_form NX eq VN
    (fun z=>A z /\ B (f z)) (fun z=>ev h (f z)) p x eta.
  exists (@G p x (P h));split;first exact:hActual.
  move=>u;rewrite hEta;congr (@eq p _ (@G p x (P h))).
  by apply/ffunP=>i;rewrite ffunE tnth_mktuple.
have hpp:(1<=p<=p)%N by rewrite hp leqnn.
have hEquation:=@norm_higher_composition_formula R X Y T NX NY NT hNX hNY hNT
  Z W V ez ZN ew WN eq VN hZ hW hV A B f (ev h) p x phi psi hp hx (hImage x hx)
  (hf p) (smooth_function_evaluation_smooth hE h p)
  (fun j hj=>(hPhi j hj).1) (fun j hj=>(hPsi j hj).1)
  p hpp eta hEtaActual.
have hPhiBound (i:'I_p):(symmetric_operator_norm hNX.1 NY (phi (val i).+1)<=C%:E)%E.
  rewrite (hPhi _ (valP i)).2 lee_fin.
  apply:hInner;apply/andP;split;first by [].
  exact:(valP i).
have hPsiBound j (hj:(1<=j<=p)%N):
    (symmetric_operator_norm hNY.1 NT (psi j)<=b%:E)%E.
  rewrite (hPsi j (andP hj).2).2 lee_fin;exact:hOuter j hj.
have hEstimate:=@composition_form_finite_outer_bound R X Y T NX NY NT hNX hNY hNT
  p phi psi (fun _:'I_p=>C) b hp (fun _=>hC) hPhiBound hb hPsiBound.
rewrite -hEquation hEtaNorm lee_fin in hEstimate.
apply:le_trans hEstimate _.
change (is_true (b*M<=`|M|*b)).
rewrite (mulrC `|M| b);exact:(ler_wpM2l hb (ler_norm M)).
Qed.
End SmoothPrecompositionPositiveBound.
