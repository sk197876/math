(** Federer (1969), 4.1.6, pp. 354–355:
    the full original pullback/exterior-derivative
    equation on the original open domains. The
    actual graph operators and first-differential
    representatives supply the fields; the twice
    differentiable hypothesis is kept literally. *)
From mathcomp Require Import all_boot all_order all_algebra boolp functions reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormDifferentialDirectional
  NormHigherDifferentialUP NormHigherDifferentialFirst NormHigherDifferentialUnique NormHigherDifferential
  ContinuousMultilinearUP ContinuousMultilinearOne
  InnerNorm HilbertFormCompactness EuclideanInnerProduct GrassmannAbbreviations Alternating
  EuclideanFormNorm ExteriorDifferentialUP ExteriorDifferentialSealed ExteriorDerivativeUP ExteriorDerivativeSealed
  PartialFunctionUP PartialFunctionExtensionSealed DifferentialFormPullbackUP
  VectorFormPullbackDifferential.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope ring_scope.

(** Source for [original_exterior_derivative_field_exists]:
    differentiability at every point of the original
    domain supplies the original derivative field,
    Federer 4.1.6, p. 352. The opaque
    partial graph and its existing total representative
    determine values only on that domain. *)
Theorem original_exterior_derivative_field_exists (R:realType) (h2:(1+1:R)!=0) n (W:lmodType R)
    (NW:W->R) (hNW:is_real_norm NW) m (B:R_n R n->Prop) (phi:R_n R n->A_m (R_n R n) W m):
  (forall y,B y->norm_differentiable_at (inner_norm (@euclidean_inner_productP R n))
      (@euclidean_form_norm R h2 n W NW hNW m) B phi y)->
  exists dphi:R_n R n->A_m (R_n R n) W m.+1,
    forall y,B y->has_exterior_derivative (inner_norm (@euclidean_inner_productP R n))
      (@euclidean_form_norm R h2 n W NW hNW m) B phi y (dphi y).
Proof.
move=>hPhi.
pose D:=@ExteriorDerivative.value R (R_n R n) W (inner_norm (@euclidean_inner_productP R n))
  (inner_norm_real_norm (@euclidean_inner_productP R n)) m
  (@euclidean_form_norm R h2 n W NW hNW m) (@euclidean_form_norm_real_norm R h2 n W NW hNW m) B phi.
exists (@PartialFunctionExtension.value (R_n R n) (A_m (R_n R n) W m.+1) D 0)=>y hy.
have [M hM]:=hPhi y hy.
have hDerivative:has_exterior_derivative (inner_norm (@euclidean_inner_productP R n))
    (@euclidean_form_norm R h2 n W NW hNW m) B phi y (@ExteriorDifferential.value R h2 n W m M).
  exists M; split=>//; exact:ExteriorDifferential.laws.
have hGraph:partial_function_graph D y (@ExteriorDifferential.value R h2 n W m M).
  exact:(@ExteriorDerivative.laws R (R_n R n) W (inner_norm (@euclidean_inner_productP R n))
    (inner_norm_real_norm (@euclidean_inner_productP R n)) m
    (@euclidean_form_norm R h2 n W NW hNW m) (@euclidean_form_norm_real_norm R h2 n W NW hNW m)
    B phi y _).2 hDerivative.
rewrite (@PartialFunctionExtension.laws (R_n R n) (A_m (R_n R n) W m.+1) D 0 y _ hGraph).
exact:hDerivative.
Qed.

Section PullbackExteriorDerivative.
Variable R:realType.
Hypothesis h2:(1+1:R)!=0.
Variables v n:nat.
Local Notation X:=(R_n R v).
Local Notation Y:=(R_n R n).
Local Notation NX:=(inner_norm (@euclidean_inner_productP R v)).
Local Notation NY:=(inner_norm (@euclidean_inner_productP R n)).
Local Notation hNX:=(inner_norm_real_norm (@euclidean_inner_productP R v)).
Local Notation hNY:=(inner_norm_real_norm (@euclidean_inner_productP R n)).
Variable Z:nat->lmodType R.
Variable evaluation:forall k,{ffun 'I_k->X}->Hom (Z k) Y.
Variable ZN:forall k,Z k->R.
Hypothesis hZ:forall k,is_continuous_multilinear_space NX NY (@evaluation k) (@ZN k).
Variable A:X->Prop.
Variable B:Y->Prop.
Variable f:X->Y.
Hypothesis hImage:forall x,A x->B (f x).
Variable W:lmodType R.
Variable NW:W->R.
Hypothesis hNW:is_real_norm NW.
Variable m:nat.
Variable phi:Y->A_m Y W m.

(** Source for [original_pullback_exterior_derivative]:
    the full original d(f# phi)=f#(d phi),
    Federer 4.1.6, pp. 354–355. All
    three fields are certified by the actual original
    graph laws on A and B. No class-two or
    whole-coefficient completeness assumption is added. *)
Theorem original_pullback_exterior_derivative:
  (forall x,A x->exists z:Z 2%N,
    has_norm_higher_differential NX evaluation ZN A f 2%N x z)->
  (forall y,B y->norm_differentiable_at NY (@euclidean_form_norm R h2 n W NW hNW m) B phi y)->
  exists (theta:X->A_m X W m) (dphi:Y->A_m Y W m.+1) (dtheta:X->A_m X W m.+1),
    (forall y,B y->has_exterior_derivative NY (@euclidean_form_norm R h2 n W NW hNW m) B phi y (dphi y)) /\
    (forall x,A x->
      has_differential_form_pullback NX NY A B f phi x (theta x) /\
      has_exterior_derivative NX (@euclidean_form_norm R h2 v W NW hNW m) A theta x (dtheta x) /\
      has_differential_form_pullback NX NY A B f dphi x (dtheta x)).
Proof.
move=>hTwice hPhi.
have [F hRep]:=@norm_higher_differential_representative_exists R X Y NX NY hNX hNY Z evaluation ZN hZ A f 1%N.
have hF x:A x->has_norm_higher_differential NX evaluation ZN A f 1%N x (F x).
  move=>hx; have [z hz]:=hTwice x hx.
  have [w hw]:=norm_higher_differential_previous_domain hNX hz.
  by rewrite (hRep x w hw).
pose J:=@continuous_multilinear_one_evaluation R X Y (Z 1%N) NX NY (@evaluation 1%N) (@ZN 1%N) (@hZ 1%N).
have [dphi hdphi]:=@original_exterior_derivative_field_exists R h2 n W NW hNW m B phi hPhi.
pose theta x:=A_m_dual (hom_as_linear (J (F x))) (phi (f x)).
pose dtheta x:=A_m_dual (hom_as_linear (J (F x))) (dphi (f x)).
exists theta,dphi,dtheta; split; first exact:hdphi.
move=>x hx.
have hFirst:=(@norm_higher_differential_first R X Y NX NY hNX hNY
  Z evaluation ZN hZ A f x (F x)).1 (hF x hx).
split.
- split; first exact:(@hImage x hx).
  exists (J (F x)); by split.
- split.
  + have [z hz]:=hTwice x hx.
    have [M [hM hD]]:=hdphi (f x) (@hImage x hx).
    have hMain:=@original_vector_pullback_exterior_derivative R h2 v n Z evaluation ZN hZ
      A f F hF W NW hNW B hImage x z m phi M hz hM.
    have hEqual:=exterior_differential_value_unique (@ExteriorDifferential.laws R h2 n W m M) hD.
    by rewrite /dtheta -hEqual.
  + split; first exact:(@hImage x hx).
    exists (J (F x)); by split.
Qed.
End PullbackExteriorDerivative.
