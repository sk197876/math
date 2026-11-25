(** Federer (1969), 4.1.2, pp. 346–347:
    actual higher derivatives of the rescaled kernel.
    The earlier affine-dilation and scalar-multiple laws
    give the exact factor epsilon^(-n-i). *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals.
From Federer Require Import Hom RealNormUP GrassmannAbbreviations EuclideanInnerProduct InnerNorm HilbertFormCompactness
  ContinuousMultilinearUP NormHigherDifferentialUP NormAffineDilationDifferentials NormHigherDifferentialArithmetic
  SmoothingDilationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory.
Local Open Scope ring_scope.
Section SmoothingDilationDerivatives.
Variable R:realType.
Variable n:nat.
Local Notation X := (R_n R n).
Local Notation N := (inner_norm (@euclidean_inner_productP R n)).
Local Notation hN := (inner_norm_real_norm (@euclidean_inner_productP R n)).
Local Notation hR := (@scalar_absolute_value_norm R).
Variable phi:X->R.
Variable family:R->X->R.
Hypothesis hFamily:is_smoothing_dilation phi family.
Variable Z:nat->lmodType R.
Variable ev:forall j,{ffun 'I_j->X}->Hom (Z j) R^o.
Variable ZN:forall j,Z j->R.
Hypothesis hZ:forall j,is_continuous_multilinear_space N (fun t:R^o=>`|t|) (@ev j) (@ZN j).

(** Source for [smoothing_dilation_derivative_coefficient]: the
    exact scalar factor epsilon^(-n-i) in
    Federer 4.1.2, pp. 346–347. *)
Lemma smoothing_dilation_derivative_coefficient (e:R) k:
  (e^+n)^-1*(e^-1)^+k=(e^+(n+k))^-1.
Proof. by rewrite exprD invfM exprVn. Qed.

(** Source for [smoothing_dilation_higher_differential]: the
    actual kth derivative of Phi_epsilon equals
    epsilon^(-n-k) times the kth derivative
    of Phi at epsilon^(-1)x,
    Federer 4.1.2, pp. 346–347. *)
Theorem smoothing_dilation_higher_differential k (D:X->Z k):
  (forall x,has_norm_higher_differential N ev ZN (fun _=>True) phi k x (D x)) ->
  forall e:R,0<e ->forall x,
    has_norm_higher_differential N ev ZN (fun _=>True) (family e) k x
      ((e^+(n+k))^-1*:D (e^-1*:x)).
Proof.
move=>hD e he x.
have hCompose:=@norm_higher_differential_affine_dilation R X R^o N (fun t:R^o=>`|t|) hN hR
  Z ev ZN hZ phi e^-1 0 k D hD.
have hScaled:=@norm_higher_differential_field_scale R X R^o N (fun t:R^o=>`|t|) hN hR
  Z ev ZN hZ (fun _=>True) k (fun x=>phi (e^-1*:x+0))
  (fun x=>(e^-1)^+k*:D (e^-1*:x+0)) (e^+n)^-1
  (fun x (_:True)=>hCompose x) x Logic.I.
have hEq:(fun x:X=>(e^+n)^-1*phi (e^-1*:x+0))=family e.
  apply:funext=>y; rewrite addr0 (@hFamily e he y); reflexivity.
have hValue:(e^+n)^-1*:((e^-1)^+k*:D (e^-1*:x+0))=
    (e^+(n+k))^-1*:D (e^-1*:x).
  by rewrite addr0 scalerA smoothing_dilation_derivative_coefficient.
rewrite hEq hValue in hScaled; exact hScaled.
Qed.
End SmoothingDilationDerivatives.
