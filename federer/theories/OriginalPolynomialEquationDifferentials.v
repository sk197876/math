(** Federer (1969), 3.4.8(10), p. 331:
    actual differentials of the original finite
    equation system in every transverse direction.
    Apply the proved prefix coefficient product
    and actual polynomial differential connections. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals.
From Federer Require Import Hom RealNormUP NormDifferentialUP NormDifferentialSubtraction NormDifferentialLocal
  NormBoundedLinearTopology NormLinearDomainLaws NormAnalyticUP
  PrefixCoefficientCoordinateDifferential ActualPolynomialTransverseDifferential.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Section EquationDifferentials.
Variable R:realType.
Variables X Y:lmodType R.
Variables (NX:X->R) (NY:Y->R).
Hypotheses (hNX:is_real_norm NX) (hNY:is_real_norm NY).
Variable U:Y->Prop.
Hypothesis hU:forall y,U y ->norm_domain_interior NY U y.
Variable P:Hom X Y.
Hypothesis hP:norm_bounded_linear NX NY P.
Variable index:finType.
Variable first:index.
Variable xi:index->Hom X R^o.
Hypothesis hXi:forall i,norm_bounded_linear NX (fun t:R^o=>`|t|) (xi i).
Variable k:nat.
Variable b:index->'I_k->Y->R.
Variable delta:Y->R.
Hypothesis hB:forall j i,@norm_analytic R Y R^o NY (fun t:R^o=>`|t|) hNY
  (@scalar_absolute_value_norm R) U (b j i).
Hypothesis hDelta:@norm_analytic R Y R^o NY (fun t:R^o=>`|t|) hNY
  (@scalar_absolute_value_norm R) U delta.
Variables w wD:X->R.
Hypothesis hW:forall a,U (P a) ->exists L:Hom X R^o,
  has_norm_differential NX (fun t:R^o=>`|t|) (fun x=>U (P x)) w a L /\
  forall v,P v = 0 ->L v = wD a*xi first v.
Variable t:index->X->R.
Hypothesis hT:forall j x,t j x = \sum_(i<k) b j i (P x)*(xi first x)^+(i:nat).
Variable f:index->X->R.
Hypothesis hF:forall j x,f j x = if j==first then w x else delta (P x)*xi j x-t j x.

(** Source for [original_polynomial_equation_differentials]:
    the differential matrix on e_(m+1),...,
    e_n used in 3.4.8(10), pp. 331–332.
    Its first row is W' omega_(m+1);
    each later row is delta omega_j
    minus the numerator derivative times omega_(m+1).
    Every differential is the actual derivative
    of the original equation on its cylinder. *)
Theorem original_polynomial_equation_differentials a:
  U (P a) ->exists D:index->Hom X R^o,
    (forall j,has_norm_differential NX (fun z:R^o=>`|z|) (fun x=>U (P x)) (f j) a (D j)) /\
    forall j v,P v = 0 ->D j v = if j==first then wD a*xi first v else
      delta (P a)*xi j v-
        (\sum_(i<k) (i:nat)%:R*b j i (P a)*(xi first a)^+(i:nat).-1)*xi first v.
Proof.
move=>ha.
pose A:=fun x=>U (P x).
have hInterior:norm_domain_interior NX A a:=@norm_bounded_linear_preimage_interior R X Y NX NY hNX
  P U a hP (@hU (P a) ha).
have hExists j:exists L:Hom X R^o,
    has_norm_differential NX (fun z:R^o=>`|z|) A (f j) a L /\
    forall v,P v = 0 ->L v = if j==first then wD a*xi first v else
      delta (P a)*xi j v-(\sum_(i<k) (i:nat)%:R*b j i (P a)*(xi first a)^+(i:nat).-1)*xi first v.
  case hCase:(j==first).
  - have hEqual:j = first:=eqP hCase;subst j.
    have [L [hL hDirections]]:=@hW a ha.
    exists L;split.
    + apply:(norm_differential_domain_agreement hNX _ hL)=>x _;by rewrite hF eqxx.
    + move=>v hZero;exact:hDirections v hZero.
  - have [LD [hLD hLDValues]]:=@prefix_coefficient_coordinate_differential R X Y NX NY hNX hNY
      A U P (xi j) delta a hInterior hP (hXi j) (fun x hx=>hx) ha hDelta.
    have [LT [hLT hLTValues]]:=@actual_polynomial_transverse_differential R X Y NX NY hNX hNY
      U P (xi first) k (b j) (t j) hU hP (hXi first) (hB j) (hT j) a ha.
    exists (LD-LT);split.
    + have hDifference:=norm_differential_subtract hNX (@scalar_absolute_value_norm R) hLD hLT.
      apply:(norm_differential_domain_agreement hNX _ hDifference)=>x _;by rewrite hF hCase.
    + move=>v hZero.
      change (LD v-LT v = delta (P a)*xi j v-
        (\sum_(i<k) (i:nat)%:R*b j i (P a)*(xi first a)^+(i:nat).-1)*xi first v).
      by rewrite hLDValues // hLTValues.
have [D hD]:=choice hExists.
exists D;split;first by move=>j;exact:(hD j).1.
by move=>j;exact:(hD j).2.
Qed.
End EquationDifferentials.
