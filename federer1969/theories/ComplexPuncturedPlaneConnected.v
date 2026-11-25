(** Federer (1969), 3.4.12, p. 339: connected complex
    coverings need not admit globally ordered sheets. The actual
    punctured complex plane is connected: four original open
    coordinate half-planes form a connected union. Reuse the
    project's convex-connectedness theorem. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets reals topology.
From Federer Require Import Hom RealNormUP NormMetric ScalarRestriction ComplexScalarUP ComplexScalarSealed
  ComplexScalarLaws ComplexCoefficientAlgebra ComplexModulus ComplexScalarNorm NormPositiveFunctionalConnected.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Theory ComplexScalarTheory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Plane.
Variable R:realType.
Local Notation C:=(ComplexScalars.C R).
Local Notation CR:=(restricted_space (ComplexScalars.embed R) C^o).
Local Notation M:=(real_norm_metric_space (@complex_modulus_real_norm R)).
Local Notation re:=(@ComplexScalars.re R).
Local Notation im:=(@ComplexScalars.im R).
Local Notation ii:=(ComplexScalars.ii R).
Local Notation hC:=(ComplexScalars.laws R).

(** Source for [complex_punctured_plane_connected]: the actual
    connected base and parameter space for the double-cover
    qualification in 3.4.12, p. 339. *)
Theorem complex_punctured_plane_connected:@connected M [set z:C|z<>0].
Proof.
pose realPart:Hom CR R^o:=hom_of_linear (GRing.Linear.clone R CR R^o *:%R (@complex_real_part R) _).
pose imaginaryPart:Hom CR R^o:=hom_of_linear (GRing.Linear.clone R CR R^o *:%R (@complex_imaginary_part R) _).
pose A:set M:=[set z|0<re z].
pose B:set M:=[set z|0<im z].
pose D:set M:=[set z|0< -re z].
pose F:set M:=[set z|0< -im z].
have hA:connected A:=@norm_positive_functional_connected R CR (@complex_modulus R)
  (@complex_modulus_real_norm R) realPart.
have hB:connected B:=@norm_positive_functional_connected R CR (@complex_modulus R)
  (@complex_modulus_real_norm R) imaginaryPart.
have hD:connected D.
  have h:=@norm_positive_functional_connected R CR (@complex_modulus R)
    (@complex_modulus_real_norm R) (-1*:realPart).
  have hValues:(fun z:CR=>(-1*:realPart) z)=(fun z:CR=>-re z).
    apply:funext=>z;rewrite hom_scaleE /realPart hom_of_linearE.
    change ((-1:R)*re z= -re z);by rewrite mulN1r.
  have hSet:[set z:M|0<(-1*:realPart) z]=D.
    apply:funext=>z;have hValue:=congr1 (fun f:CR->R^o=>f z) hValues.
    change (is_true (0<(-1*:realPart) z)=is_true (0< -re z)).
    exact:(congr1 (fun r:R=>is_true (0<r)) hValue).
  change (@connected M [set z:M|0<(-1*:realPart) z]) in h.
  rewrite hSet in h;exact:h.
have hF:connected F.
  have h:=@norm_positive_functional_connected R CR (@complex_modulus R)
    (@complex_modulus_real_norm R) (-1*:imaginaryPart).
  have hValues:(fun z:CR=>(-1*:imaginaryPart) z)=(fun z:CR=>-im z).
    apply:funext=>z;rewrite hom_scaleE /imaginaryPart hom_of_linearE.
    change ((-1:R)*im z= -im z);by rewrite mulN1r.
  have hSet:[set z:M|0<(-1*:imaginaryPart) z]=F.
    apply:funext=>z;have hValue:=congr1 (fun f:CR->R^o=>f z) hValues.
    change (is_true (0<(-1*:imaginaryPart) z)=is_true (0< -im z)).
    exact:(congr1 (fun r:R=>is_true (0<r)) hValue).
  change (@connected M [set z:M|0<(-1*:imaginaryPart) z]) in h.
  rewrite hSet in h;exact:h.
have hAB:connected (A `|` B).
  apply:connectedU;[|exact:hA|exact:hB].
  exists (1+ii:C);split.
  - change (is_true (0<re (1+ii:C))).
    rewrite (complex_re_add hC) (complex_re_one hC) (complex_re_i hC) addr0;exact:ltr01.
  - change (is_true (0<im (1+ii:C))).
    rewrite (complex_im_add hC) (complex_im_one hC) (complex_im_i hC) add0r;exact:ltr01.
have hABD:connected ((A `|` B) `|` D).
  apply:connectedU;[|exact:hAB|exact:hD].
  exists (-1+ii:C);split.
  - right;change (is_true (0<im (-1+ii:C))).
    rewrite (complex_im_add hC) im_neg (complex_im_one hC) (complex_im_i hC) oppr0 add0r;exact:ltr01.
  - change (is_true (0< -re (-1+ii:C))).
    rewrite (complex_re_add hC) re_neg (complex_re_one hC) (complex_re_i hC) addr0 opprK;exact:ltr01.
have hWhole:connected (((A `|` B) `|` D) `|` F).
  apply:connectedU;[|exact:hABD|exact:hF].
  exists (1-ii:C);split.
  - left;left;change (is_true (0<re (1-ii:C))).
    rewrite (complex_re_add hC) re_neg (complex_re_one hC) (complex_re_i hC) oppr0 addr0;exact:ltr01.
  - change (is_true (0< -im (1-ii:C))).
    rewrite (complex_im_add hC) im_neg (complex_im_one hC) (complex_im_i hC) add0r opprK;exact:ltr01.
have hSame:(((A `|` B) `|` D) `|` F)=[set z:C|z<>0].
  apply/seteqP;split=>z.
  - move=>[[[hz|hz]|hz]|hz] hZero.
    + change (is_true (0<re z)) in hz;by rewrite hZero re_zero ltxx in hz.
    + change (is_true (0<im z)) in hz;by rewrite hZero im_zero ltxx in hz.
    + change (is_true (0< -re z)) in hz;by rewrite hZero re_zero oppr0 ltxx in hz.
    + change (is_true (0< -im z)) in hz;by rewrite hZero im_zero oppr0 ltxx in hz.
  - move=>hNonzero;case:(ltgtP (re z) 0)=>[hR|hR|hR].
    + left;right;change (is_true (0< -re z));rewrite oppr_gt0;exact:hR.
    + left;left;left;exact:hR.
    + case:(ltgtP (im z) 0)=>[hI|hI|hI].
      * right;change (is_true (0< -im z));rewrite oppr_gt0;exact:hI.
      * left;left;right;exact:hI.
      * exfalso;apply:hNonzero;apply:coordinates_injective;[by rewrite hR re_zero|by rewrite hI im_zero].
by rewrite -hSame.
Qed.
End Plane.
