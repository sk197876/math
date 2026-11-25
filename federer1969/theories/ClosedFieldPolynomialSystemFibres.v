(** Federer (1969), 3.4.12, p. 339: every nonexceptional
    complex projection fibre has exactly the original polynomial
    degree. Apply the checked simple-root count, original coordinate
    root realisation, transverse separation and finite enumeration. *)
From mathcomp Require Import all_boot all_order all_algebra boolp classical_sets.
From Federer Require Import Hom LinearBasis FiniteCoordinates FieldPrefixCoordinatesUP
  OrdinalCoordinateTail FieldPolynomialRootRealisation FieldPolynomialFibreSeparation
  ClosedFieldFiniteSimpleRoots FiniteRootFibreEnumeration FiniteFibreEnumerationUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope classical_set_scope.
Section Fibres.
Variable K:fieldType.
Variable hClosed:GRing.closed_field_axiom [the pzRingType of (K:Type)].
Variable X:lmodType K.
Variables n m:nat.
Variable hMN:(m<=n)%N.
Variable e:'I_n->X.
Hypothesis he:is_basis e.
Variable omega:'I_n->Hom X K^o.
Hypothesis hDual:forall i j,omega i (e j)=if i==j then 1 else 0.
Local Notation Y:=(coordinate_space K m).
Variable P:Hom X Y.
Hypothesis hP:is_field_prefix_projection omega hMN P.
Local Notation index:=[the finType of 'I_(n-m)].
Local Notation xi:=(fun j:index=>omega (ordinal_coordinate_tail_index hMN j)).
Variable first:index.
Variable k:nat.
Variable U:set Y.
Variable delta:Y->K.
Variable bW:'I_k.+1->Y->K.
Variable b:index->'I_k->Y->K.
Variable Z:set X.
Hypothesis hLeading:forall y,bW ord_max y = 1.
Local Notation lower:=(fun (i:'I_k) y=>bW (widen_ord (leqnSn k) i) y).
Hypothesis hZ:forall x,Z x <->U (P x) /\
  ((xi first x)^+k+\sum_(i<k) lower i (P x)*(xi first x)^+(i:nat)=0) /\
  (forall j,j!=first ->delta (P x)*xi j x=\sum_(i<k) b j i (P x)*(xi first x)^+(i:nat)) /\
  delta (P x)!=0.
Hypothesis hSimple:forall x,Z x ->
  (\sum_(i<k.+1) (i:nat)%:R*bW i (P x)*(xi first x)^+(i:nat).-1)<>0.
(** Source for [closed_field_polynomial_system_fibres]: every
    original fibre over U minus delta zero has exactly k
    points. Thus the other cardinality strata Y_nu are empty,
    as stated in 3.4.12, p. 339. Every root is realised
    by an actual original source vector; no ordering is used. *)
Theorem closed_field_polynomial_system_fibres y:
  U y ->delta y!=0 ->exists a:'I_k->X,is_finite_fibre_enumeration P Z y a.
Proof.
move=>hy hDelta.
have hMonic z:(\sum_(i<k.+1) bW i y*z^+(i:nat))=
    z^+k+\sum_(i<k) lower i y*z^+(i:nat).
  by rewrite big_ord_recr hLeading mul1r addrC.
have hRealise:=@field_polynomial_root_realisation K X n m hMN e omega hDual P hP first k
  U delta lower b Z hZ y hy hDelta.
have hSimpleRoot z:(\sum_(i<k.+1) bW i y*z^+(i:nat))=0 ->
    (\sum_(i<k.+1) (i:nat)%:R*bW i y*z^+(i:nat).-1)<>0.
  rewrite hMonic=>hRoot.
  have [x [hx [hPrefix hFirst]]]:=(hRealise z).1 hRoot.
  have h:=@hSimple x hx;by rewrite hPrefix hFirst in h.
have [roots [hUnique [hCount hRoots]]]:=@closed_field_finite_simple_roots K hClosed k
  (fun i=>bW i y) (hLeading y) hSimpleRoot.
apply:(@finite_root_fibre_enumeration K [the choiceType of (X:Type)] Y P Z y
  (xi first) k roots hUnique hCount).
- move=>x hx hPrefix;apply:(hRoots (xi first x)).1;rewrite hMonic.
  have h:=((hZ x).1 hx).2.1;by rewrite hPrefix in h.
- move=>z hz;apply:(hRealise z).1.
  rewrite -hMonic;exact:(hRoots z).2 hz.
- move=>x z hx hz hPx hPz hFirst.
  pose numerator:=fun j:index=>\sum_(i<k) b j i y*(xi first x)^+(i:nat).
  have hX j (hj:j!=first):delta y*xi j x=numerator j.
    have h:=((hZ x).1 hx).2.2.1 j hj;by rewrite hPx in h.
  have hZZ j (hj:j!=first):delta y*xi j z=numerator j.
    have h:=((hZ z).1 hz).2.2.1 j hj;by rewrite hPz -hFirst in h.
  apply:(@field_polynomial_fibre_separation K X n m e he omega hDual hMN P hP first
    x z (delta y) numerator hDelta _ hFirst hX hZZ).
  by rewrite hPx hPz.
Qed.
End Fibres.
