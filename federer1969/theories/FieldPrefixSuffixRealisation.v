(** Federer (1969), 3.4.12, p. 339: retain the actual
    original prefix and transverse coordinates of a complex polynomial
    fibre. Apply the biorthogonal finite-sum theorem of 1.4.3,
    p. 19, and the existing finite concatenation laws. *)
From mathcomp Require Import all_boot all_order all_algebra boolp.
From Federer Require Import Hom Bilinear Biorthogonal FiniteCoordinates
  FieldPrefixCoordinatesUP ConcatenatedFamilies OrdinalCoordinateTail.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.
(** Source for [field_prefix_suffix_realisation]: every prescribed
    prefix and suffix is realised by one vector in the original
    coordinates, supporting the complex polynomial fibres of 3.4.12,
    p. 339. The finite sum is only an existence witness. *)
Theorem field_prefix_suffix_realisation (K:fieldType) (X:lmodType K) n m
    (e:'I_n->X) (omega:'I_n->Hom X K^o) (hMN:(m<=n)%N)
    (P:Hom X (coordinate_space K m)):
  (forall i j,omega i (e j)=if i==j then 1 else 0) ->
  is_field_prefix_projection omega hMN P ->
  forall (y:coordinate_space K m) (t:'I_(n-m)->K),
    exists x:X,P x=y /\forall j,omega (ordinal_coordinate_tail_index hMN j) x=t j.
Proof.
move=>hDual hP y t.
pose c:=fun i:'I_n=>concatenate_family y t (cast_ord (esym (subnKC hMN)) i).
pose x:=\sum_i c i*:e i.
have hValues i:omega i x=c i:=@biorthogonal_sum K X [the finType of 'I_n] omega e hDual c i.
exists x;split.
- apply/ffunP=>i;rewrite hP hValues /c.
  have hIndex:cast_ord (esym (subnKC hMN)) (widen_ord hMN i)=lshift (n-m) i.
    by apply:val_inj.
  by rewrite hIndex concatenate_family_l.
- move=>j;rewrite hValues /c.
  have hIndex:cast_ord (esym (subnKC hMN)) (ordinal_coordinate_tail_index hMN j)=rshift m j.
    by apply:val_inj.
  by rewrite hIndex concatenate_family_r.
Qed.
