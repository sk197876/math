(** Federer (1969), 3.4.10, p. 338:
    three actual curve tangents rule out a regular
    two-dimensional surface at a positive axis point.
    Reuse the existing coordinate basis and finite independent
    family dimension bound. *)
From mathcomp Require Import all_boot all_order all_algebra boolp reals ring.
From Federer Require Import ModuleQuotient SubspaceCarrier SubspaceFamilies GrassmannSubspaces
  GrassmannAbbreviations FiniteCoordinates FiniteDimension FiniteBasisComparison
  FiniteIndependence LinearBasis.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory.
Local Open Scope ring_scope.

(** Source for [bruhat_whitney_tangent_plane_obstruction]: the
    two signed curve directions and the axis direction
    cannot lie in a plane, supporting the original
    example cited by 3.4.10, p. 338. *)
Theorem bruhat_whitney_tangent_plane_obstruction (R:realType) (b s:R)
    (W:G (R_n R 3) 2):
  s!=0 ->
  grassmann_val W [ffun i=>if i==ord0 then s else
    if i==Ordinal (isT:(1<3)%N) then 1 else b] ->
  grassmann_val W [ffun i=>if i==ord0 then -s else
    if i==Ordinal (isT:(1<3)%N) then 1 else b] ->
  grassmann_val W (@coordinate_basis R 3 ord_max) ->False.
Proof.
move=>hs hPlus hMinus hAxis.
pose X:=R_n R 3.
pose j:=Ordinal (isT:(1<3)%N).
pose p:X:=[ffun i=>if i==ord0 then s else if i==j then 1 else b].
pose q:X:=[ffun i=>if i==ord0 then -s else if i==j then 1 else b].
have hFirst:grassmann_val W (@coordinate_basis R 3 ord0).
  have hLinear:=subspace_scale (2*s)^-1
    (subspace_add hPlus (subspace_opp hMinus)).
  have hEqual:(2*s)^-1*:(p-q)=@coordinate_basis R 3 ord0.
    apply/ffunP=>i;rewrite !ffunE /p /q /coordinate_basis ?ffunE.
    case h0:(i==ord0).
    - change ((2*s)^-1*(s- -s)= 1).
      field;rewrite ?mulf_eq0 ?pnatr_eq0 ?hs //.
    - by rewrite subrr scaler0.
  by rewrite hEqual in hLinear.
have hSecond:grassmann_val W (@coordinate_basis R 3 j).
  have hLinear:=subspace_add (subspace_add hPlus
    (subspace_opp (subspace_scale s hFirst)))
    (subspace_opp (subspace_scale b hAxis)).
  have hEqual:p-s*:@coordinate_basis R 3 ord0-b*:@coordinate_basis R 3 ord_max=
      @coordinate_basis R 3 j.
    apply/ffunP=>i;rewrite !ffunE /p /coordinate_basis ?ffunE.
    change ((if i==ord0 then s else if i==j then 1 else b)-
      s*(if i==ord0 then 1 else 0)-b*(if i==ord_max then 1 else 0)=
      (if i==j then 1 else 0)).
    case h0:(i==ord0).
    - move/eqP:h0=>->;rewrite /=;ring.
    case h1:(i==j).
    - move/eqP:h1=>->;rewrite /=;ring.
    have hi:i=ord_max.
      apply:val_inj;case:i h0 h1=>[i hi] /= h0 h1.
      by case:i hi h0 h1=>[|[|[|i]]].
    rewrite hi /=;ring.
  by rewrite hEqual in hLinear.
have hBasis i:grassmann_val W (@coordinate_basis R 3 i).
  case h0:(i==ord0);first by move/eqP:h0=>->.
  case h1:(i==j);first by move/eqP:h1=>->.
  have hi:i=ord_max.
    apply:val_inj;case:i h0 h1=>[i hi] /= h0 h1.
    by case:i hi h0 h1=>[|[|[|i]]].
  by rewrite hi.
have hIndependent:=@subspace_family_independent R X (grassmann_val W)
  [the finType of 'I_3] (@coordinate_basis R 3) hBasis
  (finite_basis_independent (@coordinate_basisP R 3)).
have [e he]:=grassmann_proof W.
have hBound:=@finite_independent_dimension R (finite_basis_vect he) 3
  (subspace_family hBasis) hIndependent.
by rewrite finite_basis_dimension card_ord in hBound.
Qed.
