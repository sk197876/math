(** Federer (1969), 3.2.33, p. 270: analytic
    coordinates and local representatives of f on W. *)
From mathcomp Require Import all_boot all_order all_algebra reals classical_sets.
From Federer Require Import RealNormUP NormAnalyticUP NormAnalyticDomain NormAnalyticComposition
  NormAnalyticOperations NormAnalyticRelativeUP.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Local Open Scope classical_set_scope.

(** Source for [relative_analytic_in_parametrisation]: analytic
    f on W has analytic coordinate representatives,
    supporting the use of 3.1.24 in Federer 3.2.33,
    p. 270. Compose a local analytic representative with
    the actual analytic parametrization and use local agreement.
    This needs no global choice of a representative or chart. *)
Theorem relative_analytic_in_parametrisation (R:realType) (X Z Y:lmodType R)
    (NX:X->R) (NZ:Z->R) (NY:Y->R)
    (hNX:is_real_norm NX) (hNZ:is_real_norm NZ) (hNY:is_real_norm NY)
    (A W:set X) (V:set Z) (psi:Z->X) (f:X->Y):
  (forall u,V u ->W (psi u)) ->
  @norm_analytic R Z X NZ NX hNZ hNX V psi ->
  @norm_analytic_relative R X Y NX NY hNX hNY A W f ->
  @norm_analytic R Z Y NZ NY hNZ hNY V (fun u=>f (psi u)).
Proof.
move=>hRange hPsi hf a ha.
have [U [g [hUa [hg hAgree]]]]:=hf (psi a) (hRange a ha).
pose O:set Z:=[set u|V u /\U (psi u)].
have hOa:O a by split.
have hOV:O `<=` V by move=>u hu; exact hu.1.
have hComposite:=@norm_analytic_composition R Z X Y NZ NX NY hNZ hNX hNY V U psi g hPsi hg.
have hSame u (hu:O u):g (psi u)=f (psi u).
  exact:(esym (hAgree (psi u) (hRange u hu.1) hu.2).2).
apply:(@norm_analytic_at_domain_enlargement R Z Y NZ NY hNZ hNY O V (fun u=>f (psi u)) a hOV).
exact:(@norm_analytic_at_domain_agreement R Z Y NZ NY hNZ hNY O
  (fun u=>g (psi u)) (fun u=>f (psi u)) a hSame (hComposite a hOa)).
Qed.

(** Source for [analytic_coordinate_local_extension]: the
    converse coordinate interpretation for analytic f on W
    in Federer 3.2.33, p. 270. Compose the analytic
    coordinate function with the ambient analytic forward chart.
    Its exact inverse law proves agreement on W intersect T.
    This shows the local-extension predicate does not assume
    an analytic ambient extension as an additional premise. *)
Theorem analytic_coordinate_local_extension (R:realType) (X Z Y:lmodType R)
    (NX:X->R) (NZ:Z->R) (NY:Y->R)
    (hNX:is_real_norm NX) (hNZ:is_real_norm NZ) (hNY:is_real_norm NY)
    (A W T:set X) (V:set Z) (phi:X->Z) (psi:Z->X) (f:X->Y):
  W `<=` A ->(forall x,T x ->V (phi x)) ->
  (forall x,W x ->T x ->psi (phi x)=x) ->
  @norm_analytic R X Z NX NZ hNX hNZ T phi ->
  @norm_analytic R Z Y NZ NY hNZ hNY V (fun u=>f (psi u)) ->
  exists g:X->Y,@norm_analytic R X Y NX NY hNX hNY T g /\
    forall x,W x ->T x ->A x /\f x=g x.
Proof.
move=>hWA hPhiRange hInverse hPhi hCoordinate.
exists (fun x=>f (psi (phi x))); split.
- exact:(norm_analytic_compose_on hPhiRange hPhi hCoordinate).
- move=>x hx ht; split; first exact:(hWA x hx).
  by rewrite (hInverse x hx ht).
Qed.
